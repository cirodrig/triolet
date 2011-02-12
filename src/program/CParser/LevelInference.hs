
{-# LANGUAGE FlexibleContexts, UndecidableInstances #-}
module CParser.LevelInference(levelInferModule) where

import qualified Data.Map as Map
import Data.Foldable as Fold

import Common.SourcePos
import Common.Identifier
import Common.Label
import Type.Var
import Type.Level
import CParser.AST

type LIVar = Var

-------------------------------------------------------------------------------
-- * Level inference

showResolvedVar (ResolvedVar var maybeLabel _) =
          case maybeLabel of
            Just label -> ((mangleLabel label)++"("++(show var)++")")
            Nothing -> show var

type LMap = Map.Map (Identifier Resolved) Level

predLvl :: Level -> ResolvedVar -> LMap -> IO (LIVar, LMap)
predLvl lvl rVar lmap = case lvl 
  of ObjectLevel -> error ((showResolvedVar rVar)++" cannot have a type lower than Value")
     TypeLevel -> mkLIVar lmap rVar ObjectLevel
     KindLevel -> mkLIVar lmap rVar TypeLevel

-- Extract Level info from a ResolvedVar.  Provide Position Information if possible
lvlFromVarPos :: LMap -> ResolvedVar -> SourcePos -> Level
lvlFromVarPos lmap resVar@(ResolvedVar _ _ det) pos =
  case det
  of Just details -> getLevel details
     Nothing ->
       case Map.lookup resVar lmap
       of Just lvl -> lvl
          Nothing -> error $ "Could not infer level of " ++ showResolvedVar resVar ++ "(" ++ show pos ++")"

-- Wrapper to construct an LIVar
castLIVar :: ResolvedVar -> Level -> Identifier LevelInferred
castLIVar (ResolvedVar ident label det) lvl =
  case det
  of Just (PredefinedVar v) -> v
     Nothing -> mkVar ident label lvl

-- Lazily add the Mapping, return updated Map and constructed LIVar
mkLIVar :: LMap -> ResolvedVar -> Level -> IO (Identifier LevelInferred,LMap)
mkLIVar lmap rvar lvl = 
    let s = Map.insert rvar lvl lmap
        v = castLIVar rvar lvl 
    in return (v, s)
  
-- Go through the module, assign levels, and compute levels using constraints

liModule :: RModule -> IO (Module LevelInferred)
liModule (Module rlist) = do
   lilist <- mapM (\x -> traverse (liDecl Map.empty) x) rlist
   return $ Module lilist

liDataConDecl lmap (DataConDecl v ty params ex_types args rng) = do
  liType <- liReturnType lmap ty
  (liVar, _) <- predLvl (getLevel liType) v lmap
  (liParams, lmap') <- liParamTypes lmap params
  (liExTypes, lmap'') <- liParamTypes lmap' ex_types
  liArgs <- mapM (liReturnType lmap'') args
  liRng <- liReturnType lmap'' rng
  return $ DataConDecl liVar liType liParams liExTypes liArgs liRng

-- Check the Type's level, then infer
liDecl :: LMap -> (Decl Resolved) -> IO (Decl LevelInferred)
liDecl lmap (VarDecl declVar declType) = do
   liType <- liReturnType lmap declType
   (liVar,_) <- predLvl (getLevel liType) declVar lmap
   return $ VarDecl liVar liType

liDecl lmap (DataDecl declVar repr declType cons) = do
   liType <- liReturnType lmap declType
   (liVar,lmap') <- predLvl (getLevel liType) declVar lmap
   liCons <- mapM (traverse (liDataConDecl lmap)) cons
   return $ DataDecl liVar repr liType liCons

-- Entry Point for Type
liLType :: LMap -> RLType -> IO (LType LevelInferred)
liLType lmap (L pos rType) = case rType
  of VarT rVar -> do 
  -- Given a variable, find the information, typically from the Map
        let lvl = lvlFromVarPos lmap rVar pos
            livar = castLIVar rVar lvl
        return $ L pos (VarT livar)
     AppT tOper tArgs -> do
     -- Recurse
        liOp <- liLType lmap tOper
        liArgs <- mapM (\x -> liLType lmap x) tArgs
        return $ L pos (AppT liOp liArgs)
     FunT fParam fRng -> do
     -- Recurse, but use updated Map from Param
        (lParam,umap) <- liParamType lmap fParam
        lRng <- liReturnType umap fRng
        return $ L pos (FunT lParam lRng)

-- Perform level inference on a sequence of parameter types
liParamTypes :: LMap
             -> [ParamType Resolved]
             -> IO ([ParamType LevelInferred], LMap)
liParamTypes lmap (pt:pts) = do
  (pt', lmap') <- liParamType lmap pt
  (pts', lmap'') <- liParamTypes lmap' pts
  return (pt' : pts', lmap'')

liParamTypes lmap [] = return ([], lmap)

-- Find Type's level, and if needed, assign predecessor and insert to update Map
liParamType :: LMap -> (ParamType Resolved)
            -> IO (ParamType LevelInferred, LMap)
liParamType lmap (ParamType repr ty) = do
  liType <- liLType lmap ty
  (repr, umap) <- li_param_repr (getLevel liType) repr
  return (ParamType repr liType, umap)
  where
    li_param_repr param_level repr = 
      case repr
      of ValuePT (Just ptVar) -> do
           (liVar, umap) <- predLvl param_level ptVar lmap 
           return $ (ValuePT (Just liVar), umap)
         ValuePT Nothing -> return (ValuePT Nothing, lmap)
         BoxedPT -> return (BoxedPT, lmap)
         ReadPT -> return (ReadPT, lmap)
         WritePT -> return (WritePT, lmap)
         OutPT -> return (OutPT, lmap)
         SideEffectPT -> return (SideEffectPT, lmap)

liReturnType :: LMap -> (ReturnType Resolved) -> IO (ReturnType LevelInferred)
liReturnType lmap (ReturnType rtRepr rtType) = do
  lt <- liLType lmap rtType
  return $ ReturnType rtRepr lt
     
     
-- These define the getLevel method for other LevelInferred Classes, anything wanting to know the Level info from the AST could use these     
instance HasLevel a => HasLevel (Located a) where getLevel loc = getLevel (unLoc loc) 
     
instance HasLevel (Identifier ix) => HasLevel (Type ix) where
  getLevel t = case t
    of VarT liVar -> getLevel liVar
       AppT liOper _ -> getLevel liOper
       FunT _ liRng -> getLevel liRng
 
instance HasLevel (Identifier ix) => HasLevel (ReturnType ix) where
  getLevel (ReturnType _ rType) = getLevel rType  

-------------------------------------------------------------------------------
-- * Main function

levelInferModule :: RModule -> IO (Module LevelInferred)
levelInferModule mod = liModule mod 
