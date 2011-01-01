
{-# LANGUAGE FlexibleContexts, UndecidableInstances #-}
module CParser.LevelInference(levelInferModule) where

import qualified Data.Map as Map
import Data.Foldable as Fold

import Gluon.Common.SourcePos
import Gluon.Common.Label
import Gluon.Common.Identifier
import Gluon.Core.Level
import Gluon.Core(Var, mkVar)
import CParser.AST

-------------------------------------------------------------------------------
-- * Level inference

showResolvedVar (ResolvedVar var maybeLabel _) =
          case maybeLabel of
            Just label -> ((showLabel label)++"("++(show var)++")")
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
  of Just (PredefinedVar v) -> LIVar v
     Just (PredefinedCon c) -> LICon c
     Just (PredefinedKind k) -> LIKind k
     Nothing -> LIVar (mkVar ident label lvl)

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

-- Check the Type's level, then infer
liDecl :: LMap -> (Decl Resolved) -> IO (Decl LevelInferred)
liDecl lmap (BoxedDecl declVar declType) = do
   liType <- liLType lmap declType
   let depType = getLevel liType
   (liVar,_) <- predLvl depType declVar lmap 
   return $ BoxedDecl liVar liType
                     
liDecl lmap (DataDecl declAddr declPtr declType) = do
   (liAddr,umap) <- mkLIVar lmap declAddr ObjectLevel
   liType <- liLType umap declType
   let depType = getLevel liType
   (liPtr,_) <- predLvl depType declPtr umap 
   return $ DataDecl liAddr liPtr liType

-- Entry Point for Type
liLType :: LMap -> RLType -> IO (LType LevelInferred)
liLType lmap (L pos rType) = case rType
  of VarT rVar -> do 
  -- Given a variable, find the information, typically from the Map
        let lvl = lvlFromVarPos lmap rVar pos
            livar = castLIVar rVar lvl
        return $ L pos (VarT livar)
     LitT tLit -> return $ L pos (LitT tLit)
     AppT tOper tArgs -> do
     -- Recurse
        liOp <- liLType lmap tOper
        liArgs <- mapM (\x -> liLType lmap x) tArgs
        return $ L pos (AppT liOp liArgs)
     FunT fParam (Just fEff) fRng -> do
     -- Recurse, but use updated Map from Param
        (lParam,umap) <- liParamType lmap fParam
        lEff <- liLType umap fEff
        lRng <- liReturnType umap fRng
        return $ L pos (FunT lParam (Just lEff) lRng)
     FunT fParam Nothing fRng -> do
        (lParam,umap) <- liParamType lmap fParam
        lRng <- liReturnType umap fRng
        return $ L pos (FunT lParam Nothing lRng)
        
        
-- Find Type's level, and if needed, assign predecessor and insert to update Map
liParamType :: LMap -> (ParamType Resolved) -> IO (ParamType LevelInferred, LMap)
liParamType lmap param = case param
  of ValuePT (Just ptVar) ptType -> do 
        liType <- liLType lmap ptType
        let depType = getLevel liType
        (liVar,umap) <- predLvl depType ptVar lmap 
        return $ (ValuePT (Just liVar) liType,umap)

     ValuePT Nothing ptType -> do liType <- liLType lmap ptType
                                  return $ (ValuePT Nothing liType,lmap)
                                
     BoxedPT ptType -> do liType <- liLType lmap ptType
                          return $ (BoxedPT liType,lmap)
     ReferencedPT ptAddr ptType -> do (liAddr,umap) <- mkLIVar lmap ptAddr ObjectLevel
                                      liType <- liLType umap ptType
                                      return $ (ReferencedPT liAddr liType,umap)

liReturnType :: LMap -> (ReturnType Resolved) -> IO (ReturnType LevelInferred)
liReturnType lmap (ReturnType rtRepr rtType) = do
  lt <- liLType lmap rtType
  return $ ReturnType rtRepr lt
     
     
-- These define the getLevel method for other LevelInferred Classes, anything wanting to know the Level info from the AST could use these     
instance HasLevel a => HasLevel (Located a) where getLevel loc = getLevel (unLoc loc) 
     
instance HasLevel (Identifier ix) => HasLevel (Type ix) where
  getLevel t = case t
    of VarT liVar -> getLevel liVar
       LitT _ -> ObjectLevel
       AppT liOper _ -> getLevel liOper
       FunT _ _ liRng -> getLevel liRng
       
   
 
instance HasLevel (Identifier ix) => HasLevel (ReturnType ix) where
  getLevel (ReturnType _ rType) = getLevel rType  

instance HasLevel LIVar where
  getLevel (LIVar v) = getLevel v
  getLevel (LICon c) = getLevel c
  getLevel (LIKind _) = KindLevel

-------------------------------------------------------------------------------
-- * Main function

levelInferModule :: RModule -> IO (Module LevelInferred)
levelInferModule mod = liModule mod 
