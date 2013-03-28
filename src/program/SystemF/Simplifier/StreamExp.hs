
{-# LANGUAGE FlexibleInstances, ViewPatterns #-}
module SystemF.Simplifier.StreamExp
       (isStreamAppExp,
        interpretStreamAppExp,
        embedStreamExp,
        simplifyStreamExp,
        sequentializeStreamExp,
        pprExpS)
where

import Control.Monad
import Control.Monad.Trans.Maybe
import qualified Data.IntMap as IntMap
import qualified Data.Set as Set
import Data.Maybe
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import Common.Error
import Common.Identifier
import Common.PrecDoc
import Builtins.Builtins
import SystemF.Build
import SystemF.IncrementalSubstitution
import SystemF.Rename
import SystemF.Syntax
import SystemF.MemoryIR
import SystemF.PrintMemoryIR
import qualified Type.Rename as Rename
import Type.Rename(Renameable(..))
import qualified Type.Substitute as Substitute
import Type.Substitute(Substitutable(..), substitute, freshen)
import Type.Type
import Type.Environment
import Type.Eval

breakAt n xs = go n xs
  where
    go 0 ys     = Just (take n xs, ys)
    go i (_:ys) = go (i-1) ys
    go _ []     = Nothing

-- | Type index of stream expressions
data Stream

type ExpS = Exp Stream
type AltS = Alt Stream
type FunS = Fun Stream

newtype instance Pat Stream = PatS {fromPatS :: Pat Mem}
newtype instance Alt Stream = AltS {fromAltS :: BaseAlt Stream}
newtype instance Fun Stream = FunS {fromFunS :: BaseFun Stream}

data instance Exp Stream =
    -- | An expression that's not representable in this form
    OtherSE !ExpM
    -- | A stream-specific operation
  | OpSE
    { sexpInfo :: ExpInfo
    , sexpOp :: !StreamOp
      -- | Repr arguments describing the data types manipulated by this
      --   stream operation.
    , sexpReprArgs :: [ExpM]
      -- | Other non-stream arguments.
    , sexpMiscArgs :: [ExpM]
      -- | Stream arguments.
    , sexpStreamArgs :: [ExpS]
      -- | The optional output pointer for stream expressions whose return
      --   type is a bare type.
    , sexpReturnArg :: !(Maybe ExpM)
    }
    -- | Lambda expression
  | LamSE
    { sexpInfo :: ExpInfo
    , sexpFun  :: FunS
    }
    -- | A let expression
  | LetSE
    { sexpInfo   :: ExpInfo
    , sexpBinder :: PatM
    , sexpValue  :: ExpM
    , sexpBody   :: ExpS
    }
    -- | Recursive definition group.
    --   These functions are treated as local non-stream functions.
    --   If they are, in fact, continuations/join points, the stream
    --   optimizer will treat them as unknown function calls.
  | LetfunSE
    { sexpInfo :: ExpInfo
    , sexpDefs :: DefGroup (FDef Mem)
    , sexpBody :: ExpS
    }
    -- | Case analysis 
  | CaseSE
    { sexpInfo :: ExpInfo
    , sexpScrutinee :: ExpM
    , sexpAlternatives :: [AltS]
    }
    -- | Raise an exception instead of producing a stream.
    -- The expression's type is decomposed into parts.
  | ExceptSE
    { sexpInfo :: ExpInfo
    , sexpStreamType :: !StreamType
    , sexpElementType :: Type
    }

instance Renameable (Exp Stream) where
  rename rn expression =
    case expression
    of OtherSE e -> OtherSE $ rename rn e
       OpSE inf op repr_args misc_args stream_args ret_arg ->
         OpSE inf (rename rn op) (rename rn repr_args)
         (rename rn misc_args) (rename rn stream_args) (rename rn ret_arg)
       LamSE inf f ->
         LamSE inf (rename rn f)
       LetSE inf pat rhs body ->
         let rhs' = rename rn rhs
         in renamePatM rn pat $ \rn' pat' ->
            LetSE inf pat' rhs' (rename rn' body)
       LetfunSE inf defs body ->
         renameDefGroup rn defs $ \rn' defs' ->
         LetfunSE inf defs' (rename rn' body)
       CaseSE inf scr alts ->
         CaseSE inf (rename rn scr) (map (rename rn) alts)
       ExceptSE inf st ty ->
         ExceptSE inf (rename rn st) (rename rn ty)

instance Renameable (Fun Stream) where
  rename rn (FunS fun) =
    renameTyPats rn (funTyParams fun) $ \rn' ty_params -> 
    renamePatMs rn' (map fromPatS $ funParams fun) $ \rn'' params ->
    let ret = rename rn'' $ funReturn fun
        body = rename rn'' $ funBody fun
    in FunS $ Fun { funInfo = funInfo fun
                  , funTyParams = ty_params
                  , funParams = map PatS $ params
                  , funReturn = ret
                  , funBody = body}

  freeVariables (FunS fun) =
    Rename.bindersFreeVariables [p | TyPat p <- funTyParams fun] $
    let uses_fv = freeVariables (map (patMDmd . fromPatS) $ funParams fun)
        params_fv = Rename.bindersFreeVariables (map (patMBinder . fromPatS) $ funParams fun) $
                    freeVariables (funBody fun) `Set.union`
                    freeVariables (funReturn fun)
    in Set.union uses_fv params_fv

instance Renameable (Alt Stream) where
  rename rn (AltS (Alt con params body)) =
    renameDeConInst rn con $ \rn' con' ->
    renamePatMs rn' (map fromPatS params) $ \rn'' params' ->
    AltS $ Alt con' (map PatS params') (rename rn'' body)

  freeVariables (AltS (Alt decon params body)) =
    deConFreeVariables decon $
    let uses_fv = freeVariables (map (patMDmd . fromPatS) params) 
        params_fv = Rename.bindersFreeVariables (map (patMBinder . fromPatS) params) $
                    freeVariables body
    in Set.union uses_fv params_fv

instance Substitutable (Exp Stream) where
  type Substitution (Exp Stream) = Subst
  substituteWorker s expression =
    case expression
    of OtherSE e -> OtherSE `liftM` substitute s e 
       OpSE inf op repr_args misc_args stream_args return_arg -> do
         op' <- substitute (typeSubst s) op
         repr_args' <- substitute s repr_args
         misc_args' <- substitute s misc_args
         stream_args' <- substitute s stream_args
         return_arg' <- substitute s return_arg
         return $ OpSE inf op' repr_args' misc_args' stream_args' return_arg'
       LamSE inf f ->
         LamSE inf `liftM` substitute s f
       LetSE inf b rhs body -> do
         rhs' <- substitute s rhs
         substitutePatM s b $ \s' b' -> do
           body' <- substitute s' body
           return $ LetSE inf b' rhs' body'
       LetfunSE inf defs body -> do
         substituteDefGroup substitute s defs $ \s' defs' -> do
           body' <- substitute s' body
           return $ LetfunSE inf defs' body'
       CaseSE inf scr alts -> do
         scr' <- substitute s scr
         alts' <- substitute s alts
         return $ CaseSE inf scr' alts'
       ExceptSE inf st ty -> do
         let type_subst = typeSubst s
         st' <- substitute type_subst st
         ty' <- substitute type_subst ty
         return $ ExceptSE inf st' ty'

instance Substitutable (Fun Stream) where
  type Substitution (Fun Stream) = Subst
  substituteWorker s (FunS fun) =
    substituteTyPats s (funTyParams fun) $ \s' ty_params ->
    substitutePatMs s' (map fromPatS $ funParams fun) $ \s'' params -> do
      body <- substitute s'' $ funBody fun
      ret <- substitute (typeSubst s'') $ funReturn fun
      return $ FunS $ Fun { funInfo = funInfo fun
                          , funTyParams = ty_params
                          , funParams = map PatS params
                          , funReturn = ret
                          , funBody = body}

instance Substitutable (Alt Stream) where
  type Substitution (Alt Stream) = Subst
  substituteWorker s (AltS (Alt con params body)) =
    substituteDeConInst (typeSubst s) con $ \ts' con' ->
    substitutePatMs (setTypeSubst ts' s) (map fromPatS params) $ \s' params' -> do
      body' <- substitute s' body
      return $ AltS $ Alt con' (map PatS params') body'

-- | A stream type encodes the shape and implementation of a stream.
--
--   In most domains, there's a one-to-one correspondence between shape
--   and stream type.  The domain @list_dim@ has two stream types,
--   'SequenceType' and 'ListViewType'.
data StreamType =
    -- | 1D sequence type
    SequenceType

    -- | List view type
  | ListViewType

    -- | N-dimensional view type
  | ArrViewType {-#UNPACK#-} !Int

streamShapeType, streamIndexType :: StreamType -> Type

-- | Return the shape type of the stream, the same type that would be returned
--   by 'shape'.
streamShapeType st =
  case st
  of SequenceType -> list_dim
     ListViewType -> list_dim
     ArrViewType 0 -> dim0
     ArrViewType 1 -> dim1
     ArrViewType 2 -> dim2
  where
    list_dim = VarT $ coreBuiltin The_list_dim
    dim0 = VarT $ coreBuiltin The_dim0
    dim1 = VarT $ coreBuiltin The_dim1
    dim2 = VarT $ coreBuiltin The_dim2

-- | Return the index type of the stream, the same type that would be returned
--   by 'index'.
streamIndexType st =
  case st
  of SequenceType -> ix1
     ListViewType -> ix1
     ArrViewType 0 -> ix0
     ArrViewType 1 -> ix1
     ArrViewType 2 -> ix2
  where
    ix0 = varApp (coreBuiltin The_Stored) [VarT $ coreBuiltin The_NoneType]
    ix1 = varApp (coreBuiltin The_Stored) [intT]
    ix2 = varApp (coreBuiltin The_Tuple2) [ix1, ix1]

data ConsumerOp =
    -- | Reduce using a reducer and initial value
    --
    -- > (reduce @{other type arguments} @{type} {other arguments})
    -- >   {reducer} {init} {stream} {output pointer}
    Reduce Type

    -- | Reduce using a reducer
    --
    -- > (reduce @{other type arguments} @{type} {other arguments})
    -- >   {reducer} {stream} {output pointer}
  | Reduce1 Type

    -- | Reduce using a scatter algorithm
    --
    -- > (scatter @{other type arguments} @{in_type} @{out_type}
    -- >   {other arguments})
    -- >   {reducer} {stream} {output pointer}
  | Scatter Type Type

    -- | Reduce sequentially.  The type arguments are the input type and the
    --   accumulator type.
    --
    -- > (reduce @{other type arguments} @{input type} @{accumulator type}
    -- >   {other arguments}) {reducer} {init} {stream} {output pointer}
  | Fold Type Type

    -- | Build a data structure
  | Build Type

data StreamOp =
    -- | Generate a stream.
    --
    -- > generate @{shape indices} @{output type}
    -- >   {shape parameters} {output repr} {[shape], generator function}
    GenerateOp !StreamType Type

    -- | N-ary zip over streams using a transformer function to combine values.
    --   When N=1, the operation is 'map'.
    --
    -- > zipWith @{shape indices} @{input types} @{output type}
    -- >   {shape parameters} {input reprs, output repr}
    -- >   {transformer function} {input streams}
  | ZipOp !StreamType [Type] Type

    -- | Convert a stream to a 1D sequence.
    --
    -- > flatten @{shape indices} @{type} {shape_args} {repr} {input stream}
  | ToSequenceOp !StreamType Type

    -- | Convert a stream to a 1D view.
    --
    -- > flatten @{shape indices} @{type} {shape_args} {repr} {input stream}
  | ToView1Op !StreamType Type

    -- | Produce a 1D sequence of size 1. 
    --
    -- > return @{output type} {output repr} {output writer} {}
  | ReturnOp !Type

    -- | Produce a stream of size 0.
    --
    -- > empty @{output type} {output repr} {} {}
  | EmptyOp !StreamType !Type

    -- | Concatenate two sequences.
    --
    -- > chain @{output type} {output repr} {} {input stream 1, input stream 2}
  | ChainOp !Type

    -- | Traverse a linked list
    -- > traverse @{output type} {output repr} {} {list}
  | TraverseListOp !Type

    -- | The bind operation on sequences.
    --
    -- > bind @{producer type, transformer type}
    --        {producer repr} {} {producer, transformer}
  | BindOp !Type !Type

    -- | A fused Sequence version of 'generate' and 'bind'.
    --
    -- > generate_bind @{output type}
    -- >   {} {} {dim1_shape} {transformer function}
  | GenerateBindOp Type

    -- | Consume a stream and produce a single value.
    --   A reduction consumes a stream.  So does building a data structure.
    --
    -- > consume @{shape indices} @{reduction type parameters}
    -- >   {shape parameters} {repr} {reduction parameters}
  | ConsumeOp !StreamType !ConsumerOp

instance Renameable StreamOp where
  rename rn op =
    case op
    of GenerateOp st ty -> GenerateOp (rename rn st) (rename rn ty)
       ZipOp st tys ty -> ZipOp (rename rn st) (rename rn tys) (rename rn ty)
       ToSequenceOp st ty -> ToSequenceOp (rename rn st) (rename rn ty)
       ToView1Op st ty -> ToView1Op (rename rn st) (rename rn ty)
       ReturnOp ty -> ReturnOp (rename rn ty)
       EmptyOp st ty -> EmptyOp (rename rn st) (rename rn ty)
       ChainOp t -> ChainOp (rename rn t)
       BindOp t1 t2 -> BindOp (rename rn t1) (rename rn t2)
       GenerateBindOp t -> GenerateBindOp (rename rn t)
       ConsumeOp st r -> ConsumeOp (rename rn st) (rename rn r)

instance Renameable StreamType where
  rename _ t = t

instance Renameable ConsumerOp where
  rename rn (Reduce t) = Reduce (rename rn t)
  rename rn (Reduce1 t) = Reduce1 (rename rn t)
  rename rn (Scatter t1 t2) = Scatter (rename rn t1) (rename rn t2)
  rename rn (Fold t1 t2) = Fold (rename rn t1) (rename rn t2)
  rename rn (Build t) = Build (rename rn t)

instance Substitutable StreamOp where
  type Substitution StreamOp = Substitute.TypeSubst
  substituteWorker s op =
    case op
    of GenerateOp st ty ->
         GenerateOp `liftM` substitute s st `ap` substitute s ty
       ZipOp st tys ty ->
         ZipOp `liftM` substitute s st `ap` substitute s tys `ap` substitute s ty
       ToSequenceOp st ty ->
         ToSequenceOp `liftM` substitute s st `ap` substitute s ty
       ToView1Op st ty ->
         ToView1Op `liftM` substitute s st `ap` substitute s ty
       ReturnOp ty ->
         ReturnOp `liftM` substitute s ty
       EmptyOp st ty ->
         EmptyOp `liftM` substitute s st `ap` substitute s ty
       ChainOp ty ->
         ChainOp `liftM` substitute s ty
       BindOp t1 t2 ->
         BindOp `liftM` substitute s t1 `ap` substitute s t2
       GenerateBindOp t ->
         GenerateBindOp `liftM` substitute s t
       ConsumeOp st r ->
         ConsumeOp `liftM` substitute s st `ap` substitute s r

instance Substitutable StreamType where
  type Substitution StreamType = Substitute.TypeSubst
  substituteWorker _ t = return t
  
instance Substitutable ConsumerOp where
  type Substitution ConsumerOp = Substitute.TypeSubst
  substituteWorker s (Reduce t) = Reduce `liftM` substitute s t
  substituteWorker s (Reduce1 t) = Reduce1 `liftM` substitute s t
  substituteWorker s (Scatter t1 t2) = Scatter `liftM` substitute s t1 `ap` substitute s t2
  substituteWorker s (Fold t1 t2) = Fold `liftM` substitute s t1 `ap` substitute s t2
  substituteWorker s (Build t) = Build `liftM` substitute s t

-- | Decompose a stream type into its shape and contents
deconstructStreamType :: Type -> UnboxedTypeEvalM (StreamType, Type)
deconstructStreamType ty = do
  ty' <- reduceToWhnf ty
  case fromVarApp ty' of
    Just (op, [arg])
      | op `isCoreBuiltin` The_Sequence -> return (SequenceType, arg)

    Just (op, [shape_arg, arg])
      | op `isCoreBuiltin` The_view -> do
          shp <- reduceToWhnf shape_arg
          case shp of
            VarT v
              | v `isCoreBuiltin` The_list_dim -> return (ListViewType, arg)
              | v `isCoreBuiltin` The_dim0 -> return (ArrViewType 0, arg)
              | v `isCoreBuiltin` The_dim1 -> return (ArrViewType 1, arg)
              | v `isCoreBuiltin` The_dim2 -> return (ArrViewType 2, arg)

    -- Don't know how to handle other types
    _ -> internalError "deconstructStreamType"

reconstructStreamType :: StreamType -> Type -> Type
reconstructStreamType stream_type ty =
  case stream_type
  of SequenceType ->
       varApp (coreBuiltin The_Sequence) [ty]
     ListViewType -> view_type (VarT $ coreBuiltin The_list_dim)
     ArrViewType n ->
       view_type $!
       case n
       of 0 -> VarT $ coreBuiltin The_dim0
          1 -> VarT $ coreBuiltin The_dim1
          2 -> VarT $ coreBuiltin The_dim2
  where
    view_type shape_arg = varApp (coreBuiltin The_view) [shape_arg, ty]

-------------------------------------------------------------------------------
-- Pretty-printing

asApplication :: [PrecDoc] -> PrecDoc
asApplication [] =
  parens empty `hasPrec` atomicPrec

asApplication [x] = x

asApplication (x:xs) =
  let op_doc = x ?+ appPrec
      args_doc = map (?+ appPrec) xs
  in hang op_doc 4 (sep args_doc) `hasPrec` appPrec

nameApplication :: String -> [PrecDoc] -> [PrecDoc]
nameApplication s xs = hasPrec (text s) atomicPrec : xs

pprParenList xs = parens $ sep $ punctuate (text ",") xs

pprStreamType :: StreamType -> PrecDoc
pprStreamType SequenceType = text "Sequence" `hasPrec` atomicPrec
pprStreamType ListViewType = text "list_view" `hasPrec` atomicPrec
pprStreamType (ArrViewType n) = text "view" <> int n `hasPrec` atomicPrec

pprStreamOp :: StreamOp -> PrecDoc
pprStreamOp op = asApplication $ pprStreamOp' op

pprStreamOp' :: StreamOp -> [PrecDoc]
pprStreamOp' (GenerateOp st ty) =
  nameApplication "generate" [pprStreamType st, pprTypePrec ty]

pprStreamOp' (ZipOp st [t] t') =
  nameApplication "map" [pprStreamType st, pprTypePrec t, pprTypePrec t']
                 
pprStreamOp' (ZipOp st ts t') =
  nameApplication "zip" (pprStreamType st : map pprTypePrec ts ++ [pprTypePrec t'])

pprStreamOp' (ToSequenceOp st t) =
  nameApplication "to_sequence" [pprStreamType st, pprTypePrec t]

pprStreamOp' (ToView1Op st t) =
  nameApplication "to_view1" [pprStreamType st, pprTypePrec t]

pprStreamOp' (BindOp t1 t2) =
  nameApplication "bind" [pprTypePrec t1, pprTypePrec t2]

pprStreamOp' (GenerateBindOp t) =
  nameApplication "generate_bind" [pprTypePrec t]

pprStreamOp' (ReturnOp t) =
  nameApplication "return" [pprTypePrec t]

pprStreamOp' (EmptyOp st t) =
  nameApplication "empty" [pprStreamType st, pprTypePrec t]

pprStreamOp' (ChainOp t) =
  nameApplication "chain" [pprTypePrec t]

pprStreamOp' (ConsumeOp st op) =
  let (name, tys) = case op
                    of Reduce ty -> ("reduce", [ty])
                       Reduce1 ty -> ("reduce1", [ty])
                       Scatter in_ty out_ty -> ("scatter", [in_ty, out_ty])
                       Fold in_ty acc_ty -> ("fold", [in_ty, acc_ty])
                       Build ty -> ("build", [ty])
  in nameApplication name (pprStreamType st : map pprTypePrec tys)

pprExpSPrec :: ExpS -> PrecDoc  
pprExpSPrec expression = 
  case expression
  of OtherSE e -> pprExpPrec e
     OpSE _ op repr_args misc_args stream_args ret_arg ->
       let arg_group xs = braces (sep $ map pprExp xs) `hasPrec` atomicPrec
       in asApplication $ pprStreamOp' op ++
                          arg_group repr_args :
                          arg_group misc_args :
                          map pprExpSPrec stream_args ++
                          maybeToList (fmap pprExpPrec ret_arg)
     LamSE _ f ->
       pprFunS f
     LetSE _ pat rhs body ->
       hang (text "let" <+> pprPat pat <+> text "=") 6 (pprExp rhs) $$
       pprExpS body `hasPrec` stmtPrec
     LetfunSE _ defs body ->
       text "letfun" <+> pprFDefGroup defs $$
       pprExpS body `hasPrec` stmtPrec
     CaseSE _ scr alts ->
       text "case" <+> pprExp scr $$
       text "of" <+> vcat (map pprAltS alts) `hasPrec` stmtPrec
     ExceptSE _ st ty ->
       asApplication $ nameApplication "except" [pprStreamType st, pprTypePrec ty]

pprAltS :: AltS -> Doc
pprAltS (AltS (Alt decon params body)) =
  hang (pprPatternMatch decon (map fromPatS params) <> text ".") 2
  (pprExpS body)

pprFunS :: FunS -> PrecDoc
pprFunS (FunS f) =
  let ty_params_doc = map pprTyPat $ funTyParams f
      params_doc = map (pprPat . fromPatS) $ funParams f
      return_doc = pprTypePrec (funReturn f) ?+ funPrec
      body_doc = pprExpSPrec (funBody f) ? stmtPrec
      sig_doc = sep [pprParenList (ty_params_doc ++ params_doc),
                     nest (-3) $ text "->" <+> return_doc]
  in hang (text "lambda" <+> sig_doc <> text ".") 2 body_doc
     `hasPrec` stmtPrec

pprExpS :: ExpS -> Doc
pprExpS e = pprExpSPrec e ? outerPrec

-------------------------------------------------------------------------------
-- Converting ordinary expressions to stream expressions

interpretViewShape :: Type -> UnboxedTypeEvalM (Maybe StreamType)
interpretViewShape ty = do
  ty' <- reduceToWhnf ty
  case ty' of
    VarT v
      | v `isCoreBuiltin` The_list_dim ->
          return $ Just ListViewType
      | v `isCoreBuiltin` The_dim1 ->
          return $ Just (ArrViewType 1)
      | v `isCoreBuiltin` The_dim2 ->
          return $ Just (ArrViewType 2)
    _ -> return Nothing

interpretViewShape' :: Type -> UnboxedTypeEvalM StreamType
interpretViewShape' ty = interpretViewShape ty >>= check
  where
    check Nothing  = internalError "interpretViewShape': Unrecognized type"
    check (Just t) = return t

data StreamOpInterpreter =
  StreamOpInterpreter
  { checkArity :: !(Int -> Int -> Bool)
  , interpretOp :: !(ExpInfo -> [Type] -> [ExpM] -> UnboxedTypeEvalM (Maybe ExpS))
  }

streamOpTable :: IntMap.IntMap StreamOpInterpreter
streamOpTable =
  IntMap.fromList [(fromIdent $ varID v, f) | (v, f) <- list]
  where
    list = [ (coreBuiltin The_reduce_list_dim, interpretReduce ListViewType)
           , (coreBuiltin The_reduce1_list_dim, interpretReduce1 ListViewType)
           , (coreBuiltin The_Sequence_reduce, interpretReduce SequenceType)
           , (coreBuiltin The_Sequence_reduce1, interpretReduce1 SequenceType)
           , (coreBuiltin The_Sequence_scatter, interpretScatter SequenceType)
           , (coreBuiltin The_Sequence_fold, interpretFold SequenceType)
           , (coreBuiltin The_Sequence_generate, interpretSequenceGenerate)
           , (coreBuiltin The_Sequence_map, interpretSequenceZip 1)
           , (coreBuiltin The_Sequence_zipWith, interpretSequenceZip 2)
           , (coreBuiltin The_Sequence_zipWith3, interpretSequenceZip 3)
           , (coreBuiltin The_Sequence_zipWith4, interpretSequenceZip 4)
           , (coreBuiltin The_viewToSequence, interpretToSequence ListViewType)
           , (coreBuiltin The_Sequence_bind, interpretBind)
           , (coreBuiltin The_Sequence_generate_bind, interpretGenerateBind)
           , (coreBuiltin The_Sequence_return, interpretReturn)
           , (coreBuiltin The_Sequence_empty, interpretEmpty SequenceType)
           , (coreBuiltin The_Sequence_chain, interpretChain)
           , (coreBuiltin The_Sequence_from_llist, interpretFromLList)
             {-, (coreBuiltin The_view1_array1_build, interpretBuild (PolyViewType 1) ArrayType)
           , (coreBuiltin The_view1_list_build, interpretBuild (PolyViewType 1) ListType)
           , (coreBuiltin The_view1_empty, interpretEmptyView)
           , (coreBuiltin The_Sequence_array1_build, interpretBuild PolySequenceType ArrayType)
           , (coreBuiltin The_Sequence_list_build, interpretBuild SequenceType) -}
           ]

-- | Overloaded view operations
viewOpTable :: IntMap.IntMap StreamOpInterpreter
viewOpTable =
  IntMap.fromList [(fromIdent $ varID v, f) | (v, f) <- list]
  where
    list = [ (coreBuiltin The_view_generate, interpretViewGenerate)
           , (coreBuiltin The_view_map, interpretViewZip 1)
           , (coreBuiltin The_view_zipWith, interpretViewZip 2)
           , (coreBuiltin The_view_zipWith3, interpretViewZip 3)
           , (coreBuiltin The_view_zipWith4, interpretViewZip 4)
           ]

interpretViewGenerate = StreamOpInterpreter check_arity interpret
  where
    check_arity ty_args args = ty_args == 2 && args == 4
    
    interpret inf ty_args args = do
      let [stream_shape, ty] = ty_args
          [shape_dict, repr, dom, f] = args
      m_sh <- interpretViewShape stream_shape
      return $! case m_sh of
        Nothing -> Nothing
        Just sh ->
          let op = GenerateOp sh ty
          in Just $ OpSE inf op [repr] [dom, f] [] Nothing

interpretSequenceGenerate = StreamOpInterpreter check_arity interpret
  where
    check_arity ty_args args = ty_args == 1 && args == 3
    
    interpret inf ty_args args = do
      let [ty] = ty_args
          [repr, dom, f] = args
      let op = GenerateOp SequenceType ty
      return $ Just $ OpSE inf op [repr] [dom, f] [] Nothing

interpretSequenceZip n_inputs = StreamOpInterpreter check_arity interpret
  where
    check_arity ty_args args = ty_args == n_ty_args && args == n_args

    interpret inf ty_args args = do
      let input_types = init ty_args
          output_type = last ty_args
          Just (repr_args, transformer : inputs) = breakAt (1 + n_inputs) args
      let op = ZipOp SequenceType input_types output_type
      stream_exps <- mapM interpretStreamSubExp inputs
      return $ Just $ OpSE inf op repr_args [transformer] stream_exps Nothing
    
    n_ty_args = n_inputs + 1
    n_args = 2 * n_inputs + 2

interpretViewZip n_inputs = StreamOpInterpreter check_arity interpret
  where
    check_arity ty_args args = ty_args == n_ty_args && args == n_args
    
    interpret inf ty_args args = do
      let (stream_shape : ty_args') = ty_args
          input_types = init ty_args'
          output_type = last ty_args'
          (shape_dict_arg : args') = args
          Just (repr_args, transformer : inputs) = breakAt (1 + n_inputs) args'
      m_sh <- interpretViewShape stream_shape
      case m_sh of
        Nothing -> return Nothing
        Just sh -> do
          let op = ZipOp sh input_types output_type
          stream_exps <- mapM interpretStreamSubExp inputs
          return $ Just $ OpSE inf op repr_args [transformer] stream_exps Nothing
    
    n_ty_args = n_inputs + 2
    n_args = 2 * n_inputs + 3

interpretReduce stream_type = StreamOpInterpreter check_arity interpret
  where
    -- There is one optional argument for the output pointer
    check_arity ty_args args = ty_args == 1 && (args == 4 || args == 5)

    interpret inf ty_args args = do
      let [ty] = ty_args
          repr : reducer : init : source : other_args = args
          maybe_return_arg = case other_args
                             of [] -> Nothing
                                [x] -> Just x
          op = ConsumeOp stream_type (Reduce ty)

      stream_exp <- interpretStreamSubExp source
      return $ Just $ OpSE inf op [repr] [reducer, init] [stream_exp] maybe_return_arg

interpretReduce1 stream_type = StreamOpInterpreter check_arity interpret
  where
    -- There is one optional argument for the output pointer
    check_arity ty_args args =
      ty_args == 1 && (args == 3 || args == 4)

    interpret inf ty_args args = do
      let [ty] = ty_args
          repr : reducer : source : other_args = args
          maybe_return_arg = case other_args
                             of [] -> Nothing
                                [x] -> Just x
          op = ConsumeOp stream_type (Reduce1 ty)

      stream_exp <- interpretStreamSubExp source
      return $ Just $ OpSE inf op [repr] [reducer] [stream_exp] maybe_return_arg

interpretScatter stream_type = StreamOpInterpreter check_arity interpret
  where
    -- There is one optional argument for the output pointer
    check_arity ty_args args =
      ty_args == 2 && (args == 4 || args == 5)

    interpret inf ty_args args = do
      let [in_type, out_type] = ty_args
          in_repr : out_repr : reducer : source : other_args = args
          maybe_return_arg = case other_args
                             of [] -> Nothing
                                [x] -> Just x
          op = ConsumeOp stream_type (Scatter in_type out_type)

      stream_exp <- interpretStreamSubExp source
      return $ Just $ OpSE inf op [in_repr, out_repr] [reducer]
        [stream_exp] maybe_return_arg

interpretFold stream_type = StreamOpInterpreter check_arity interpret
  where
    -- There is one optional argument for the output pointer
    check_arity ty_args args =
      ty_args == 2 && (args == 5 || args == 6)

    interpret inf ty_args args = do
      let [in_type, acc_type] = ty_args
          in_repr : acc_repr : reducer : init : source : other_args = args
          maybe_return_arg = case other_args
                             of [] -> Nothing
                                [x] -> Just x
          op = ConsumeOp stream_type (Fold in_type acc_type)

      stream_exp <- interpretStreamSubExp source
      return $ Just $ OpSE inf op [in_repr, acc_repr] [reducer, init]
        [stream_exp] maybe_return_arg

interpretToSequence stream_type = StreamOpInterpreter check_arity interpret
  where
    check_arity ty_args args = ty_args == 1 && args == 2
    
    interpret inf ty_args args = do
      let [ty] = ty_args
          [repr, src] = args
          op = ToSequenceOp stream_type ty
      src_stream <- interpretStreamSubExp src
      return $ Just $ OpSE inf op [repr] [] [src_stream] Nothing

interpretBind = StreamOpInterpreter check_arity interpret
  where
    check_arity 2 3 = True
    check_arity _ _ = False
    
    interpret inf [t1, t2] [repr, producer, transformer] = do
      producer' <- interpretStreamSubExp producer
      transformer' <- interpretStreamSubExp transformer
      return $ Just $ OpSE inf (BindOp t1 t2) [repr] [] [producer', transformer'] Nothing

interpretGenerateBind = StreamOpInterpreter check_arity interpret
  where
    check_arity 1 2 = True
    check_arity _ _ = False
    
    interpret inf [t] [shape, transformer] = do
      transformer' <- interpretStreamSubExp transformer
      return $ Just $ OpSE inf (GenerateBindOp t) [] [shape] [transformer'] Nothing

interpretReturn = StreamOpInterpreter check_arity interpret
  where
    check_arity 1 2 = True
    check_arity _ _ = False
    
    interpret inf [ty] [repr, gen] = do
      return $ Just $ OpSE inf (ReturnOp ty) [repr] [gen] [] Nothing

interpretEmpty stream_type = StreamOpInterpreter check_arity interpret
  where
    check_arity 1 1 = True
    check_arity _ _ = False
    
    interpret inf [ty] [repr] = do
      return $ Just $ OpSE inf (EmptyOp stream_type ty) [repr] [] [] Nothing

interpretChain = StreamOpInterpreter check_arity interpret
  where
    check_arity 1 3 = True
    check_arity _ _ = False

    interpret inf [ty] [repr, s1, s2] = do
      s1' <- interpretStreamSubExp s1
      s2' <- interpretStreamSubExp s2
      return $ Just $ OpSE inf (ChainOp ty) [repr] [] [s1', s2'] Nothing

interpretFromLList = StreamOpInterpreter check_arity interpret
  where
    check_arity 1 2 = True
    check_arity _ _ = False

    interpret inf [ty] [repr, l] =
      return $ Just $ OpSE inf (TraverseListOp ty) [repr] [l] [] Nothing

interpretBuild stream_type =
  StreamOpInterpreter check_arity interpret
  where
    -- There is one optional argument for the output pointer
    check_arity 1 2 = True
    check_arity 1 3 = True
    check_arity _ _ = False

    interpret inf [ty] (repr : s : other_args) = do
      s' <- interpretStreamSubExp s
      let op = ConsumeOp stream_type (Build ty)
          ret_arg = case other_args
                    of [] -> Nothing
                       [e] -> Just e
      return $ Just $ OpSE inf op [repr] [] [s'] ret_arg

{-

interpretEmptyView = StreamOpInterpreter check_arity interpret
  where
    check_arity 1 1 = True
    check_arity _ _ = False
    
    interpret inf [ty] [repr] = do
      return $ OpSE inf (EmptyViewOp 1 ty) [] [repr] [] [] Nothing
-}

interpretStreamSubExp :: ExpM -> UnboxedTypeEvalM ExpS
interpretStreamSubExp expression =
  case fromExpM expression of
    AppE inf op ty_args args -> do
      interpreted <- interpretStreamAppExp inf op ty_args args
      case interpreted of
        Just e  -> return e
        Nothing -> embed_expression
    VarE inf op_var -> do
      interpreted <- interpretStreamAppExp inf expression [] []
      case interpreted of
        Just e  -> return e
        Nothing -> embed_expression
    LamE inf f -> do
      liftM (LamSE inf) $ interpretStreamFun f
    LetE inf pat rhs body -> do
      body' <- assumePatM pat $ interpretStreamSubExp body
      return $ LetSE inf pat rhs body'
    LetfunE inf defs body -> do
      ((), body') <-
        assumeFDefGroup defs (return ()) $ interpretStreamSubExp body
      return $ LetfunSE inf defs body'
    CaseE inf scr alts -> do
      alts' <- mapM interpretStreamAlt alts
      return $ CaseSE inf scr alts'
    ExceptE inf ty -> do
      (stream_type, element_type) <- deconstructStreamType ty
      return $ ExceptSE inf stream_type element_type
    _ -> embed_expression
  where
    embed_expression = return $ OtherSE expression

interpretStreamFun :: FunM -> UnboxedTypeEvalM FunS
interpretStreamFun (FunM fun) =
  assumeTyPats (funTyParams fun) $
  assumePatMs (funParams fun) $ do
    body <- interpretStreamSubExp $ funBody fun
    return $ FunS $ Fun { funInfo = funInfo fun
                        , funTyParams = funTyParams fun
                        , funParams = map PatS $ funParams fun
                        , funReturn = funReturn fun
                        , funBody = body }

interpretStreamAlt :: AltM -> UnboxedTypeEvalM AltS
interpretStreamAlt (AltM alt) =
  assumeBinders (deConExTypes $ altCon alt) $
  assumePatMs (altParams alt) $ do
    body <- interpretStreamSubExp $ altBody alt
    return $ AltS $ Alt (altCon alt) (map PatS $ altParams alt) body

-- | Interpret a stream expression that is a function application.
--   If the expression can't be interpeted as a stream, return Nothing.
interpretStreamAppExp :: ExpInfo -> ExpM -> [Type] -> [ExpM]
                      -> UnboxedTypeEvalM (Maybe ExpS)
interpretStreamAppExp inf op ty_args args =
  case op
  of -- Match a known function call
     ExpM (VarE _ op_var) ->
       case IntMap.lookup (fromIdent $ varID op_var) streamOpTable 
       of Just interpreter
            | checkArity interpreter (length ty_args) (length args) ->
                interpretOp interpreter inf ty_args args
          _ -> return Nothing

     -- Match a shape-polymorphic function call.  The operator is a function
     -- application term.
     (unpackVarAppM -> Just (op_var, [ty_arg], [arg])) ->
       case IntMap.lookup (fromIdent $ varID op_var) viewOpTable 
       of Just interpreter
            | checkArity interpreter (1 + length ty_args) (1 + length args) ->
                interpretOp interpreter inf (ty_arg : ty_args) (arg : args)
          _ -> return Nothing

     _ -> return Nothing

-- | Interpret a stream expression that is a function application.
--   If the expression can't be interpeted as a stream, return Nothing.
isStreamAppExp :: ExpM -> [Type] -> [ExpSM] -> Bool
isStreamAppExp op tys args =
  case op
  of -- Match a known function call
     ExpM (VarE _ op_var) ->
       case IntMap.lookup (fromIdent $ varID op_var) streamOpTable
       of Nothing -> False
          Just interpreter -> checkArity interpreter (length tys) (length args)

     -- Match a shape-polymorphic function call.  The operator is a function
     -- application term.
     (unpackVarAppM -> Just (op_var, ty_arg, arg)) ->
       case IntMap.lookup (fromIdent $ varID op_var) viewOpTable 
       of Just interpreter ->
            checkArity interpreter (1 + length tys) (1 + length args)
          Nothing -> False

     _ -> False

-------------------------------------------------------------------------------
-- Convert a stream expression to a System F expression

-- | Instantiate a shape-polymorphic view operation
embedViewOp :: Var -> StreamType -> ExpM
embedViewOp op stream_type =
  let (shape, dict) =
        case stream_type
        of ListViewType -> (coreBuiltin The_list_dim,
                            coreBuiltin The_ShapeDict_list_dim)
           ArrViewType 1 -> (coreBuiltin The_dim1,
                             coreBuiltin The_ShapeDict_dim1)
           ArrViewType 2 -> (coreBuiltin The_dim2,
                             coreBuiltin The_ShapeDict_dim2)
  in appE' (varE' op) [VarT shape] [varE' dict]

-- | Convert a stream operator to a function and set of type parameters
embedOp :: StreamOp -> (ExpM, [Type])
embedOp (GenerateOp stream_type output_type) = let
  op = case stream_type
       of SequenceType -> varE' (coreBuiltin The_Sequence_generate)
          ListViewType -> view_op
          ArrViewType _ -> view_op

  view_op = embedViewOp (coreBuiltin The_view_generate) stream_type
  in (op, [output_type])

embedOp (ZipOp stream_type input_types output_type) = let
  n_input_types = length input_types
  op = case stream_type
       of SequenceType ->
            case n_input_types
            of 1 -> varE' $ coreBuiltin The_Sequence_map
               2 -> varE' $ coreBuiltin The_Sequence_zipWith
               3 -> varE' $ coreBuiltin The_Sequence_zipWith3
               4 -> varE' $ coreBuiltin The_Sequence_zipWith4
          ListViewType -> view_op
          ArrViewType _ -> view_op
  view_op = 
    let op = case n_input_types
             of 1 -> coreBuiltin The_view_map
                2 -> coreBuiltin The_view_zipWith
                3 -> coreBuiltin The_view_zipWith3
                4 -> coreBuiltin The_view_zipWith4
    in embedViewOp op stream_type
  in (op, input_types ++ [output_type])

embedOp (ToSequenceOp st ty) =
  let op = case st
           of ListViewType -> coreBuiltin The_viewToSequence
  in (varE' op, [ty])

embedOp (ToView1Op st ty) =
  let op = case st
           of SequenceType -> coreBuiltin The_sequenceToView
  in (varE' op, [ty])

embedOp (ReturnOp ty) =
  (varE' $ coreBuiltin The_Sequence_return, [ty])

embedOp (EmptyOp st ty) =
  let op = case st
           of SequenceType -> varE' $ coreBuiltin The_Sequence_empty
              ListViewType -> varE' $ coreBuiltin The_empty_list_dim_view
  in (op, [ty])

embedOp (ChainOp ty) =
  (varE' $ coreBuiltin The_Sequence_chain, [ty])

embedOp (TraverseListOp ty) =
  (varE' $ coreBuiltin The_Sequence_from_llist, [ty])

embedOp (BindOp t1 t2) =
  (varE' $ coreBuiltin The_Sequence_bind, [t1, t2])

embedOp (GenerateBindOp t) =
  (varE' $ coreBuiltin The_Sequence_generate_bind, [t])

embedOp (ConsumeOp st (Reduce ty)) =
  let op = case st
           of SequenceType -> coreBuiltin The_Sequence_reduce
              ListViewType -> coreBuiltin The_reduce_list_dim
              ArrViewType 1 -> coreBuiltin The_reduce_dim1
  in (varE' op, [ty])

embedOp (ConsumeOp st (Reduce1 ty)) =
  let op = case st
           of SequenceType -> coreBuiltin The_Sequence_reduce1
              ListViewType -> coreBuiltin The_reduce1_list_dim
              ArrViewType 1 -> coreBuiltin The_reduce1_dim1
  in (varE' op, [ty])

embedOp (ConsumeOp st (Scatter in_ty out_ty)) =
  let op = case st
           of SequenceType -> coreBuiltin The_Sequence_scatter
              ListViewType -> coreBuiltin The_scatter_list_dim
              ArrViewType 1 -> coreBuiltin The_scatter_dim1
  in (varE' op, [in_ty, out_ty])

embedOp (ConsumeOp st (Fold in_ty acc_ty)) =
  let op = case st
           of SequenceType -> coreBuiltin The_Sequence_fold
              ListViewType -> coreBuiltin The_fold_list_dim
              ArrViewType 1 -> coreBuiltin The_fold_dim1
  in (varE' op, [in_ty, acc_ty])

embedOp (ConsumeOp st (Build ty)) =
  let op = case st
           of SequenceType -> coreBuiltin The_Sequence_list_build
              ListViewType -> coreBuiltin The_build_list_dim_list
              ArrViewType 1 -> coreBuiltin The_build_dim1_array
  in (varE' op, [ty])

embedStreamExp :: ExpS -> ExpM
embedStreamExp expression =
  case expression
  of OpSE inf op reprs misc_args streams ret_args ->
       let (embedded_op, ty_args) = embedOp op
           stream_args = map embedStreamExp streams
       in appE inf embedded_op ty_args
          (reprs ++ misc_args ++ stream_args ++ maybeToList ret_args)
     OtherSE e -> e
     LamSE inf f -> 
       ExpM $ LamE inf (embedStreamFun f)
     LetSE inf b rhs body ->
       ExpM $ LetE inf b rhs (embedStreamExp body)
     LetfunSE inf defs body ->
       ExpM $ LetfunE inf defs (embedStreamExp body)
     CaseSE inf scr alts ->
       ExpM $ CaseE inf scr (map embedStreamAlt alts)
     ExceptSE inf stream_type element_type ->
       let ty = reconstructStreamType stream_type element_type
       in ExpM $ ExceptE inf ty

embedStreamFun (FunS f) =
  FunM $ Fun (funInfo f) (funTyParams f) (map fromPatS $ funParams f)
             (funReturn f) (embedStreamExp $ funBody f)

embedStreamAlt (AltS alt) =
  AltM $ Alt (altCon alt) (map fromPatS $ altParams alt)
             (embedStreamExp $ altBody alt)

-------------------------------------------------------------------------------

restructureStreamExp :: ExpS -> UnboxedTypeEvalM ExpS
restructureStreamExp e = restructureIfNeeded Set.empty e return

-- | Restructure a stream expression by hoisting out all non-data-dependent
--   case statements.  Restructuring can introduce code replication.
--   If the expression was restructured, pass the
--   part from inside case statements to the continuation, which will
--   decide what to do with it.  Otherwise pass Nothing.
--
--   Hoisting is only valid when it introduces no side effects.
--   To avoid introducing side effects, case statements are only hoisted if
--   their scrutinee (which will be executed more frequently) is a variable.
--
--   The nesting of case statements is preserved, which might be important
--   if we start hoisting in other situations.
restructureIfNeeded :: Set.Set Var
                    -> ExpS
                    -> (ExpS -> UnboxedTypeEvalM ExpS)
                    -> UnboxedTypeEvalM ExpS
restructureIfNeeded locals expression cont =
  case expression
  of OpSE {sexpStreamArgs = es} ->
       restructureListIfNeeded locals es $ \es' ->
       cont (expression {sexpStreamArgs = es'})
     LamSE inf f ->
       restructureLam locals f $ \f' ->
       cont (LamSE inf f')
     LetSE inf pat rhs body ->
       let locals' = Set.insert (patMVar pat) locals
       in assumePatM pat $
          restructureIfNeeded locals' body $ \body' ->
          cont (LetSE inf pat rhs body')
     LetfunSE inf defs body -> do
       let locals' = foldr Set.insert locals $
                     map definiendum (defGroupMembers defs)
       (_, e) <- assumeFDefGroup defs (return ()) $
                 restructureIfNeeded locals' body $ \body' ->
                 cont (LetfunSE inf defs body')
       return e
     CaseSE inf scr@(ExpM (VarE _ scr_var)) alts
       -- If the scrutinee is independent of stream-local variables, then
       -- float the case statement outward
       | not $ scr_var `Set.member` locals -> do
           alts' <- sequence [restructureAlt locals alt cont | alt <- alts]
           return $ CaseSE inf scr alts'
     _ ->
       cont expression

-- Restructure a case alternative that will be floated outward
restructureAlt locals (AltS (Alt con params body)) cont = do
  -- Rename local variables to avoid name conflicts
  (con', con_rn) <- freshenDeConInst con
  renamePatMs con_rn (map fromPatS params) $ \con_rn' params' -> do
    (params', param_rn) <- freshenPatMs params'
    let rn = param_rn `Rename.compose` con_rn'
        rn_body = rename rn body

    -- Restructure the case alternative body.
    -- The continuation is executed to move code inside the body.
    let extra_locals = map binderVar (deConExTypes con') ++ map patMVar params'
        locals' = foldr Set.insert locals extra_locals
    body' <- assumeBinders (deConExTypes con') $
             assumePatMs params' $
             restructureIfNeeded locals' rn_body cont

    -- Rebuild the case alternative.
    return $ AltS $ Alt con' (map PatS params') body'

restructureLam locals (FunS (Fun inf ty_params params ret body)) cont =
  let locals' = foldr Set.insert locals (map tyPatVar ty_params ++
                                         map (patMVar . fromPatS) params)
  in assumeTyPats ty_params $
     assumePatMs (map fromPatS params) $
     restructureIfNeeded locals' body $ \body' ->
     cont $ FunS (Fun inf ty_params params ret body')

-- | Restructure a list of stream expressions.
restructureListIfNeeded :: Set.Set Var 
                        -> [ExpS]
                        -> ([ExpS] -> UnboxedTypeEvalM ExpS)
                        -> UnboxedTypeEvalM ExpS
restructureListIfNeeded locals es cont = go es cont
  where
    go (e:es) k =
      restructureIfNeeded locals e $ \e' -> go es $ \es' -> k (e' : es')

    go [] k = k []

-- TODO: hoist case statements and non-excepting let statements
-- out of other stream expressions
--
-- > foo (case x of {A. S1; B. S2}) ==> case x of {A. foo S1; B. foo S2})

-- | Simplify a stream expression.

-- First, the expression is globally restructured.
-- Then a top-down simplification pass is performed.
simplifyStreamExp :: ExpS -> UnboxedTypeEvalM ExpS
simplifyStreamExp expression = do
  e' <- simplifyExp =<< restructureStreamExp expression
  traceShow (text "SIMPLIFY" <+> (pprExpS expression $$ text "----" $$ pprExpS e')) $ return e'
  
-- | Recursively transform a stream expression
simplifyExp :: ExpS -> UnboxedTypeEvalM ExpS
simplifyExp input_expression = do
  expression <- freshen input_expression
  case expression of
     -- Map operation: try to fuse with its producer
     OpSE inf op@(ZipOp st [in_type] out_type)
       repr_args@[in_repr, out_repr] [f] [in_stream] Nothing -> do
       (progress, e) <-
         fuseMapWithProducer st in_type out_type in_repr out_repr f in_stream

       -- If the expression was transformed, then re-simplify it.
       -- Otherwise, process subexpressions.
       if progress
         then simplifyExp e
         else simplify_subexpressions e

     -- Zip operation: if any argument is empty, the entire stream is empty
     OpSE inf op@(ZipOp st _ out_type) reprs _ stream_args _ -> do
       let out_repr = last reprs
       stream_args' <- mapM simplifyExp stream_args
       if any isEmptyStream stream_args'
         then return $ empty_stream inf st out_type out_repr
         else return $ expression {sexpStreamArgs = stream_args'}

     -- Convert to sequence: Try to replace the source stream with the
     -- equivalent sequence stream
     OpSE inf op@(ToSequenceOp st ty) [repr] [] [s] Nothing -> do
       e <- convertToSequenceOp s
       case e of
         Just e' -> simplifyExp e'
         Nothing -> do
           s' <- simplifyExp s
           if isEmptyStream s'
             then return $ empty_stream inf SequenceType ty repr
             else return $ expression {sexpStreamArgs = [s']}

     -- Sequence bind: Try to fuse with 'generate'
     OpSE inf op@(BindOp producer_ty transformer_ty)
       [repr] [] [producer, transformer] Nothing -> do
       simplifyBindOp inf op repr producer transformer

     _ -> simplify_subexpressions expression
  where
    empty_stream inf shape ty repr =
      OpSE inf (EmptyOp shape ty) [repr] [] [] Nothing

    simplify_subexpressions e =
      case e
      of OpSE {sexpStreamArgs = stream_args} -> do
           stream_args' <- mapM simplifyExp stream_args
           return $ e {sexpStreamArgs = stream_args'}
         LamSE inf f ->
           LamSE inf `liftM` simplifyStreamFun f
         CaseSE inf scr alts ->
           CaseSE inf scr `liftM` mapM simplifyStreamAlt alts
         _ -> return e

simplifyStreamAlt (AltS alt) =
  assumeBinders (deConExTypes $ altCon alt) $
  assumePatMs (map fromPatS $ altParams alt) $ do
    body <- simplifyExp $ altBody alt
    return $ AltS $ alt {altBody = body}

simplifyStreamFun (FunS fun) =
  assumeTyPats (funTyParams fun) $
  assumePatMs (map fromPatS $ funParams fun) $ do
    body <- simplifyExp $ funBody fun
    return $ FunS $ fun {funBody = body}

fuseMapWithProducer :: StreamType
                    -> Type -> Type -> ExpM -> ExpM -> ExpM -> ExpS
                    -> UnboxedTypeEvalM (Bool, ExpS)
fuseMapWithProducer shape in_type ty in_repr repr map_f producer =
  fuse_with_producer shape producer
  where
    fuse_with_producer :: StreamType -> ExpS -> UnboxedTypeEvalM (Bool, ExpS)
    fuse_with_producer shape producer =
      case producer
      of OpSE inf (GenerateOp st producer_ty)
           [producer_repr] [dim, gen_f] [] Nothing -> do
           new_gen_f <- fuse_with_generator [streamIndexType st] producer_ty gen_f

           progress $ OpSE inf (GenerateOp st ty) [repr] [dim, new_gen_f] [] Nothing

         OpSE inf (ZipOp st zip_tys producer_ty)
           zip_and_producer_reprs [zip_f] zip_streams Nothing -> do
           new_zip_f <- fuse_with_generator zip_tys producer_ty zip_f
           let zip_reprs = init zip_and_producer_reprs

           progress $ OpSE inf (ZipOp st zip_tys ty) (zip_reprs ++ [repr]) [new_zip_f] zip_streams Nothing

         OpSE inf (BindOp producer_ty transformer_ty)
           [producer_repr] [] [producer, transformer] Nothing -> do
           -- Fuse with the transformer
           m_transformer <- runMaybeT $ freshenUnaryStreamFunction transformer
           case m_transformer of
             Just (var, s) -> do
               (_, s') <- fuse_with_producer SequenceType s
               let return_type = varApp (coreBuiltin The_Sequence) [ty]
               progress $ OpSE inf (BindOp producer_ty ty) [producer_repr] []
                 [producer, mkUnaryStreamFunction defaultExpInfo var producer_ty
                            return_type s'] Nothing
             Nothing ->
               build_map_expression shape producer

         OpSE inf (GenerateBindOp transformer_ty)
           [] [shp] [transformer] Nothing -> do
           -- Fuse with the transformer
           m_transformer <- runMaybeT $ freshenUnaryStreamFunction transformer
           case m_transformer of
             Just (var, s) -> do
               (_, s') <- fuse_with_producer SequenceType s
               let stored_int_type =
                     varApp (coreBuiltin The_Stored) [intT]
                   return_type = varApp (coreBuiltin The_Sequence) [ty]
               progress $ OpSE inf (GenerateBindOp ty) [] [shp]
                 [mkUnaryStreamFunction defaultExpInfo var stored_int_type return_type s'] Nothing
             Nothing ->
               build_map_expression shape producer

         OpSE inf (EmptyOp st _) [_] [] [] Nothing -> 
           progress $ OpSE inf (EmptyOp st ty) [repr] [] [] Nothing

         OpSE inf (ReturnOp return_t) [_] [v] [] Nothing -> do
           -- Apply function to value
           tmpvar <- newAnonymousVar ObjectLevel
           let boxed_value = conE' (VarCon (coreBuiltin The_boxed) [return_t] []) [v]
               call = appE' map_f [] [varE' tmpvar]
               return_value = ExpM $ CaseE defaultExpInfo boxed_value
                              [AltM $ Alt (VarDeCon (coreBuiltin The_boxed) [return_t] [])
                               [patM (tmpvar ::: return_t)] call]
           progress $ OpSE inf (ReturnOp ty) [repr] [return_value] [] Nothing

         OpSE inf (ChainOp _) [_] [] [s1, s2] Nothing -> do
           -- Distribute over both streams
           (_, s1') <- fuse_with_producer shape s1
           (_, s2') <- fuse_with_producer shape s2
           progress $ OpSE inf (ChainOp ty) [repr] [] [s1', s2'] Nothing

         OpSE inf (ToSequenceOp st _) [_] [] [s] Nothing -> do
           (_, s') <- fuse_with_producer st s
           progress $ OpSE inf (ToSequenceOp st ty) [repr] [] [s'] Nothing

         LetSE inf pat rhs body -> do
           (_, body') <- assumePatM pat $
                         fuse_with_producer shape body
           progress $ LetSE inf pat rhs body'

         LetfunSE inf defs body -> do
           (_, (_, body')) <- assumeFDefGroup defs (return ()) $
                              fuse_with_producer shape body
           progress $ LetfunSE inf defs body'
         
         CaseSE inf scr alts -> do
           (progress_list, alts') <-
             mapAndUnzipM (fuse_with_alt shape) alts

           -- If any case alternatives introduced the potential for further
           -- optimization, then keep the change.
           -- Otherwise, leave the expression where it is.
           if or progress_list
             then progress $ CaseSE inf scr alts'
             else build_map_expression shape producer

         ExceptSE inf stream_type _ ->
           -- Return type of the exception statement is changed
           progress $ ExceptSE inf stream_type ty

         _ -> build_map_expression shape producer

    build_map_expression shape producer =
      no_progress $ OpSE defaultExpInfo (ZipOp shape [in_type] ty)
      [in_repr, repr] [map_f] [producer] Nothing

    fuse_with_alt shape alt = do 
      AltS (Alt decon params body) <- freshen alt
      (b, body') <- assumeBinders (deConExTypes decon) $
                    assumePatMs (map fromPatS params) $
                    fuse_with_producer shape body
      return (b, AltS $ Alt decon params body')

    -- Fuse with generator function
    -- > \ ARGS r. case boxed (gen_f ARGS) of boxed x. map_f x r
    fuse_with_generator arg_types producer_ty gen_f = do
      -- Rename the function to avoid name shadowing
      map_f' <- freshenFullyExp $ deferEmptySubstitution map_f
      lamE $
        mkFun []
        (\ [] -> return (arg_types ++ [outType ty], initEffectType ty))
        (\ [] args ->
          let arg_value_vars = init args
              out_ptr = last args
          in localE producer_ty
             (appExp (return gen_f) [] (map mkVarE arg_value_vars)) $ \x ->
             appExp (return map_f') [] [mkVarE x, mkVarE out_ptr])

    progress x = return (True, x)
    no_progress x = return (False, x)

-- | Convert a stream operation to an equivalent sequence operation, if
--   possible.
convertToSequenceOp :: ExpS -> UnboxedTypeEvalM (Maybe ExpS)
convertToSequenceOp expression =
  case expression
  of OpSE inf (GenerateOp st ty) repr_args misc_args [] Nothing ->
       case st
       of ListViewType ->
            -- Convert view_generate to Sequence_Generate
            return $ Just $
            OpSE inf (GenerateOp SequenceType ty) repr_args misc_args [] Nothing
          _ -> return Nothing
     _ -> return Nothing

simplifyBindOp :: ExpInfo -> StreamOp -> ExpM -> ExpS -> ExpS
               -> UnboxedTypeEvalM ExpS
simplifyBindOp inf bind_op@(BindOp producer_ty transformer_ty) repr producer transformer = do
  producer' <- simplifyExp producer
  case producer' of
    OpSE _ (GenerateOp SequenceType _) [_] [shp, gen_f] [] Nothing -> do
      -- Fuse the bind and generate operations together
      m_transformer <- runMaybeT $ freshenUnaryStreamFunction transformer
      case m_transformer of
        Nothing -> simplify_subexpressions producer'
        Just (transformer_var, transformer_body) -> do
          transformer_body' <- assume transformer_var producer_ty $ 
                               simplifyExp transformer_body

          -- Create a fused transformer function that runs the producer and
          -- transformer.
          --
          -- > \ ix. case boxed @(index dim1) (gen_f ix)
          -- >       of boxed @(index dim1) (transformer_var : index dim1).
          -- >       transformer_body
          ix_var <- newAnonymousVar ObjectLevel
          let new_transformer =
                fuse_bind_generate gen_f ix_var transformer_var transformer_body'
          return $ OpSE inf (GenerateBindOp transformer_ty)
            [] [shp] [new_transformer] Nothing

    _ | isEmptyStream producer' ->
      return $ OpSE inf (EmptyOp SequenceType transformer_ty) [] [] [] Nothing

    _ -> simplify_subexpressions producer'
  where
    simplify_subexpressions producer' = do
      transformer' <- simplifyStreamExp transformer
      return $ OpSE inf bind_op [repr] [] [producer', transformer'] Nothing

    fuse_bind_generate gen_f ix_var trans_var trans_body = let
      index_type = varApp (coreBuiltin The_index) [VarT $ coreBuiltin The_dim1]
      boxed_decon = VarDeCon (coreBuiltin The_boxed) [producer_ty] []
      boxed_con = VarCon (coreBuiltin The_boxed) [producer_ty] []
      case_alt = AltS $ Alt boxed_decon
                 [PatS $ patM (trans_var ::: producer_ty)] trans_body
      scr_exp = conE inf boxed_con
                [appE inf gen_f [] [ExpM $ VarE defaultExpInfo ix_var]]
      case_exp = CaseSE inf scr_exp [case_alt]
      in mkUnaryStreamFunction inf ix_var index_type
         (varApp (coreBuiltin The_Sequence) [transformer_ty]) case_exp

-- | Check whether the given expression is an empty stream.
--
 --   We look through stream expressions, but not through function calls.
--   If a stream function call is equivalent to the empty stream, that should
--   be detected when the function call is transformed (not here).
isEmptyStream :: ExpS -> Bool
isEmptyStream (OpSE {sexpOp = EmptyOp _ _}) = True
isEmptyStream (LetSE {sexpBody = s}) = isEmptyStream s
isEmptyStream (LetfunSE {sexpBody = s}) = isEmptyStream s
isEmptyStream (CaseSE {sexpAlternatives = [AltS (Alt _ _ s)]}) = isEmptyStream s
isEmptyStream _ = False

-------------------------------------------------------------------------------

-- | Convert a stream expression to a sequential loop.
--   The conversion only succeeds if the outermost term is a consumer.
--   The result is often better than simply inlining the stream operations.
sequentializeStreamExp :: ExpS -> UnboxedTypeEvalM (Maybe ExpM)
sequentializeStreamExp expression =
  case expression
  of OpSE inf (ConsumeOp st op) repr_args misc_args [src] ret_arg ->
       case op
       of Reduce ty -> runMaybeT $ do
            let [reducer, init] = misc_args
                [repr] = repr_args

            -- Assign the Repr to a variable to avoid replicating the
            -- same expression many times
            let_repr ty repr $ \repr_var -> do
              fold_exp <-
                sequentializeFold ty ty repr_var
                (varE' repr_var) init reducer src
              return $ appE inf fold_exp [] (maybeToList ret_arg)

          Reduce1 ty -> runMaybeT $ do
            let [reducer] = misc_args
                [repr] = repr_args

            -- Assign the Repr to a variable to avoid replicating the
            -- same expression many times
            let_repr ty repr $ \repr_var -> do
              let repr_exp = varE' repr_var

              -- Always create a function
              f <- lamE $
                   mkFun [] (\ [] -> return ([outType ty], initEffectType ty))
                   (\ [] [ret_var] -> do
                     -- Peeled continuation: call sequentializeFold
                     let peeled_cont s =
                           lamE $
                           mkFun [] (\ [] -> return ([ty, outType ty],
                                                    initEffectType ty))
                           (\ [] [x, ret] -> do
                               fold_exp <- sequentializeFold ty ty repr_var
                                           repr_exp (varE' x) reducer s
                               return $ appE inf fold_exp [] [varE' ret])
                     -- Empty continuation: error
                     let empty_cont =
                           lamE $ 
                           mkFun[] (\ [] -> return ([outType ty],
                                                    initEffectType ty))
                           (\ [] [ret] -> do
                               return $ ExpM $ ExceptE inf (initEffectType ty))
                     peelStream ty (varE' repr_var) ty repr_exp
                       peeled_cont empty_cont src (varE' ret_var))
              return $ appE inf f [] (maybeToList ret_arg)

          Fold in_ty acc_ty -> runMaybeT $ do
            let [reducer, init] = misc_args
                [repr_in, repr_acc] = repr_args

            -- Assign the Repr to a variable to avoid replicating the
            -- same expression many times
            let_repr in_ty repr_in $ \repr_in_var ->
              let_repr acc_ty repr_acc $ \repr_acc_var -> do
                fold_exp <-
                  sequentializeFold acc_ty in_ty repr_acc_var
                  (varE' repr_in_var) init reducer src
                return $ appE inf fold_exp [] (maybeToList ret_arg)

     _ -> return Nothing
  where
    -- Bind a Repr value to a temporary variable
    let_repr ty val k = do
      repr_var <- newAnonymousVar ObjectLevel
      k_expr <- k repr_var
      let repr_pat = patM (repr_var ::: varApp (coreBuiltin The_Repr) [ty])
      return $ letE repr_pat val k_expr

-- | Evaluate just the first element of a sequence that has list domain.
--   Statically construct a
--   new stream expression representing the rest of the stream.
--   This is used when sequentializing 'reduce1'.
peelStream :: Type              -- ^ Stream contents type
           -> ExpM              -- ^ Repr dictionary for stream source
           -> Type              -- ^ Return type produced by continuations
           -> ExpM              -- ^ Repr dictionary for return values
           -> (ExpS -> MaybeT UnboxedTypeEvalM ExpM)
              -- ^ Continuation to process a peeled stream.
              --   The computed expression has type
              --   @ret -> OutPtr ret -> Store@.
           -> MaybeT UnboxedTypeEvalM ExpM
              -- ^ Continuation to process a missing value.
              --   The computed expression has type @OutPtr ret -> Store@.
           -> ExpS              -- ^ Input stream
           -> ExpM              -- ^ Output pointer
           -> MaybeT UnboxedTypeEvalM ExpM
peelStream a_ty a_repr ret_ty ret_repr value_cont empty_cont source ret_ptr =
  -- This transformation may generate nested copies of the stream code
  -- (an outer copy to find the first element, and inner copies to process
  -- the remaining elements).
  -- Perform renaming to avoid name shadowing.
  freshenExpS source >>=
  peelStream' a_ty a_repr ret_ty ret_repr value_cont empty_cont ret_ptr

peelStream' a_ty a_repr ret_ty ret_repr value_cont empty_cont ret_ptr source =
  case source
  of OpSE inf (GenerateBindOp _) [] [shape] [f] Nothing -> do
       -- Return (f 0) and a stream of (f 1 .. f N)

       -- > peel_generate_bind @a @r a_repr ret_repr shape
       -- > $(make_body_function f) $(empty_cont) ret_ptr

       body_function <- make_body_function f
       failure <- empty_cont
       return $ appE' (varE' $ coreBuiltin The_peel_generate_bind)
         [a_ty, ret_ty]
         [a_repr, ret_repr, shape, body_function, failure, ret_ptr]

     OpSE inf (GenerateOp _ _) [repr] [shape, f] [] Nothing -> do
       -- Return (f 0) and a stream of (f 1 .. f N)
       -- > peel_generate @a @r a_repr ret_repr shape f
       -- > $(make_generate_function f) $(empty_cont) ret_ptr
       body_function <- make_generate_function f
       failure <- empty_cont
       return $ appE' (varE' $ coreBuiltin The_peel_generate)
         [a_ty, ret_ty]
         [a_repr, ret_repr, shape, body_function, failure, ret_ptr]
     
     OpSE inf (ReturnOp ty) [_] [w] [] Nothing -> do
       -- Bind the value to a temporary variable
       localE a_ty (return w) $ \x -> do
         -- The remaining stream is empty
         let s = OpSE inf (EmptyOp SequenceType a_ty) [a_repr] [] [] Nothing
         k_exp <- value_cont s
         return $ appE inf k_exp [] [varE' x, ret_ptr]

     OpSE inf (EmptyOp _ _) [_] [] [] Nothing -> do
       -- Stream is empty
       k_exp <- empty_cont
       return $ appE' k_exp [] [ret_ptr]

     LetSE inf pat rhs body -> assumeBinder (patMBinder pat) $ do
       -- Create a let binding
       e <- peelStream a_ty a_repr ret_ty ret_repr value_cont empty_cont
            body ret_ptr
       return $ ExpM $ LetE inf pat rhs e

     CaseSE inf scr alts -> do
       -- Create a case expression
       case_alts <- mapM peel_alt alts
       return $ ExpM $ CaseE inf scr case_alts

     -- We can't peel a 'bind' operation because the peeled stream is
     -- hard to compute
     OpSE _ (BindOp _ _) _ _ _ _ -> mzero

     -- We should handle more cases.
     _ -> internalError "peelStream: Unhandled expression constructor"
  where
    peel_alt (AltS (Alt decon params body)) =
      assumeBinders (deConExTypes decon) $
      assumePatMs [p | PatS p <- params] $ do
        body' <- peelStream a_ty a_repr ret_ty ret_repr value_cont empty_cont
                 body ret_ptr
        return $ AltM $ Alt decon [p | PatS p <- params] body'

    -- Create a shortened 'generate' loop
    --
    -- > (\d r -> $(value_cont (make_leftover_stream d f))
    -- >          (f 0) r)
    make_generate_function f =
      lamE $
      mkFun []
      (\ [] -> return ([list_dim_type, outType ret_ty], initEffectType ret_ty))
      (\ [] [leftover_domain, r] -> do
         s' <- make_leftover_generate_stream (varE' leftover_domain) f
         k <- value_cont s'

         -- Create a stored 'zero' value
         zero_var <- newAnonymousVar ObjectLevel
         let zero_exp = ExpM (LitE defaultExpInfo (IntL 0 intT))

         -- Call 'f' to create a value
         let value_exp = as_stored_int zero_exp zero_var $
                         appE' f [] [varE' zero_var]

         -- Bind the value to a new variable
         value_var <- newAnonymousVar ObjectLevel
         let cont_exp = appE' k [] [varE' value_var, varE' r]

         return $ letViaBoxed (value_var ::: a_ty) value_exp cont_exp)

    make_leftover_generate_stream d f = do
      f' <- lamE $
            mkFun [] (\ [] -> return ([stored_int_type, outType a_ty],
                                      initEffectType a_ty))
            (\ [] [i, r] -> do
               value_i <- newAnonymousVar ObjectLevel
               i' <- newAnonymousVar ObjectLevel

               -- Compute (i+1)
               let add_expression =
                     appE' (varE' $ coreBuiltin The_addI) []
                     [varE' value_i,
                      ExpM (LitE defaultExpInfo (IntL 1 intT))]

               return $ ExpM $ CaseE defaultExpInfo (varE' i)
                 [AltM $ Alt stored_decon [patM (value_i ::: intT)]
                  (as_stored_int add_expression i' $
                   appE' f [] [varE' i', varE' r])])

      return $ OpSE defaultExpInfo (GenerateOp SequenceType a_ty) [a_repr]
        [d, f'] [] Nothing

    -- Create a loop body function 
    --
    -- > (\i d k r ->
    -- >    case boxed (stored i) of boxed stored_i.
    -- >    $(peel (\x s' -> value_cont x
    -- >                     (make_leftover_stream inner_stream i d s'))
    -- >           (k r)
    -- >           (inner_stream stored_i) r)
    make_body_function inner_stream =
      lamE $
      mkFun []
      (\ [] -> return ([intT, list_dim_type, cont_type, outType a_ty],
                       initEffectType a_ty))
      (\ [] [index, leftover_domain, loop_cont, r] -> do
         stored_index <- newAnonymousVar ObjectLevel
         (inner_param, inner_body) <- freshenUnaryStreamFunction inner_stream
         let inner_body' =
               rename (Rename.singleton inner_param stored_index) inner_body
 
         assume stored_index stored_int_type $ do
           -- If peeling the inner stream produces a value, then construct
           -- a leftover stream and pass it to the value continuation
           let body_value_cont :: ExpS -> MaybeT UnboxedTypeEvalM ExpM
               body_value_cont leftover_stream = do
                 s <- make_leftover_generate_bind_stream inner_stream index
                      leftover_domain leftover_stream
                 value_cont s

           -- If no value is produced, invoke the failure continuation
           let body_empty_cont = return $ varE' loop_cont

           -- Peel the inner stream
           body_exp <- peelStream a_ty a_repr ret_ty ret_repr
                       body_value_cont body_empty_cont
                       inner_body' (varE' r)

           -- Bind the stored index to a variable
           let exp = as_stored_int (varE' index) stored_index body_exp
           return exp)
         

    -- Create a stream expression representing the part of the stream that
    -- wasn't evaluated by peeling.
    -- It consists of the rest of the current inner loop and the remaining
    -- iterations of the outer loop.
    --
    -- inner_stream has type @Sequence $(a_ty)@
    -- outer_index has type @int@
    -- leftover_domain has type @list_dim@
    -- leftover_inner_stream has typ @Sequence $(a_ty)@
    make_leftover_generate_bind_stream inner_stream
      outer_index leftover_domain leftover_inner_stream = do

      new_param <- newAnonymousVar ObjectLevel

      -- Adjust the index
      -- (\i ->
      --   case i of stored value_i.
      --   case boxed (stored (value_i + outer_index + 1)) of boxed i'.
      --   f i')
      inner_stream_exp <- do
        (inner_param, inner_body) <- freshenUnaryStreamFunction inner_stream
        i <- newAnonymousVar ObjectLevel
        value_i <- newAnonymousVar ObjectLevel       
        i' <- newAnonymousVar ObjectLevel

        -- Replace 'inner_param' by 'i'' in inner_body
        let inner_body' = rename (Rename.singleton inner_param i') inner_body

        -- Create expressions
        let add_expression =
              appE' (varE' $ coreBuiltin The_addI) []
              [ appE' (varE' $ coreBuiltin The_addI) []
                [varE' outer_index, varE' value_i]
              , ExpM (LitE defaultExpInfo (IntL 1 intT))
              ]
        let inner_stream_exp =
              CaseSE defaultExpInfo (varE' i)
              [AltS $ Alt stored_decon [PatS $ patM (value_i ::: intT)]
               (as_stored_int_stream add_expression i' inner_body')]
            adjusted_inner_stream =
              mkUnaryStreamFunction defaultExpInfo i stored_int_type
              a_ty inner_stream_exp

        return adjusted_inner_stream

      -- Build the stream
      let leftover_outer_stream =
            OpSE defaultExpInfo (GenerateBindOp a_ty) []
            [varE' leftover_domain] [inner_stream_exp] Nothing
      return $ OpSE defaultExpInfo (ChainOp a_ty) [a_repr] []
        [leftover_inner_stream, leftover_outer_stream] Nothing

    -- Convert an int to a stored int in an expression
    as_stored_int int_e int_var body_e =
      ExpM $ CaseE defaultExpInfo
      (conE' boxed_con [conE' stored_con [int_e]])
      [AltM $ Alt boxed_decon [patM (int_var ::: stored_int_type)] body_e]

    -- Convert an int to a stored int in a stream
    as_stored_int_stream int_e int_var body_s =
      CaseSE defaultExpInfo
      (conE' boxed_con [conE' stored_con [int_e]])
      [AltS $ Alt boxed_decon [PatS $ patM (int_var ::: stored_int_type)] body_s]

    stored_int_type = varApp (coreBuiltin The_Stored) [intT]
    list_dim_type = VarT (coreBuiltin The_list_dim)
    cont_type = writerType ret_ty

    stored_decon = VarDeCon (coreBuiltin The_stored) [intT] []
    boxed_decon = VarDeCon (coreBuiltin The_boxed) [stored_int_type] []
    stored_con = VarCon (coreBuiltin The_stored) [intT] []
    boxed_con = VarCon (coreBuiltin The_boxed) [stored_int_type] []


-- | Convert a fold over a sequence to a sequential loop.
--
--   The accumulator value has type @acc@.
--   The combining function has type @acc -> a -> Writer acc@.
--   The input stream has type @Sequence a@.
--   The returned expression has type @Writer acc@.
--
--   The type environment is only used to look up data constructors.
sequentializeFold :: Type       -- ^ Accumulator type
                  -> Type       -- ^ Stream contents type
                  -> Var        -- ^ Repr dictionary for accumulator
                  -> ExpM       -- ^ Repr dictionary for stream source
                  -> ExpM       -- ^ Accumulator value
                  -> ExpM       -- ^ Combining function
                  -> ExpS       -- ^ Input stream
                  -> MaybeT UnboxedTypeEvalM ExpM
sequentializeFold acc_ty a_ty acc_repr_var a_repr acc combiner source =
  case source
  of OpSE inf (GenerateOp _ gen_ty) _ [shape, f] [] Nothing -> do
       -- Create a @for@ loop
       tenv <- getTypeEnv
       mkVarAppE (coreBuiltin The_primitive_list_dim_fold)
         [acc_ty]
         [mkVarE acc_repr_var,
          return shape,
          lamE $ mkFun []
          (\ [] -> return ([stored_int_type, acc_ty, outType acc_ty],
                           initEffectType acc_ty))
          (\ [] [i_var, a_var, r_var] ->
            -- > let x = f i in combiner acc x ret
            localE gen_ty (appExp (return f) [] [mkVarE i_var]) $ \x_var ->
            return $ appE' combiner [] [varE' a_var, varE' x_var, varE' r_var]),
        return acc]

     OpSE inf (TraverseListOp ty) [repr] [l] [] Nothing -> do
       -- Create a fold over the list
       tenv <- getTypeEnv
       mkVarAppE (coreBuiltin The_llist_fold)
         [ty, acc_ty]
         [return repr,
          mkVarE acc_repr_var,
          lamE $ mkFun []
          (\ [] -> return ([ty, acc_ty, outType acc_ty],
                           initEffectType acc_ty))
          (\ [] [i_var, a_var, r_var] ->
            return $ appE' combiner [] [varE' a_var, varE' i_var, varE' r_var]),
          return acc,
          return l]

     -- Sequentialize 'map'
     OpSE inf (ZipOp _ [in_ty] zip_ty) [in_repr, _] [zip_f] [in_stream] Nothing -> do
       -- Apply the function to whatever 'in_stream' returns.
       map_combiner <-
         lamE $ mkFun []
         (\ [] -> return ([acc_ty, in_ty, outType acc_ty], initEffectType acc_ty))
         (\ [] [acc_var, in_var, r_var] ->
             localE zip_ty (appExp (return zip_f) [] [mkVarE in_var]) $ \x_var ->
             return $ appE' combiner [] [varE' acc_var, varE' x_var, varE' r_var])
       sequentializeFold acc_ty in_ty acc_repr_var in_repr acc map_combiner in_stream

     OpSE inf (ReturnOp ret_ty) _ [w] [] Nothing ->
       -- Accumulate the written value
       localE ret_ty (return w) $ \x_var ->
       return $ appE' combiner [] [acc, varE' x_var]

     OpSE inf (EmptyOp _ _) _ _ [] Nothing ->
       -- Return the accumulator
       mkVarAppE (coreBuiltin The_copy) [acc_ty] [mkVarE acc_repr_var, return acc]

     OpSE inf (ChainOp _) [_] [] [s1, s2] Nothing -> do
       -- Fold over the first stream, then over the second
       partial_result <-
         sequentializeFold acc_ty a_ty acc_repr_var a_repr acc combiner s1

       partial_result_var <- newAnonymousVar ObjectLevel
       let partial_result_exp = varE' partial_result_var
       final_result <-
         assume partial_result_var acc_ty $
         sequentializeFold acc_ty a_ty acc_repr_var a_repr partial_result_exp combiner s2

       -- Partial result goes into a temporary boxed object
       let boxed_result =
             conE' (VarCon (coreBuiltin The_boxed) [acc_ty] [])
             [partial_result]
           use_boxed_result =
             ExpM $ CaseE defaultExpInfo boxed_result
             [AltM $ Alt (VarDeCon (coreBuiltin The_boxed) [acc_ty] [])
              [patM (partial_result_var ::: acc_ty)]
              final_result]
       return use_boxed_result
       
     OpSE inf (BindOp p_ty _) [p_repr] [] [producer, transformer] Nothing -> do
       -- The "bind" operator is what makes sequentializing folds interesting.
       -- This transformation is performed:
       -- T [| bind s (\x. t) |] z c =
       --   T [| s |] z (\acc x r. T [| t |] acc c r)
       t_combiner <-
         sequentializeCombiningFunction acc_ty p_ty acc_repr_var p_repr combiner transformer

       sequentializeFold
         acc_ty a_ty acc_repr_var a_repr acc t_combiner producer

     OpSE inf (GenerateBindOp transformer_ty)
       [] [shp] [transformer] Nothing -> do
       -- Fused 'bind' and generate'
       -- Create a combiner from the transformer
       let stored_int_repr =
             ExpM $ VarE defaultExpInfo (coreBuiltin The_repr_int)
       t_combiner <-
         sequentializeCombiningFunction acc_ty stored_int_type
         acc_repr_var stored_int_repr combiner transformer

       -- Create a @for@ loop that uses the combiner
       tenv <- getTypeEnv
       mkVarAppE (coreBuiltin The_primitive_list_dim_fold)
         [acc_ty]
         [mkVarE acc_repr_var,
          return shp,
          lamE $ mkFun []
          (\ [] -> return ([stored_int_type, acc_ty, outType acc_ty],
                           initEffectType acc_ty))
          (\ [] [i_var, a_var, r_var] ->
            -- > t_combiner acc i ret
            return $ appE' t_combiner [] [varE' a_var, varE' i_var, varE' r_var]),
          return acc]

     OpSE {} -> internalError "sequentializeFold: Unsupported stream"
     
     LetSE inf pat rhs body -> do
       body' <- sequentializeFold acc_ty a_ty acc_repr_var a_repr acc
                combiner body
       return $ ExpM $ LetE inf pat rhs body'
     LetfunSE inf defs body -> do
       body' <- sequentializeFold acc_ty a_ty acc_repr_var a_repr acc
                combiner body
       return $ ExpM $ LetfunE inf defs body'
     CaseSE inf scr alts -> do
       alts' <- mapM (sequentializeFoldCaseAlternative
                      acc_ty a_ty acc_repr_var a_repr acc combiner) alts
       return $ ExpM $ CaseE inf scr alts'
     ExceptSE inf _ _ ->
       -- Raise an exception
       return $ ExpM $ ExceptE inf (writerType acc_ty)
     OtherSE _ -> mzero
     LamSE {} -> internalError "sequentializeFold: Unexpected lambda function"
  where
    stored_int_type = varApp (coreBuiltin The_Stored) [intT]

-- Turn a one-parameter stream function into a combining function for a fold.
--
-- Creates (\acc x r. T [| t |] acc c r)
sequentializeCombiningFunction :: Type -> Type -> Var -> ExpM -> ExpM -> ExpS
                               -> MaybeT UnboxedTypeEvalM ExpM
sequentializeCombiningFunction
    acc_ty arg_ty acc_repr_var arg_repr combiner transformer = do
  (t_value_var, t_stream) <- freshenUnaryStreamFunction transformer

  -- Create a function corresponding to the sequentialized transformer.
  -- This is a combining function for combining the producer's output
  -- with the accumulator.
  t_acc_var <- newAnonymousVar ObjectLevel
  let t_acc = ExpM $ VarE defaultExpInfo t_acc_var
  t_body <- sequentializeFold acc_ty arg_ty acc_repr_var arg_repr t_acc
            combiner t_stream

  let t_params = [patM (t_acc_var ::: acc_ty),
                  patM (t_value_var ::: arg_ty)]
      t_return = writerType acc_ty
  return $
    ExpM $ LamE defaultExpInfo $
    FunM $ Fun defaultExpInfo [] t_params t_return t_body

-- | Rename the parameter variable of a single-parameter stream function.
--   The renamed parameter and the body are returned.
freshenUnaryStreamFunction :: ExpS -> MaybeT UnboxedTypeEvalM (Var, ExpS)
freshenUnaryStreamFunction (LamSE _ (FunS (Fun _ [] [pat] _ body))) = do
  let v = patMVar $ fromPatS pat
  v' <- newClonedVar v
  return (v', Rename.rename (Rename.singleton v v') body)

freshenUnaryStreamFunction _ = mzero

-- | Construct a stream function that takes one parameter.
--
--   The return type should be an application of a stream type constructor.
mkUnaryStreamFunction :: ExpInfo -> Var -> Type -> Type -> ExpS -> ExpS
mkUnaryStreamFunction inf v param_ty return_stream_ty body =
  LamSE inf $
  FunS $ Fun inf [] [PatS $ patM (v ::: param_ty)] return_stream_ty body

-- | Rename variables bound by the outermost term of the expression.
--   Variables bound by 'ExpM' expressions (in an 'OtherSE' term) do not
--   get renamed.
freshenExpS expression =
  case expression
  of LetSE inf pat rhs body -> do
       (pat', rn) <- freshenPatM pat
       let body' = rename rn body
       return $ LetSE inf pat' rhs body'
     CaseSE inf scr alts -> do
       alts' <- mapM freshen_alt alts
       return $ CaseSE inf scr alts'
     ExceptSE {} -> return expression
     OpSE {} -> return expression
     OtherSE {} -> return expression
     LamSE {} ->
       -- If this is a stream-valued function,
       -- then 'freshenUnaryStreamFunction' should have been called
       internalError "freshenExpS: Unexpected function"
  where
    freshen_alt (AltS (Alt decon params body)) = do
      (decon', rn1) <- freshenDeConInst decon
      renamePatMs rn1 (map fromPatS params) $ \rn1' rn_params -> do
        (params', rn2) <- freshenPatMs rn_params
        let body' = rename (rn2 `Rename.compose` rn1') body
        return $ AltS $ Alt decon' (map PatS params') body'

sequentializeFoldCaseAlternative acc_ty a_ty acc_repr_var a_repr acc combiner
  (AltS (Alt decon params body)) = do
    body' <- sequentializeFold acc_ty a_ty acc_repr_var a_repr acc combiner body
    return $ AltM (Alt decon (map fromPatS params) body')