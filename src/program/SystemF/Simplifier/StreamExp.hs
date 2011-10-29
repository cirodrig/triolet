
module SystemF.Simplifier.StreamExp
       (isStreamAppExp,
        interpretStreamAppExp,
        simplifyStreamExp,
        embedStreamExp,
        pprExpS)
where

import Control.Monad
import qualified Data.IntMap as IntMap
import Data.Maybe
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import Common.Error
import Common.Identifier
import Common.PrecDoc
import Builtins.Builtins
import SystemF.Build
import SystemF.IncrementalSubstitution
import SystemF.Syntax
import SystemF.MemoryIR
import SystemF.PrintMemoryIR
import Type.Type
import Type.Environment

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
      -- | Shape arguments describing the run-time shape of streams.
    , sexpShapeArgs :: [ExpM]
      -- | Repr arguments describing the data types manipulated by this
      --   stream operation.
    , sexpReprArgs :: [ExpM]
      -- | Other non-stream arguments.
    , sexpMiscArgs :: [ExpM]
      -- | Stream arguments.
    , sexpStreamArgs :: [ExpS]
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
    -- | Recursive definition group
  | LetfunSE
    { sexpInfo :: ExpInfo
    , sexpDefs :: DefGroup (Def Mem)
    , sexpBody :: ExpS
    }
    -- | Case analysis 
  | CaseSE
    { sexpInfo :: ExpInfo
    , sexpScrutinee :: ExpM
    , sexpAlternatives :: [AltS]
    }

data PolyStreamType =
    PolySequenceType
  | PolyViewType {-# UNPACK #-}!Int
  | PolyDArrType {-# UNPACK #-}!Int

data StreamType =
    -- | 1D sequence type
    SequenceType

    -- | N-dimensional view type
  | ViewType {-#UNPACK#-} !Int

    -- | N-dimensional delayed array type.
    --   The arguments are the size indices in each dimension.
  | DArrType [Type]

-- | Apply the given shape indices to the shape-polymorphic stream type to get
--   a shape-monomorphic stream type.
applyShapeIndices :: [Type] -> PolyStreamType -> StreamType
applyShapeIndices ts pst =
  case (pst, ts)
  of (PolySequenceType, []) -> SequenceType
     (PolyViewType n, []) -> ViewType n
     (PolyDArrType n, ts) | n == length ts -> DArrType ts
     _ -> internalError "applyShape: Argument length mismatch"

-- | Get the shape indices from a 'StreamType'.  The shape indices are the
--   types that were passed to 'applyShapeIndices' to create the 'StreamType'.
extractShapeIndices :: StreamType -> [Type]
extractShapeIndices SequenceType = []
extractShapeIndices (ViewType _) = []
extractShapeIndices (DArrType xs) = xs

streamShapeType, streamIndexType :: StreamType -> Type

-- | Return the shape type of the stream, the same type that would be returned
--   by 'shape'.
streamShapeType st =
  case st
  of SequenceType -> dim1
     ViewType 0 -> dim0
     ViewType 1 -> dim1
  where
    dim0 = VarT $ pyonBuiltin The_dim0
    dim1 = VarT $ pyonBuiltin The_dim1

-- | Return the shape type of the stream, the same type that would be returned
--   by 'index'.
streamIndexType st =
  case st
  of SequenceType -> ix1
     ViewType 0 -> ix0
     ViewType 1 -> ix1
  where
    ix0 = varApp (pyonBuiltin The_Stored) [VarT $ pyonBuiltin The_NoneType]
    ix1 = varApp (pyonBuiltin The_Stored) [VarT $ pyonBuiltin The_int]

data ReductionOp =
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

    -- | Reduce sequentially
    --
    -- > (reduce @{other type arguments} @{input type} @{accumulator  type}
    -- >   {other arguments}) {reducer} {init} {stream} {output pointer}
  | Fold Type Type

data StreamOp =
    -- | Generate a stream.
    --
    -- > generate @{shape indices} @{output type}
    -- >   {shape parameters} {output repr} {generator function}
    GenerateOp !StreamType Type

    -- | N-ary zip over streams using a transformer function to combine values.
    --   When N=1, the operation is 'map'.
    --
    -- > zipWith @{shape indices} @{input types} @{output type}
    -- >   {shape parameters} {input reprs} {output repr}
    -- >   {transformer function} {input streams}
  | ZipOp !StreamType [Type] Type

    -- | Convert a stream to a 1D sequence.
    --
    -- > flatten @{shape indices} @{input type} @{input stream}
  | ToSequenceOp !StreamType Type

    -- | Convert a stream to a 1D view.
    --
    -- > flatten @{shape indices} @{input type} @{input stream}
  | ToView1Op !StreamType Type

    -- | Produce a 1D sequence of size 1. 
  | ReturnOp !Type

    -- | Produce a 1D sequence of size 0.
  | EmptyOp !Type

    -- | The bind operation on sequences
  | BindOp !Type !Type

    -- | Reduce a stream and produce a single value.
    --
    -- > reduce @{shape indices} @{reduction type parameters}
    -- >   {shape parameters} {repr} {reduction parameters}
  | ReduceOp !StreamType !ReductionOp

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
pprStreamType (ViewType n) = text "view" <> int n `hasPrec` atomicPrec
pprStreamType (DArrType ts) =
  let op = text "darr" <> int (length ts) `hasPrec` atomicPrec
  in asApplication (op : map pprTypePrec ts)

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

pprStreamOp' (ReturnOp t) =
  nameApplication "return" [pprTypePrec t]

pprExpSPrec :: ExpS -> PrecDoc  
pprExpSPrec expression = 
  case expression
  of OtherSE e -> pprExpPrec e
     OpSE _ op shape_args repr_args misc_args stream_args ->
       let arg_group xs = braces (sep $ map pprExp xs) `hasPrec` atomicPrec
       in asApplication $ pprStreamOp' op ++
                          arg_group shape_args :
                          arg_group repr_args :
                          arg_group misc_args :
                          map pprExpSPrec stream_args
     LamSE _ f ->
       pprFunS f
     LetSE _ pat rhs body ->
       hang (text "let" <+> pprPat pat <+> text "=") 6 (pprExp rhs) $$
       pprExpS body `hasPrec` stmtPrec
     CaseSE _ scr alts ->
       text "case" <+> pprExp scr $$
       text "of" <+> vcat (map pprAltS alts) `hasPrec` stmtPrec

pprAltS :: AltS -> Doc
pprAltS (AltS (Alt decon params body)) =
  hang (pprPatternMatch (AltM (Alt decon (map fromPatS params) undefined)) <> text ".") 2
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

numShapeIndices pst =
  case pst
  of PolySequenceType -> 0
     PolyViewType _ -> 0
     PolyDArrType n -> n

takeShapeIndices :: PolyStreamType -> [Type] -> Maybe ([Type], [Type])
takeShapeIndices pst tys = breakAt (numShapeIndices pst) tys

takeShapeArguments :: PolyStreamType -> [ExpM] -> Maybe ([ExpM], [ExpM])
takeShapeArguments pst tys = breakAt (numShapeIndices pst) tys

data StreamOpInterpreter =
  StreamOpInterpreter
  { checkArity :: !(Int -> Int -> Bool)
  , interpretOp :: !(ExpInfo -> [Type] -> [ExpM] -> TypeEvalM ExpS)
  }

streamOpTable :: IntMap.IntMap StreamOpInterpreter
streamOpTable =
  IntMap.fromList [(fromIdent $ varID v, f) | (v, f) <- list]
  where
    list = [ (pyonBuiltin The_view1_generate, interpretGen (PolyViewType 1))
           , (pyonBuiltin The_view1_map, interpretZip (PolyViewType 1) 1)
           , (pyonBuiltin The_view1_zipWith, interpretZip (PolyViewType 1) 2)
           , (pyonBuiltin The_view1_zipWith3, interpretZip (PolyViewType 1) 3)
           , (pyonBuiltin The_view1_zipWith4, interpretZip (PolyViewType 1) 4)
           , (pyonBuiltin The_Sequence_bind, interpretBind)
           , (pyonBuiltin The_Sequence_return, interpretReturn)
           , (pyonBuiltin The_Sequence_generate, interpretGen PolySequenceType)
           , (pyonBuiltin The_viewToSequence, interpretToSequence (PolyViewType 1))
           ]

interpretGen stream_type = StreamOpInterpreter check_arity interpret
  where
    check_arity ty_args args = ty_args == n_ty_args && args == n_args

    interpret inf ty_args args = do
      let Just (shape_indices, ty_args') = takeShapeIndices stream_type ty_args
          Just (shape_args, args') = takeShapeArguments stream_type args
          [output_type] = ty_args'
          [repr, shape, generator] = args'
          op = GenerateOp (applyShapeIndices shape_indices stream_type)
               output_type
      return $ OpSE inf op shape_args [repr] [shape, generator] []

    n_shape_indices = numShapeIndices stream_type
    n_ty_args = n_shape_indices + 1
    n_args = n_shape_indices + 3
       
interpretZip stream_type n_inputs = StreamOpInterpreter check_arity interpret 
  where
    check_arity ty_args args = ty_args == n_ty_args && args == n_args
    
    interpret inf ty_args args = do
      let Just (shape_indices, ty_args') = takeShapeIndices stream_type ty_args
          Just (shape_args, args') = takeShapeArguments stream_type args
          Just (repr_args, transformer : inputs) = breakAt (1 + n_inputs) args
          input_types = init ty_args'
          output_type = last ty_args'
          op = ZipOp  (applyShapeIndices shape_indices stream_type)
               input_types output_type

      stream_exps <- mapM interpretStreamSubExp inputs
      return $ OpSE inf op shape_args repr_args [transformer] stream_exps

    n_shape_indices = numShapeIndices stream_type
    n_ty_args = n_shape_indices + n_inputs + 1
    n_args = n_shape_indices + 2 * n_inputs + 2

interpretBind = StreamOpInterpreter check_arity interpret
  where
    check_arity 2 3 = True
    check_arity _ _ = False
    
    interpret inf [t1, t2] [repr, producer, transformer] = do
      producer' <- interpretStreamSubExp producer
      transformer' <- interpretStreamSubExp transformer
      return $ OpSE inf (BindOp t1 t2) [] [repr] [] [producer', transformer']

interpretReturn = StreamOpInterpreter check_arity interpret
  where
    check_arity 1 2 = True
    check_arity _ _ = False
    
    interpret inf [ty] [repr, gen] = do
      return $ OpSE inf (ReturnOp ty) [] [repr] [gen] []

interpretToSequence stream_type = StreamOpInterpreter check_arity interpret
  where
    check_arity ty_args args =
      ty_args == 1 + n_shape_indices && args == 2 + n_shape_indices
    
    interpret inf ty_args args = do
      let Just (shape_indices, [ty]) = takeShapeIndices stream_type ty_args
          Just (shape_args, [repr, src]) = takeShapeArguments stream_type args
          op = ToSequenceOp (applyShapeIndices shape_indices stream_type) ty
      src_stream <- interpretStreamSubExp src
      return $ OpSE inf op shape_args [repr] [] [src_stream]

    n_shape_indices = numShapeIndices stream_type

interpretStreamSubExp :: ExpM -> TypeEvalM ExpS
interpretStreamSubExp expression =
  case fromExpM expression of
    AppE inf (ExpM (VarE _ op_var)) ty_args args ->
      interpret_app inf op_var ty_args args
    AppE {} ->
      embed_expression
    VarE inf op_var -> interpret_app inf op_var [] []
    LamE inf f -> do
      liftM (LamSE inf) $ interpretStreamFun f
    LetE inf pat rhs body -> do
      body' <- assumePatM pat $ interpretStreamSubExp body
      return $ LetSE inf pat rhs body'
    CaseE inf scr alts -> do
      alts' <- mapM interpretStreamAlt alts
      return $ CaseSE inf scr alts'
    _ -> embed_expression
  where
    embed_expression = return $ OtherSE expression

    interpret_app inf op_var ty_args args
      | Just interpreter <-
          IntMap.lookup (fromIdent $ varID op_var) streamOpTable,
        checkArity interpreter (length ty_args) (length args) =
          interpretOp interpreter inf ty_args args
      | otherwise = embed_expression

interpretStreamFun :: FunM -> TypeEvalM FunS
interpretStreamFun (FunM fun) =
  assumeTyPats (funTyParams fun) $
  assumePatMs (funParams fun) $ do
    body <- interpretStreamSubExp $ funBody fun
    return $ FunS $ Fun { funInfo = funInfo fun
                        , funTyParams = funTyParams fun
                        , funParams = map PatS $ funParams fun
                        , funReturn = funReturn fun
                        , funBody = body }

interpretStreamAlt :: AltM -> TypeEvalM AltS
interpretStreamAlt (AltM alt) =
  assumeBinders (deConExTypes $ altCon alt) $
  assumePatMs (altParams alt) $ do
    body <- interpretStreamSubExp $ altBody alt
    return $ AltS $ Alt (altCon alt) (map PatS $ altParams alt) body

-- | Interpret a stream expression that is a function application.
--   If the expression can't be interpeted as a stream, return Nothing.
interpretStreamAppExp :: ExpInfo -> Var -> [Type] -> [ExpM]
                      -> TypeEvalM (Maybe ExpS)
interpretStreamAppExp inf op ty_args args =
  case IntMap.lookup (fromIdent $ varID op) streamOpTable 
  of Just interpreter | checkArity interpreter (length ty_args) (length args) ->
       liftM Just $ interpretOp interpreter inf ty_args args
     _ -> return Nothing

-- | Interpret a stream expression that is a function application.
--   If the expression can't be interpeted as a stream, return Nothing.
isStreamAppExp :: Var -> [Type] -> [ExpSM] -> Bool
isStreamAppExp op_var tys args =
  case IntMap.lookup (fromIdent $ varID op_var) streamOpTable
  of Nothing -> False
     Just interpreter -> checkArity interpreter (length tys) (length args)

-------------------------------------------------------------------------------
-- Convert a stream expression to a System F expression

-- | Convert a stream operator to a function and set of type parameters
embedOp :: StreamOp -> (Var, [Type])
embedOp (GenerateOp stream_type output_type) = let
  op = case stream_type
       of SequenceType -> pyonBuiltin The_Sequence_generate
          ViewType 1 -> pyonBuiltin The_view1_generate
  in (op, extractShapeIndices stream_type ++ [output_type])

embedOp (ZipOp stream_type input_types output_type) = let
  n_input_types = length input_types
  op = case stream_type
       of SequenceType ->
            case n_input_types
            of 1 -> pyonBuiltin The_Sequence_map
               2 -> pyonBuiltin The_Sequence_zipWith
               3 -> pyonBuiltin The_Sequence_zipWith3
               4 -> pyonBuiltin The_Sequence_zipWith4
          ViewType 1 ->
            case n_input_types
            of 1 -> pyonBuiltin The_view1_map
               2 -> pyonBuiltin The_view1_zipWith
               3 -> pyonBuiltin The_view1_zipWith3
               4 -> pyonBuiltin The_view1_zipWith4
          {-ViewType 2 ->
            case n_input_types
            of 1 -> pyonBuiltin The_view2_map
               2 -> pyonBuiltin The_view2_zipWith
               3 -> pyonBuiltin The_view2_zipWith3
               4 -> pyonBuiltin The_view2_zipWith4
          DArrType [_] ->
            case n_input_types
            of 1 -> pyonBuiltin The_darr1_map
               2 -> pyonBuiltin The_darr1_zipWith
               3 -> pyonBuiltin The_darr1_zipWith3
               4 -> pyonBuiltin The_darr1_zipWith4
          DArrType [_, _] ->
            case n_input_types
            of 1 -> pyonBuiltin The_darr2_map
               2 -> pyonBuiltin The_darr2_zipWith
               3 -> pyonBuiltin The_darr2_zipWith3
               4 -> pyonBuiltin The_darr2_zipWith4-}
  in (op, extractShapeIndices stream_type ++ input_types ++ [output_type])

embedOp (ToSequenceOp st ty) =
  let op = case st
           of ViewType 1 -> pyonBuiltin The_viewToSequence
  in (op, extractShapeIndices st ++ [ty])

embedOp (ToView1Op st ty) =
  let op = case st
           of ViewType 1 -> pyonBuiltin The_sequenceToView
  in (op, extractShapeIndices st ++ [ty])

embedOp (BindOp t1 t2) =
  (pyonBuiltin The_Sequence_bind, [t1, t2])

embedStreamExp :: ExpS -> ExpM
embedStreamExp expression =
  case expression
  of OpSE inf op shape_args reprs misc_args streams ->
       let (op_var, ty_args) = embedOp op
           stream_args = map embedStreamExp streams
       in appE inf (ExpM $ VarE inf op_var) ty_args
          (shape_args ++ reprs ++ misc_args ++ stream_args)
     OtherSE e -> e
     LamSE inf f -> 
       ExpM $ LamE inf (embedStreamFun f)
     LetSE inf b rhs body ->
       ExpM $ LetE inf b rhs (embedStreamExp body)
     CaseSE inf scr alts ->
       ExpM $ CaseE inf scr (map embedStreamAlt alts)

embedStreamFun (FunS f) =
  FunM $ Fun (funInfo f) (funTyParams f) (map fromPatS $ funParams f)
             (funReturn f) (embedStreamExp $ funBody f)

embedStreamAlt (AltS alt) =
  AltM $ Alt (altCon alt) (map fromPatS $ altParams alt)
             (embedStreamExp $ altBody alt)

-------------------------------------------------------------------------------

simplifyStreamExp :: ExpS -> TypeEvalM ExpS
simplifyStreamExp expression = traceShow (text "sse" <+> pprExpS expression) $ 
  case expression
  of -- Map operation: try to fuse with its producer
     OpSE inf op@(ZipOp st [in_type] out_type)
       shape_args repr_args@[in_repr, out_repr] [f] [in_stream] -> do
       e <- fuseMapWithProducer out_type out_repr f in_stream
       case e of
         Just e' -> simplifyStreamExp e'
         Nothing -> simplify_subexpressions expression

     -- Convert to sequence: Try to replace the source stream with the
     -- equivalent sequence stream
     OpSE inf op@(ToSequenceOp st ty) shape_args [repr] [] [s] -> do
       e <- convertToSequenceOp s
       case e of
         Just e' -> simplifyStreamExp e'
         Nothing -> simplify_subexpressions expression

     _ -> simplify_subexpressions expression
  where
    simplify_subexpressions e =
      case e
      of OpSE inf op shape_args repr_args misc_args stream_args -> do
           stream_args' <- mapM simplifyStreamExp stream_args
           return $ OpSE inf op shape_args repr_args misc_args stream_args'
         LamSE inf f ->
           LamSE inf `liftM` simplifyStreamFun f
         CaseSE inf scr alts ->
           CaseSE inf scr `liftM` mapM simplifyStreamAlt alts
         _ -> return expression

simplifyStreamAlt (AltS alt) =
  assumeBinders (deConExTypes $ altCon alt) $
  assumePatMs (map fromPatS $ altParams alt) $ do
    body <- simplifyStreamExp $ altBody alt
    return $ AltS $ alt {altBody = body}

simplifyStreamFun (FunS fun) =
  assumeTyPats (funTyParams fun) $
  assumePatMs (map fromPatS $ funParams fun) $ do
    body <- simplifyStreamExp $ funBody fun
    return $ FunS $ fun {funBody = body}

fuseMapWithProducer :: Type -> ExpM -> ExpM -> ExpS -> TypeEvalM (Maybe ExpS)
fuseMapWithProducer ty repr map_f producer = trace "fuseMapWithProducer" $ 
  case producer
  of OpSE inf (GenerateOp st producer_ty)
       shape_args [producer_repr] [dim, gen_f] [] -> do
       new_gen_f <- fuse_with_generator [streamIndexType st] producer_ty gen_f

       return $ Just $ OpSE inf (GenerateOp st ty) shape_args [repr] [dim, new_gen_f] []
     OpSE inf (ZipOp st zip_tys producer_ty)
       shape_args zip_and_producer_reprs [zip_f] zip_streams -> do
       new_zip_f <- fuse_with_generator zip_tys producer_ty zip_f
       let zip_reprs = init zip_and_producer_reprs

       return $ Just $ OpSE inf (ZipOp st zip_tys ty) shape_args (zip_reprs ++ [repr]) [new_zip_f] zip_streams
     _ -> return Nothing
  where
    -- Fuse with generator function
    -- > \ ARGS r. case boxed (gen_f ARGS) of boxed x. map_f x r
    fuse_with_generator arg_types producer_ty gen_f =
      lamE $
      mkFun []
      (\ [] -> return (arg_types ++ [outType producer_ty],
                       initEffectType producer_ty))
      (\ [] args ->
        let arg_value_vars = init args
            out_ptr = last args
        in localE producer_ty
           (appExp (return gen_f) [] (map varE arg_value_vars)) $ \x ->
           appExp (return map_f) [] [varE x, varE out_ptr])

-- | Convert a stream operation to an equivalent sequence operation, if
--   possible.
convertToSequenceOp :: ExpS -> TypeEvalM (Maybe ExpS)
convertToSequenceOp expression =
  case expression
  of OpSE inf (GenerateOp st ty) _ repr_args misc_args [] ->
       case st
       of ViewType 1 ->
            -- Convert view1_generate to Sequence_Generate
            return $ Just $
            OpSE inf (GenerateOp SequenceType ty) [] repr_args misc_args []
          _ -> return Nothing
     _ -> return Nothing