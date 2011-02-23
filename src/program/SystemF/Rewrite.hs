
module SystemF.Rewrite
       (rewriteApp)
where

import Control.Monad
import qualified Data.Map as Map
import Data.Maybe
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import Common.Error
import Common.MonadLogic
import Builtins.Builtins
import SystemF.Build
import SystemF.Syntax
import SystemF.MemoryIR
import SystemF.PrintMemoryIR
import Type.Environment
import Type.Eval
import Type.Type

-------------------------------------------------------------------------------
-- Helper functions for writing code

-- | Create a case expression to inspect a list.
--
-- > case scrutinee
-- > of make_list list_type (n : intindex)
-- >                        (sz : IndexedInt n) 
-- >                        (p : Referenced (array n list_type)).
-- >      case p
-- >      of referenced ay. $(make_body n sz ay)
caseOfList :: TypeEnv
           -> MkExpM            -- ^ List to inspect
           -> TypM              -- ^ Type of list element
           -> (Var -> Var -> Var -> MkExpM)
              -- ^ Function from (list size index, list size, array reference)
              --   to expression
           -> MkExpM
caseOfList tenv scrutinee list_type mk_body =
  caseE scrutinee
  [mkAlt tenv (pyonBuiltin the_make_list) [list_type] $
   \ [size_index] [size, array_ref] ->
   caseE (varE array_ref)
   [mkAlt tenv (pyonBuiltin the_referenced) [array_type size_index] $
    \ [] [ay] -> mk_body size_index size ay]]
  where
    -- Create the type (array n list_type)
    array_type size_index =
      TypM $ varApp (pyonBuiltin the_array) [VarT size_index, fromTypM list_type]

caseOfTraversableDict :: TypeEnv
                      -> MkExpM
                      -> TypM
                      -> (Var -> Var -> MkExpM)
                      -> MkExpM
caseOfTraversableDict tenv scrutinee container_type mk_body =
  caseE scrutinee
  [mkAlt tenv (pyonBuiltin the_traversableDict) [container_type] $
   \ [] [trv, bld] -> mk_body trv bld]

caseOfSomeIndexedInt :: TypeEnv
                     -> MkExpM
                     -> (Var -> Var -> MkExpM)
                     -> MkExpM
caseOfSomeIndexedInt tenv scrutinee mk_body =
  caseE scrutinee
  [mkAlt tenv (pyonBuiltin the_someIndexedInt) [] $
   \ [intindex] [intvalue] -> mk_body intindex intvalue]

defineAndInspectIndexedInt tenv int_value mk_body =
  let define_indexed_int =
        varAppE (pyonBuiltin the_defineIntIndex) [] [int_value]
  in caseOfSomeIndexedInt tenv define_indexed_int mk_body

intType = VarT (pyonBuiltin the_int)

-------------------------------------------------------------------------------
-- Rewrite rules

-- Given the arguments to an application, try to create a rewritten term
type RewriteRule = TypeEnv -> ExpInfo -> [TypM] -> [ExpM]
                -> FreshVarM (Maybe ExpM)

rewriteRules :: Map.Map Var RewriteRule
rewriteRules = Map.fromList table
  where
    table = [ (pyonBuiltin the_range, rwRange)
            , (pyonBuiltin the_TraversableDict_list_traverse, rwTraverseList)
            , (pyonBuiltin the_TraversableDict_list_build, rwBuildList)
            , (pyonBuiltin the_fun_map, rwMap)
            , (pyonBuiltin the_fun_zip, rwZip)
            , (pyonBuiltin the_fun_zip3, rwZip3)
            , (pyonBuiltin the_fun_zip4, rwZip4)
            , (pyonBuiltin the_fun_map_Stream, rwMapStream)
            , (pyonBuiltin the_fun_zip_Stream, rwZipStream) 
            , (pyonBuiltin the_fun_zip3_Stream, rwZip3Stream)
            , (pyonBuiltin the_fun_zip4_Stream, rwZip4Stream)
            {- Rewrites temporarily disabled while we change Stream types
            , (pyonBuiltin the_oper_CAT_MAP, rwBindStream) -}
            , (pyonBuiltin the_histogram, rwHistogram)
            , (pyonBuiltin the_fun_reduce, rwReduce)
            , (pyonBuiltin the_fun_reduce_Stream, rwReduceStream)
            , (pyonBuiltin the_fun_reduce1, rwReduce1)
            , (pyonBuiltin the_fun_reduce1_Stream, rwReduce1Stream)
            ]

-- | Attempt to rewrite an application term.
--   If it can be rewritten, return the new expression.
rewriteApp :: TypeEnv -> ExpInfo -> Var -> [TypM] -> [ExpM]
           -> FreshVarM (Maybe ExpM)
rewriteApp tenv inf op_var ty_args args =
  case Map.lookup op_var rewriteRules
  of Just rw -> trace_rewrite $ rw tenv inf ty_args args
     Nothing -> return Nothing
  where
    trace_rewrite m = do 
      x <- m
      case x of
        Nothing -> return x
        Just e' -> traceShow (text "rewrite" <+> old_exp $$ text "    -->" <+> pprExp e') $ return x
    
    old_exp = pprExp (ExpM $ AppE defaultExpInfo (ExpM (VarE defaultExpInfo op_var)) ty_args args)

-- | Convert 'range' into an explicitly indexed variant
rwRange :: RewriteRule
rwRange tenv inf [] [count] =
  fmap Just $
  defineAndInspectIndexedInt tenv (return count)
  (\intindex intvalue ->
    varAppE (pyonBuiltin the_fun_asList_Stream)
    [TypM $ varApp (pyonBuiltin the_array) [VarT intindex], TypM intType]
    [varAppE (pyonBuiltin the_rangeIndexed) [TypM $ VarT intindex] [varE intvalue]])

rwRange _ _ _ _ = return Nothing

rwTraverseList :: RewriteRule
rwTraverseList tenv inf [elt_type] [elt_repr, list] = fmap Just $
  caseOfList tenv (return list) elt_type $ \size_index size_var array ->
    varAppE (pyonBuiltin the_fun_asList_Stream) 
    [TypM $ varApp (pyonBuiltin the_array) [VarT size_index], elt_type]
    [varAppE (pyonBuiltin the_generate)
     [TypM (VarT size_index), elt_type]
     [varE size_var,
      return elt_repr,
      lamE $ mkFun []
      (\ [] -> return ([ValPT Nothing ::: intType,
                        OutPT ::: fromTypM elt_type],
                       SideEffectRT ::: fromTypM elt_type))
      (\ [] [index_var, ret_var] ->
          varAppE (pyonBuiltin the_copy)
          [elt_type]
          [return elt_repr,
           varAppE (pyonBuiltin the_subscript)
           [TypM (VarT size_index), elt_type]
           [return elt_repr, varE array, varE index_var],
           varE ret_var])]]
  
rwTraverseList _ _ _ _ = return Nothing

rwBuildList :: RewriteRule
rwBuildList tenv inf [elt_type] (elt_repr : stream : other_args)
  | Just shape <- interpretStream elt_repr stream =
    case sShape shape
    of Array1DShape size_arg size_val ->
         fmap Just $
         buildListDoall inf elt_type elt_repr other_args size_arg size_val (sGenerator shape)
       _ -> return Nothing

rwBuildList _ _ _ _ = return Nothing

buildListDoall inf elt_type elt_repr other_args size count generator =
  let array_type = varApp (pyonBuiltin the_array) [fromTypM size, fromTypM elt_type]
  in varAppE (pyonBuiltin the_make_list)
     [elt_type, size]
     ([return count,
       varAppE (pyonBuiltin the_referenced) [TypM array_type]
       [lamE $ mkFun []
        (\ [] -> return ([OutPT ::: array_type], SideEffectRT ::: array_type))
        (\ [] [out_ptr] ->
          varAppE (pyonBuiltin the_doall)
          [size, TypM array_type, elt_type]
          [return count,
           lamE $ mkFun []
           (\ [] -> return ([ValPT Nothing ::: intType],
                            SideEffectRT ::: fromTypM elt_type))
           (\ [] [index_var] ->
             appE (generator (ExpM $ VarE defaultExpInfo index_var)) []
             [varAppE (pyonBuiltin the_subscript_out) [size, elt_type]
              [return elt_repr, varE out_ptr, varE index_var]])])]] ++
      map return other_args)


{- Disabled while we change types

-- | Rewrite applications of the stream @bind@ operator when the producer
--   or transformer has a well-behaved data flow pattern.
--
--   * Transformer is rewritable to @\x -> return f(x)@: rewrite to a
--     mapStream
rwBindStream :: RewriteRule
rwBindStream tenv inf
  [elt1, elt2]
  [repr1, repr2, producer, transformer] =
  case unreturnStreamTransformer transformer
  of Just map_fn ->
       fmap Just $
       varAppE (pyonBuiltin the_fun_map_Stream)
       [TypM (VarT $ pyonBuiltin the_list), elt1, elt2]
       [return repr1, return repr2, return map_fn, return producer]
     _ -> return Nothing

rwBindStream _ _ _ _ = return Nothing

-}

rwMap :: RewriteRule
rwMap tenv inf
  [container, element1, element2]
  (traversable : repr1 : repr2 :
   transformer : input : other_args) =
  fmap Just $
  caseOfTraversableDict tenv (return traversable) container $ \trv bld ->
  varAppE bld [element2]
  (return repr2 :
   varAppE (pyonBuiltin the_fun_map_Stream)
   [container, element1, element2]
   [return repr1,
    return repr2,
    return transformer,
    varAppE trv [element1] [return repr1, return input]] :
   map return other_args)

rwMap _ _ _ _ = return Nothing

-- | Rewrite calls to @zip@ to call @zipStream@
--
-- > case t1 of TraversableDict trv1 _.
-- > case t2 of TraversableDict trv2 _.
-- > case t3 of TraversableDict _ bld3.
-- > bld3
-- >   (PyonTuple2 element1 element2)
-- >   (repr_PyonTuple2 element1 element2 repr1 repr2)
-- >   (zipStream element1 element2 repr1 repr2
-- >     (trv1 element1 repr1 input1)
-- >     (trv2 element2 repr2 input2))
rwZip :: RewriteRule
rwZip tenv inf
  [container, element1, element2]
  (traversable : repr1 : repr2 :
   input1 : input2 : other_args) =
  let zip_args = [ZipArg element1 repr1 input1,
                  ZipArg element2 repr2 input2]
  in fmap Just $
     generalizedRewriteZip tenv inf zip_args container traversable other_args

rwZip _ _ _ _ = return Nothing

rwZip3 :: RewriteRule
rwZip3 tenv inf
  [container, element1, element2, element3]
  (traversable : repr1 : repr2 : repr3 :
   input1 : input2 : input3 : other_args) =
  let zip_args = [ZipArg element1 repr1 input1,
                  ZipArg element2 repr2 input2,
                  ZipArg element3 repr3 input3]
  in fmap Just $
     generalizedRewriteZip tenv inf zip_args container traversable other_args

rwZip3 _ _ _ _ = return Nothing

rwZip4 :: RewriteRule
rwZip4 tenv inf
  [container, element1, element2, element3, element4]
  (traversable : repr1 : repr2 : repr3 : repr4 :
   input1 : input2 : input3 : input4 : other_args) =
  let zip_args = [ZipArg element1 repr1 input1,
                  ZipArg element2 repr2 input2,
                  ZipArg element3 repr3 input3,
                  ZipArg element4 repr4 input4]
  in fmap Just $
     generalizedRewriteZip tenv inf zip_args container traversable other_args

rwZip4 _ _ _ _ = return Nothing

rwMapStream :: RewriteRule
rwMapStream tenv inf
  [shape_type, elt1, elt2]
  [repr1, repr2, transformer, producer]
  | Just shape <- interpretStream repr1 producer =
    let new_shape =
          -- Fuse the transformer into the generator expression
          InterpretedStream
          { sShape = sShape shape
          , sType = fromTypM elt2
          , sRepr = repr2
          , sGenerator = \ix ->
              -- The generator takes an output pointer as a parameter
              lamE $ mkFun []
              (\ [] -> return ([OutPT ::: fromTypM elt2],
                               SideEffectRT ::: fromTypM elt2))
              (\ [] [outvar] -> do
                  tmpvar <- newAnonymousVar ObjectLevel
                  -- Compute the input to 'map'
                  rhs <- appE (sGenerator shape ix) [] [varE tmpvar]
                  -- Compute the output of 'map'
                  body <- appE (return transformer) [] [varE tmpvar, varE outvar]
                  let binder = localVarP tmpvar (fromTypM elt1) repr1
                      let_expr = ExpM $ LetE inf binder rhs body
                  return let_expr)}
    in encodeStream shape_type new_shape 

rwMapStream _ _ _ _ = return Nothing

-- | Rewrite calls to @zipStream@ when we know the size of the stream.
--
-- > zipStream(count, generate(n, f)) -> generate(n, \i -> (i, f i))
-- > zipStream(generate(n, f), count) -> generate(n, \i -> (f i, i))
-- > zipStream(generate(n1, f1), generate(n2, f2)) ->
--     generate(min(n1, n2), \i -> (f1 i, f2 i))
rwZipStream :: RewriteRule
rwZipStream tenv inf
  [shape_type, element1, element2]
  [repr1, repr2, stream1, stream2]
  | Just shape1 <- interpretStream repr1 stream1,
    Just shape2 <- interpretStream repr2 stream2 =
      generalizedZipStream shape_type [shape1, shape2]

rwZipStream _ _ _ _ = return Nothing

rwZip3Stream :: RewriteRule
rwZip3Stream tenv inf
  [shape_type, element1, element2, element3]
  [repr1, repr2, repr3, stream1, stream2, stream3]
  | Just shape1 <- interpretStream repr1 stream1,
    Just shape2 <- interpretStream repr2 stream2,
    Just shape3 <- interpretStream repr3 stream3 =
      generalizedZipStream shape_type [shape1, shape2, shape3]

rwZip3Stream _ _ _ _ = return Nothing

rwZip4Stream :: RewriteRule
rwZip4Stream tenv inf
  [shape_type, element1, element2, element3, element4]
  [repr1, repr2, repr3, repr4, stream1, stream2, stream3, stream4]
  | Just shape1 <- interpretStream repr1 stream1,
    Just shape2 <- interpretStream repr2 stream2,
    Just shape3 <- interpretStream repr3 stream3,
    Just shape4 <- interpretStream repr4 stream4 =
      generalizedZipStream shape_type [shape1, shape2, shape3, shape4]

rwZip4Stream _ _ _ _ = return Nothing

generalizedZipStream shape_type streams =
  let zipped_stream = zipStreams streams -- Zip the streams
      zipped_shape = shapeType $ sShape zipped_stream
      elem_ty = sType zipped_stream
      tuple_repr = sRepr zipped_stream
  in case sShape zipped_stream
     of UnboundedShape -> return Nothing -- Can't deal with infinite streams
        UnknownShape _ -> return Nothing -- Don't cross the streams
        Array1DShape shp_ty shp_val -> do
          -- Generate code for a zipped loop
          zip_expr <-
            varAppE (pyonBuiltin the_generate)
            [shp_ty, TypM elem_ty]
            [return shp_val,
             return tuple_repr,
             lamE $ mkFun []
             (\ [] -> return ([ValPT Nothing ::: intType],
                              BoxRT ::: FunT (OutPT ::: elem_ty)
                              (SideEffectRT ::: elem_ty)))
             (\ [] [ixvar] ->
               sGenerator zipped_stream $ ExpM (VarE defaultExpInfo ixvar))]

          -- Cast the stream shape to the expected type
          return $ castStreamExpressionShape (fromTypM shape_type) zipped_shape elem_ty tuple_repr zip_expr

-- | Turn a list-building histogram into an array-building histogram
--
-- > rwHistogram t size input
--
-- becomes
--
-- > case (defineIntIndex size)
-- > of SomeIntIndex n index.
-- >      make_list int n index
-- >        (referenced (array n int) (histogramArray t n index input)))
rwHistogram :: RewriteRule
rwHistogram tenv inf [container] (size : input : other_args) =
  fmap Just $
  defineAndInspectIndexedInt tenv (return size)
  (\n index ->
    varAppE (pyonBuiltin the_make_list)
    [TypM intType, TypM $ VarT n]
    (varE index :
     varAppE (pyonBuiltin the_referenced)
     [TypM $ varApp (pyonBuiltin the_array) [VarT n, intType]]
     [varAppE (pyonBuiltin the_histogramArray)
      [container, TypM $ VarT n]
      [varE index, return input]] :
     map return other_args))

rwHistogram _ _ _ _ = return Nothing

rwReduce :: RewriteRule
rwReduce tenv inf
  [container, element]
  (traversable : repr : reducer : init : input : other_args) =
  fmap Just $
  caseOfTraversableDict tenv (return traversable) container $ \trv _ ->
  let app_other_args = map return other_args
  in varAppE (pyonBuiltin the_fun_reduce_Stream)
     [container, element]
     ([return repr, return reducer, return init,
       varAppE trv [element] [return repr, return input]] ++
      app_other_args)

rwReduce _ _ _ _ = return Nothing

-- | @reduce1@ is just like @reduce@ except there's no initial value
rwReduce1 :: RewriteRule
rwReduce1 tenv inf
  [container, element]
  (traversable : repr : reducer : input : other_args) =
  fmap Just $
  caseOfTraversableDict tenv (return traversable) container $ \trv _ ->
  let app_other_args = map return other_args
  in varAppE (pyonBuiltin the_fun_reduce1_Stream)
     [container, element]
     ([return repr, return reducer,
       varAppE trv [element] [return repr, return input]] ++
      app_other_args)

rwReduce1 _ _ _ _ = return Nothing

rwReduceStream :: RewriteRule
rwReduceStream tenv inf [shape_type, element]
  (elt_repr : reducer : init : stream : other_args) =
  case interpretStream elt_repr stream
  of Just s ->
       case sShape s
       of Array1DShape size count ->
            fmap Just $
            rwReduceGenerate inf element elt_repr reducer init other_args size count (sGenerator s)
          _ -> return Nothing
     _ -> return Nothing

rwReduceStream _ _ _ _ = return Nothing

rwReduceGenerate :: ExpInfo -> TypM -> ExpM -> ExpM -> ExpM -> [ExpM]
                 -> TypM -> ExpM -> (ExpM -> MkExpM) -> FreshVarM ExpM
rwReduceGenerate inf element elt_repr reducer init other_args size count producer =
  -- Create a sequential loop.
  -- In each loop iteration, generate a value and combine it with the accumulator. 
  varAppE (pyonBuiltin the_for) [size, element]
  (return elt_repr :
   return count :
   return init :
   (lamE $ mkFun []
   (\ [] -> return ([ValPT Nothing ::: intType, ReadPT ::: fromTypM element,
                     OutPT ::: fromTypM element],
                    SideEffectRT ::: fromTypM element))
   (\ [] [ix, acc, ret] -> do
       tmpvar <- newAnonymousVar ObjectLevel
       let tmpvar_binder = localVarP tmpvar (fromTypM element) elt_repr
       -- Produce a new value
       rhs <- appE (producer (ExpM $ VarE defaultExpInfo ix)) [] [varE tmpvar]
       -- Combine with accumulator
       body <- appE (return reducer) [] [varE acc, varE tmpvar, varE ret]
       return $ ExpM $ LetE defaultExpInfo tmpvar_binder rhs body)) :
   map return other_args)

rwReduce1Stream :: RewriteRule
rwReduce1Stream tenv inf [shape_type, element]
  (elt_repr : reducer : stream : other_args) =
  case interpretStream elt_repr stream
  of Just s -> 
       case sShape s
       of Array1DShape size count ->
            fmap Just $
            rwReduce1Generate inf element elt_repr reducer other_args size count (sGenerator s)
          _ -> return Nothing
     _ -> return Nothing

rwReduce1Stream _ _ _ _ = return Nothing

rwReduce1Generate inf element elt_repr reducer other_args size count producer = do
  producer_var <- newAnonymousVar ObjectLevel
  producer_fn <- mkFun []
    (\ [] -> return ([ValPT Nothing ::: intType],
                     BoxRT ::: FunT (OutPT ::: fromTypM element) (SideEffectRT ::: fromTypM element)))
    (\ [] [index] -> producer $ ExpM $ VarE defaultExpInfo index)

  -- Get the first value.
  -- This may crash if there aren't any values.
  tmpvar <- newAnonymousVar ObjectLevel
  let tmpvar_binder = localVarP tmpvar (fromTypM element) elt_repr
  rhs <- varAppE producer_var [] [litE (IntL 0 intType), varE tmpvar]
  
  -- Loop over the remaining values
  let producer_plus_1 index =
        varAppE producer_var []
        [varAppE (pyonBuiltin the_AdditiveDict_int_add) []
         [return index, litE (IntL 1 intType)]]
  
  let size_minus_1 = TypM $ varApp (pyonBuiltin the_minus_i) [fromTypM size, VarT (pyonBuiltin the_one_i)]
  count_minus_1 <-
    varAppE (pyonBuiltin the_minus_ii)
    [size, TypM $ VarT (pyonBuiltin the_one_i)]
    [return count, varE (pyonBuiltin the_one_ii)]

  body <- rwReduceGenerate inf element elt_repr reducer
          (ExpM $ VarE defaultExpInfo tmpvar) other_args size_minus_1 count_minus_1 producer_plus_1
          
  -- Build a let expression
  return $ ExpM $ LetfunE defaultExpInfo (NonRec (Def producer_var producer_fn)) $
           ExpM $ LetE defaultExpInfo tmpvar_binder rhs body

-------------------------------------------------------------------------------

-- | An argument to one of the 'zip' family of functions.
data ZipArg =
  ZipArg
  { zipElementType     :: TypM  -- ^ The data type stored in the contianer
  , zipElementDict     :: ExpM  -- ^ @Repr@ of the element
  , zipContainerValue  :: ExpM  -- ^ The container value
  }
     
-- | Generalized rewriting of zip_N to zipStream_N.  Takes a list of inputs
--   and the output as parameters.
generalizedRewriteZip :: TypeEnv -> ExpInfo -> [ZipArg] -> TypM -> ExpM
                      -> [ExpM]
                      -> FreshVarM ExpM
generalizedRewriteZip tenv inf inputs container traversable other_args =
  caseOfTraversableDict tenv (return traversable) container $ \trv bld ->
  let tuple_size = length inputs
      field_types = map zipElementType inputs
      tuple_type = varApp (pyonTupleTypeCon tuple_size) (map fromTypM field_types)
      tuple_repr = varAppE (pyonTupleReprCon tuple_size) field_types
                   (map (return . zipElementDict) inputs)
      app_other_args = map return other_args
  in varAppE bld [TypM tuple_type]
     (tuple_repr :
      varAppE (zipper tuple_size) (container : field_types)
      ([return $ zipElementDict input | input <- inputs] ++
       [varAppE trv [zipElementType input]
        [return $ zipElementDict input, return $ zipContainerValue input] 
       | input <- inputs]) :
      app_other_args)

zipper 2 = pyonBuiltin the_fun_zip_Stream
zipper 3 = pyonBuiltin the_fun_zip3_Stream
zipper 4 = pyonBuiltin the_fun_zip4_Stream
zipper n = internalError $ "zipper: Cannot zip " ++ show n ++ " streams"

-- | The iteration domain of a stream
data Shape =
    -- | An unbounded stream
    UnboundedShape
    -- | A 1D array stream with a type index and size expression
  | Array1DShape TypM ExpM
    -- | An unknown iteration domain that has the given shape index
  | UnknownShape TypM

-- | Return a type that is a valid type index for the given shape.
shapeType :: Shape -> Type
shapeType shp = 
  case shp
  of UnboundedShape              -> VarT $ pyonBuiltin the_list
     Array1DShape (TypM index) _ -> varApp (pyonBuiltin the_array) [index]
     UnknownShape (TypM s_index) -> s_index
  
-- | The interpreted value of a stream.
data InterpretedStream =
  InterpretedStream
  { -- | The stream's shape
    sShape :: !Shape

    -- | The type of a stream element
  , sType :: Type

    -- | The representation dictionary of a stream element
  , sRepr :: ExpM

    -- | Given an expression that evaluates to the index of the desired
    --   stream element (with type @val int@), produce an expression that
    --   evaluates to the desired stream element, as a write reference. 
  , sGenerator :: ExpM -> MkExpM
  }

-- | Given a stream and the repr of a stream element, get its shape.
--
--   We may change the stream's type by ignoring functions that only
--   affect the advertised stream shape.
interpretStream :: ExpM -> ExpM -> Maybe InterpretedStream
interpretStream repr expression =
  case unpackVarAppM expression
  of Just (op_var, ty_args, args)
       | op_var `isPyonBuiltin` the_TraversableDict_Stream_traverse ->
         case args of [_, stream_arg] -> interpretStream repr stream_arg
       | op_var `isPyonBuiltin` the_TraversableDict_Stream_build ->
         case args of [_, stream_arg] -> interpretStream repr stream_arg
       | op_var `isPyonBuiltin` the_fun_asList_Stream ->
         case args of [stream_arg] -> interpretStream repr stream_arg
       | op_var `isPyonBuiltin` the_generate ->
         let [size_arg, type_arg] = ty_args
             [size_val, repr, writer] = args
         in Just $ InterpretedStream
            { sShape = Array1DShape (TypM size_arg) size_val
            , sType = type_arg
            , sRepr = repr
            , sGenerator = \ix ->
                appE (return writer) [] [return ix]}
       | op_var `isPyonBuiltin` the_count ->
           Just $ InterpretedStream
           { sShape = UnboundedShape
           , sType = intType
           , sRepr = repr
           , sGenerator = counting_generator}
       | op_var `isPyonBuiltin` the_rangeIndexed ->
         let [size_index] = ty_args
             [size_val] = args
         in Just $ InterpretedStream
            { sShape = Array1DShape (TypM size_index) size_val
            , sType = intType
            , sRepr = repr
            , sGenerator = counting_generator}
     _ -> Nothing
  where
    -- A generator for the sequence [0, 1, 2, ...]
    counting_generator ix =
      varAppE (pyonBuiltin the_store) [TypM intType]
      [varE $ pyonBuiltin the_repr_int, return ix]

-- | Produce program code of an interpreted stream.  The generated code
--   will have the specified shape.  If code cannot be generated,
--   return Nothing.
encodeStream :: TypM -> InterpretedStream -> FreshVarM (Maybe ExpM)
encodeStream expected_shape stream = do
  m_encoded <-
    case sShape stream
    of Array1DShape size_ix size_val ->
         fmap Just $
         varAppE (pyonBuiltin the_generate)
         [size_ix, TypM $ sType stream]
         [return size_val,
          return $ sRepr stream,
          lamE $ mkFun []
          (\ [] -> return ([ValPT Nothing ::: intType],
                           BoxRT ::: FunT (OutPT ::: sType stream)
                                          (SideEffectRT ::: sType stream)))
          (\ [] [index_var] ->
            sGenerator stream (ExpM $ VarE defaultExpInfo index_var))]
       _ -> return Nothing

  -- Cast the shape type to the one that the code expects
  let given_shape = shapeType $ sShape stream
      elt_type = sType stream
      elt_repr = sRepr stream
      cast_shape expr = castStreamExpressionShape (fromTypM expected_shape) given_shape elt_type elt_repr expr
  return $ m_encoded >>= cast_shape

-- | Cast a stream of type @Stream given elt@ to a stream of type
--   @Stream expected elt@.
castStreamExpressionShape expected_shape given_shape elt_type elt_repr expr =
  subcast expected_shape given_shape expr
  where
    subcast e_shape g_shape expr =
      case fromVarApp e_shape
      of Just (e_op, e_args)
           | e_op `isPyonBuiltin` the_list ->
             case fromVarApp g_shape
             of Just (g_op, g_args)
                  | g_op `isPyonBuiltin` the_list -> Just expr
                  | otherwise ->
                      -- Reinterpret as a list
                      Just $ cast (pyonBuiltin the_fun_asList_Stream)
                             [TypM given_shape, TypM elt_type] [expr]
                _ -> Nothing

           | e_op `isPyonBuiltin` the_Stream ->
               let [e_stream_shape] = e_args
                   cast_expr expr' =
                     cast (pyonBuiltin the_TraversableDict_Stream_traverse)
                     [TypM e_stream_shape, TypM elt_type] [elt_repr, expr']
               in fmap cast_expr $ subcast e_stream_shape g_shape expr

           | e_op `isPyonBuiltin` the_array ->
               case fromVarApp g_shape
               of Just (g_op, g_args)
                    | g_op `isPyonBuiltin` the_Stream ->
                      let [g_stream_shape] = g_args
                          cast_expr =
                            cast (pyonBuiltin the_TraversableDict_Stream_build)
                            [TypM g_stream_shape, TypM elt_type]
                            [elt_repr, expr]
                      in subcast e_shape g_stream_shape cast_expr
                    | g_op `isPyonBuiltin` the_array ->
                        -- Should verify that array size matches here.
                        -- Since the input program was well-typed, array size
                        -- /should/ match.
                        Just expr
                  _ -> Nothing
         _ -> Nothing
                  
    cast op ty_args args =
      ExpM $ AppE defaultExpInfo (ExpM $ VarE defaultExpInfo op) ty_args args

-- | Zip together a list of two or more streams
zipStreams :: [InterpretedStream] -> InterpretedStream
zipStreams ss
  | num_streams < 2 = internalError "zipStreams: Need at least two streams"
  | Just shape <- zipped_shape =
      let typ = varApp (pyonTupleTypeCon num_streams) (map sType ss)
          repr = ExpM $ AppE defaultExpInfo
                 (ExpM $ VarE defaultExpInfo (pyonTupleReprCon num_streams))
                 (map (TypM . sType) ss)
                 (map sRepr ss)
          gen ix = varAppE (pyonTupleCon num_streams)
                   (map (TypM . sType) ss)
                   [sGenerator stream ix | stream <- ss]
      in InterpretedStream shape typ repr gen
  where
    num_streams = length ss

    zipped_shape = foldr combine_shapes (Just UnboundedShape) $ map sShape ss
          
    -- Combine shapes if possible. 
    -- Array shapes are combined using the "min" operator to get the
    -- minimum value.
    combine_shapes _              Nothing = Nothing 
    combine_shapes shp'           (Just UnboundedShape) = Just shp'
    combine_shapes UnboundedShape (Just shp) = Just shp
    combine_shapes shp'           (Just (Array1DShape typ1 val1)) =
      case shp'
      of Array1DShape typ2 val2 ->
           let typ = TypM $
                     varApp (pyonBuiltin the_min_i) [fromTypM typ1, fromTypM typ2]
               val = ExpM $ AppE defaultExpInfo min_ii [typ1, typ2] [val1, val2] 
           in Just $ Array1DShape typ val
         _ -> Nothing
    combine_shapes shp'           mshp@(Just (UnknownShape _)) =
      case shp'
      of UnknownShape _ -> mshp
         _ -> Nothing
    
    min_ii = ExpM $ VarE defaultExpInfo (pyonBuiltin the_min_ii)

{-
-- | Convert a stream transformer that produces a singleton stream
--   into a function that writes its result.
unreturnStreamTransformer :: ExpM -> Maybe ExpM
unreturnStreamTransformer expr =
  case expr
  of ExpM (LamE inf (FunM f)) -> do
       -- The function takes a single parameter, which is a readable
       -- reference to a value of type @elt_type@.
       new_ret_type <- unreturn_return $ funReturn f
       new_body <- unreturnExp $ funBody f
       return $ ExpM $ LamE inf $ FunM $ f { funReturn = new_ret_type
                                           , funBody = new_body}
     _ -> mzero
  where
    -- Convert a return type of @box Stream a@ to @out a -> SideEffect a@
    unreturn_return (RetM (BoxRT ::: rt))
      | Just (op_var, [elt_type]) <- fromVarApp rt,
        op_var `isPyonBuiltin` the_Stream =
          return $ RetM (BoxRT ::: FunT (OutPT ::: elt_type) 
                                        (SideEffectRT ::: elt_type))

    unreturn_return _ = mzero

-- | Convert an expression whose return value is @return x@ stream into
--   an expression whose return value is @x@.
unreturnExp expression =
  case fromExpM expression
  of VarE {} -> Nothing
     LitE {} -> Nothing
     AppE inf (ExpM (VarE _ op_var)) ty_args [_, arg]
       | op_var `isPyonBuiltin` the_oper_DO -> Just arg
     AppE {} -> Nothing
     LetE inf bind rhs body -> 
       fmap ExpM $ fmap (LetE inf bind rhs) $ unreturnExp body
     LetfunE inf defs body ->
       fmap ExpM $ fmap (LetfunE inf defs) $ unreturnExp body
     CaseE inf scr alts ->
       fmap ExpM $ fmap (CaseE inf scr) $ mapM unreturnAlt alts

unreturnAlt (AltM alt) = do
  body <- unreturnExp $ altBody alt
  return $ AltM (alt {altBody = body})

-}