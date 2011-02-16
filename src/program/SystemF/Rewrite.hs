
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

intType = VarT (pyonBuiltin the_int)

-------------------------------------------------------------------------------
-- Rewrite rules

-- Given the arguments to an application, try to create a rewritten term
type RewriteRule = TypeEnv -> ExpInfo -> [TypM] -> [ExpM]
                -> FreshVarM (Maybe ExpM)

rewriteRules :: Map.Map Var RewriteRule
rewriteRules = Map.fromList table
  where
    table = [ (pyonBuiltin the_TraversableDict_list_traverse, rwTraverseList)
            , (pyonBuiltin the_TraversableDict_list_build, rwBuildList)
            , (pyonBuiltin the_TraversableDict_Stream_traverse, rwBuildTraverseStream)
            , (pyonBuiltin the_TraversableDict_Stream_build, rwBuildTraverseStream)
            , (pyonBuiltin the_oper_CAT_MAP, rwBindStream)
            , (pyonBuiltin the_fun_map_Stream, rwMapStream)
            , (pyonBuiltin the_fun_zip, rwZip)
            , (pyonBuiltin the_fun_zip_Stream, rwZipStream)
            , (pyonBuiltin the_fun_zip3, rwZip3)
            , (pyonBuiltin the_fun_zip3_Stream, rwZip3Stream)
            , (pyonBuiltin the_fun_zip4, rwZip4)
            , (pyonBuiltin the_fun_zip4_Stream, rwZip4Stream)
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

rwTraverseList :: RewriteRule
rwTraverseList tenv inf [elt_type] [elt_repr, list] = fmap Just $
  caseOfList tenv (return list) elt_type $ \size_index size_var array ->
    varAppE (pyonBuiltin the_generate)
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
          varE ret_var])]
  
rwTraverseList _ _ _ _ = return Nothing

rwBuildList :: RewriteRule
rwBuildList tenv inf [elt_type] (elt_repr : stream : other_args) =
  case unpackVarAppM stream
  of Just (op, stream_ty_args, stream_args)
       | op `isPyonBuiltin` the_generate ->
           case stream_ty_args
           of [size, _] ->
                case stream_args
                of [count, _, generate_fn] ->
                     fmap Just $
                     buildListDoall inf elt_type elt_repr stream other_args size count generate_fn
  
     _ -> return Nothing

rwBuildList _ _ _ _ = return Nothing

buildListDoall inf elt_type elt_repr stream other_args size count generate_fn =
  let array_type = varApp (pyonBuiltin the_array) [size, fromTypM elt_type]
  in varAppE (pyonBuiltin the_make_list)
     [elt_type, TypM size]
     ([return count,
       varAppE (pyonBuiltin the_referenced) [TypM array_type]
       [lamE $ mkFun []
        (\ [] -> return ([OutPT ::: array_type], SideEffectRT ::: array_type))
        (\ [] [out_ptr] ->
          varAppE (pyonBuiltin the_doall)
          [TypM size, TypM array_type, elt_type]
          [return count,
           lamE $ mkFun []
           (\ [] -> return ([ValPT Nothing ::: intType],
                            SideEffectRT ::: fromTypM elt_type))
           (\ [] [index_var] ->
             appE (return generate_fn) [] 
             [varE index_var,
              varAppE (pyonBuiltin the_subscript_out) [TypM size, elt_type]
              [return elt_repr, varE out_ptr, varE index_var]])])]] ++
      map return other_args)

-- | The Stream instances of 'build' and 'traverse' are identity functions
rwBuildTraverseStream :: RewriteRule
rwBuildTraverseStream tenv inf [_] [_, stream] = return $ Just stream
rwBuildTraverseStream _ _ _ _ = return Nothing

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
       [elt1, elt2]
       [return repr1, return repr2, return map_fn, return producer]
     _ -> return Nothing

rwBindStream _ _ _ _ = return Nothing

rwMapStream :: RewriteRule
rwMapStream tenv inf
  [elt1, elt2]
  [repr1, repr2, transformer, producer] =
  case unpackVarAppM producer
  of Just (op_var, pr_ty_args, pr_args)
       | op_var `isPyonBuiltin` the_generate ->
         case pr_ty_args
         of [g_sizeix, g_ty] ->
              case pr_args
              of [g_count, g_repr, g_fun] ->
                   fmap Just $
                   rewriteMapOfGenerate tenv inf elt2 repr2 transformer g_sizeix g_ty g_count g_repr g_fun
     _ -> return Nothing

rwMapStream _ _ _ _ = return Nothing

-- Rewrite
--
-- > map (f2, generate (n, f1))
--
-- to                 
-- > generate (n, \i -> let tmp = f1 i tmp in f2 i tmp)
rewriteMapOfGenerate tenv inf elt2 repr2 transformer
                     g_sizeix g_ty g_count g_repr g_fun = do
  tmpvar <- newAnonymousVar ObjectLevel
  varAppE (pyonBuiltin the_generate) [TypM g_sizeix, elt2]
    [return g_count, return repr2,
     lamE $ mkFun []
     (\ [] -> return ([ValPT Nothing ::: intType],
                      BoxRT ::: FunT (OutPT ::: fromTypM elt2) (SideEffectRT ::: fromTypM elt2)))
     (\ [] [ixvar] -> do
         rhs <- appE (return g_fun) [] [varE ixvar, varE tmpvar]
         body <- appE (return transformer) [] [varE tmpvar]
         let binder = localVarP tmpvar g_ty g_repr
             let_expr = ExpM $ LetE defaultExpInfo binder rhs body
         return let_expr)]

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
  [TypM container1, TypM container2, container3, TypM element1, TypM element2]
  (traversable1 : traversable2 : traversable3 : repr1 : repr2 :
   input1 : input2 : other_args) =
  let zip_args = [ZipArg container1 element1 traversable1 repr1 input1,
                  ZipArg container2 element2 traversable2 repr2 input2]
  in fmap Just $
     generalizedRewriteZip tenv inf zip_args container3 traversable3 other_args

rwZip _ _ _ _ = return Nothing

rwZip3 :: RewriteRule
rwZip3 tenv inf
  [TypM container1, TypM container2, TypM container3, container4,
   TypM element1, TypM element2, TypM element3]
  (traversable1 : traversable2 : traversable3 : traversable4 :
   repr1 : repr2 : repr3 :
   input1 : input2 : input3 : other_args) =
  let zip_args = [ZipArg container1 element1 traversable1 repr1 input1,
                  ZipArg container2 element2 traversable2 repr2 input2,
                  ZipArg container3 element3 traversable3 repr3 input3]
  in fmap Just $
     generalizedRewriteZip tenv inf zip_args container4 traversable4 other_args

rwZip3 _ _ _ _ = return Nothing

rwZip4 :: RewriteRule
rwZip4 tenv inf
  [TypM container1, TypM container2, TypM container3, TypM container4, container5,
   TypM element1, TypM element2, TypM element3, TypM element4]
  (traversable1 : traversable2 : traversable3 : traversable4 : traversable5 :
   repr1 : repr2 : repr3 : repr4 :
   input1 : input2 : input3 : input4 : other_args) =
  let zip_args = [ZipArg container1 element1 traversable1 repr1 input1,
                  ZipArg container2 element2 traversable2 repr2 input2,
                  ZipArg container3 element3 traversable3 repr3 input3,
                  ZipArg container4 element4 traversable4 repr4 input4]
  in fmap Just $
     generalizedRewriteZip tenv inf zip_args container5 traversable5 other_args

rwZip4 _ _ _ _ = return Nothing

-- | Rewrite calls to @zipStream@ when we know the size of the stream.
--
-- > zipStream(count, generate(n, f)) -> generate(n, \i -> (i, f i))
-- > zipStream(generate(n, f), count) -> generate(n, \i -> (f i, i))
-- > zipStream(generate(n1, f1), generate(n2, f2)) ->
--     generate(min(n1, n2), \i -> (f1 i, f2 i))
rwZipStream :: RewriteRule
rwZipStream tenv inf
  [element1, element2]
  [repr1, repr2, stream1, stream2]
  | Just shape1 <- streamShape repr1 stream1,
    Just shape2 <- streamShape repr2 stream2 =
      generalizedZipStream [shape1, shape2]

rwZipStream _ _ _ _ = return Nothing

rwZip3Stream :: RewriteRule
rwZip3Stream tenv inf
  [element1, element2, element3]
  [repr1, repr2, repr3, stream1, stream2, stream3]
  | Just shape1 <- streamShape repr1 stream1,
    Just shape2 <- streamShape repr2 stream2,
    Just shape3 <- streamShape repr3 stream3 =
      generalizedZipStream [shape1, shape2, shape3]

rwZip3Stream _ _ _ _ = return Nothing

rwZip4Stream :: RewriteRule
rwZip4Stream tenv inf
  [element1, element2, element3, element4]
  [repr1, repr2, repr3, repr4, stream1, stream2, stream3, stream4]
  | Just shape1 <- streamShape repr1 stream1,
    Just shape2 <- streamShape repr2 stream2,
    Just shape3 <- streamShape repr3 stream3,
    Just shape4 <- streamShape repr4 stream4 =
      generalizedZipStream [shape1, shape2, shape3, shape4]

rwZip4Stream _ _ _ _ = return Nothing

generalizedZipStream streams =
  let zipped_stream = zipStreams streams
      elem_ty = ssType zipped_stream
      tuple_repr = ssRepr zipped_stream
  in case ssShape zipped_stream
     of Nothing -> return Nothing -- Can't deal with infinite streams
        Just (shp_ty, shp_val) ->
          fmap Just $
          varAppE (pyonBuiltin the_generate)
          [shp_ty, TypM elem_ty]
          [return shp_val,
           return tuple_repr,
           lamE $ mkFun []
           (\ [] -> return ([ValPT Nothing ::: intType],
                            BoxRT ::: FunT (OutPT ::: elem_ty)
                            (SideEffectRT ::: elem_ty)))
           (\ [] [ixvar] ->
             ssGenerator zipped_stream $ ExpM (VarE defaultExpInfo ixvar))]

rwReduce :: RewriteRule
rwReduce tenv inf
  [container, element]
  (traversable : repr : reducer : init : input : other_args) =
  fmap Just $
  caseOfTraversableDict tenv (return traversable) container $ \trv _ ->
  let app_other_args = map return other_args
  in varAppE (pyonBuiltin the_fun_reduce_Stream)
     [element]
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
     [element]
     ([return repr, return reducer,
       varAppE trv [element] [return repr, return input]] ++
      app_other_args)

rwReduce1 _ _ _ _ = return Nothing

rwReduceStream :: RewriteRule
rwReduceStream tenv inf [element] (elt_repr : reducer : init : stream : other_args) =
  case unpackVarAppM stream
  of Just (op, ty_args, args)
       | op `isPyonBuiltin` the_generate ->
           case ty_args
           of [size, _] ->
                case args
                of [count, _, producer] ->
                     fmap Just $
                     rwReduceGenerate tenv inf element elt_repr reducer init other_args size count producer
     _ -> return Nothing

rwReduceStream _ _ _ _ = return Nothing

rwReduceGenerate tenv inf element elt_repr reducer init other_args size count producer =
  -- Create a sequential loop.
  -- In each loop iteration, generate a value and combine it with the accumulator. 
  varAppE (pyonBuiltin the_for) [TypM size, element]
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
       rhs <- appE (return producer) [] [varE ix, varE tmpvar]
       -- Combine with accumulator
       body <- appE (return reducer) [] [varE acc, varE tmpvar, varE ret]
       return $ ExpM $ LetE defaultExpInfo tmpvar_binder rhs body)) :
   map return other_args)

rwReduce1Stream :: RewriteRule
rwReduce1Stream tenv inf [element] (elt_repr : reducer : stream : other_args) =
  case unpackVarAppM stream
  of Just (op, ty_args, args)
       | op `isPyonBuiltin` the_generate ->
           case ty_args
           of [size, _] ->
                case args
                of [count, _, producer] ->
                     fmap Just $
                     rwReduce1Generate tenv inf element elt_repr reducer other_args size count producer
     _ -> return Nothing

rwReduce1Stream _ _ _ _ = return Nothing

rwReduce1Generate tenv inf element elt_repr reducer other_args size count producer = do
  producer_var <- newAnonymousVar ObjectLevel
  let producer_type = funType [ValPT Nothing ::: intType, OutPT ::: fromTypM element]
                      (SideEffectRT ::: fromTypM element)
      producer_binder = memVarP producer_var (BoxPT ::: producer_type)

  -- Get the first value.
  -- This may crash if there aren't any values.
  tmpvar <- newAnonymousVar ObjectLevel
  let tmpvar_binder = localVarP tmpvar (fromTypM element) elt_repr
  rhs <- varAppE producer_var [] [litE (IntL 0 intType), varE tmpvar]
  
  -- Loop over the remaining values
  producer_plus_1 <-
    lamE $ mkFun []
    (\ [] -> return ([ValPT Nothing ::: intType],
                     BoxRT ::: FunT (OutPT ::: fromTypM element) (SideEffectRT ::: fromTypM element)))
    (\ [] [index] ->
      varAppE producer_var []
      [varAppE (pyonBuiltin the_AdditiveDict_int_add) []
       [varE index, litE (IntL 1 intType)]])
  
  let size_minus_1 = varApp (pyonBuiltin the_minus_i) [size, VarT (pyonBuiltin the_one_i)]
  count_minus_1 <-
    varAppE (pyonBuiltin the_minus_ii)
    [TypM size, TypM $ VarT (pyonBuiltin the_one_i)]
    [return count, varE (pyonBuiltin the_one_ii)]

  body <- rwReduceGenerate tenv inf element elt_repr reducer
          (ExpM $ VarE defaultExpInfo tmpvar) other_args size_minus_1 count_minus_1 producer_plus_1
          
  -- Build a let expression
  return $ ExpM $ LetE defaultExpInfo producer_binder producer $
           ExpM $ LetE defaultExpInfo tmpvar_binder rhs body

-------------------------------------------------------------------------------

-- | An argument to one of the 'zip' family of functions.
data ZipArg =
  ZipArg
  { zipContainerType   :: Type  -- ^ The container type being zipped
  , zipElementType     :: Type  -- ^ The data type stored in the contianer
  , zipTraversableDict :: ExpM  -- ^ @TraversableDict@ for the container
  , zipElementDict     :: ExpM  -- ^ @Repr@ of the element
  , zipContainerValue  :: ExpM  -- ^ The container value
  }
     
-- | Generalized rewriting of zip_N to zipStream_N.  Takes a list of inputs
--   and the output as parameters.
generalizedRewriteZip :: TypeEnv -> ExpInfo -> [ZipArg] -> TypM -> ExpM
                      -> [ExpM]
                      -> FreshVarM ExpM
generalizedRewriteZip tenv inf inputs out_ty out_traversable other_args =
  withMany get_traverse_method inputs $ \traverse_methods ->
  caseOfTraversableDict tenv (return out_traversable) out_ty $ \_ bld ->
  let tuple_size = length inputs
      field_types = map zipElementType inputs
      tuple_type = varApp (pyonTupleTypeCon tuple_size) field_types
      tuple_repr = varAppE (pyonTupleReprCon tuple_size) (map TypM field_types)
                   (map (return . zipElementDict) inputs)
      app_other_args = map return other_args
  in varAppE bld [TypM tuple_type]
     (tuple_repr :
      varAppE (zipper tuple_size) (map TypM field_types)
      ([return $ zipElementDict input | input <- inputs] ++
       [varAppE traverse [TypM $ zipElementType input]
        [return $ zipElementDict input, return $ zipContainerValue input] 
       | (traverse, input) <- zip traverse_methods inputs]) :
      app_other_args)
  where
    get_traverse_method input k =
      caseOfTraversableDict tenv (return $ zipTraversableDict input)
      (TypM $ zipContainerType input) $ \traverse_method _ -> k traverse_method

zipper 2 = pyonBuiltin the_fun_zip_Stream
zipper 3 = pyonBuiltin the_fun_zip3_Stream
zipper 4 = pyonBuiltin the_fun_zip4_Stream
zipper n = internalError $ "zipper: Cannot zip " ++ show n ++ " streams"

-- | The shape of a stream.
data ShapeStream =
  ShapeStream
  { -- | The number of elements in the stream.
    --   If the stream is infinite,
    --   this is 'Nothing'.  Otherwise, this is a type index @n@ of
    --   kind @intindex@ and an expression of type
    --   @val IndexedInt n@,
    --   both giving the actual number of stream elements.
    --
    --   There is no way to represent an unknown number of elements.
    ssShape :: Maybe (TypM, ExpM)
    
    -- | The type of a stream element
  , ssType :: Type

    -- | The representation dictionary of a stream element
  , ssRepr :: ExpM

    -- | Given an expression that evaluates to the index of the desired
    --   stream element (with type @val int@), produce an expression that
    --   evaluates to the desired stream element, as a write reference. 
  , ssGenerator :: ExpM -> MkExpM
  }

-- | Zip together a list of two or more streams
zipStreams :: [ShapeStream] -> ShapeStream
zipStreams ss
  | num_streams < 2 = internalError "zipStreams: Need at least two streams"
  | otherwise =
      let shape = case mapMaybe ssShape ss
                  of [] -> Nothing
                     xs -> Just $ foldr1 combine_shapes xs
          typ = varApp (pyonTupleTypeCon num_streams) (map ssType ss)
          repr = ExpM $ AppE defaultExpInfo 
                 (ExpM $ VarE defaultExpInfo (pyonTupleReprCon num_streams))
                 (map (TypM . ssType) ss)
                 (map ssRepr ss)
          gen ix = varAppE (pyonTupleCon num_streams)
                   (map (TypM . ssType) ss)
                   [ssGenerator stream ix | stream <- ss]
      in ShapeStream shape typ repr gen
  where
    num_streams = length ss

    -- Combine shapes, using the "min" operator to get the minimum value
    combine_shapes (typ1, val1) (typ2, val2) =
      let typ = TypM $
                varApp (pyonBuiltin the_min_i) [fromTypM typ1, fromTypM typ2]
          val = ExpM $ AppE defaultExpInfo min_ii [typ1, typ2] [val1, val2] 
      in (typ, val)
    
    min_ii = ExpM $ VarE defaultExpInfo (pyonBuiltin the_min_ii)

-- | Given a stream and the repr of a stream element, get its shape.
streamShape :: ExpM -> ExpM -> Maybe ShapeStream
streamShape repr expression =
  case unpackVarAppM expression
  of Nothing -> Nothing
     Just (op_var, ty_args, args)
       | op_var `isPyonBuiltin` the_count ->
           Just $
           ShapeStream { ssShape = Nothing
                       , ssType = VarT $ pyonBuiltin the_int
                       , ssRepr = repr
                       , ssGenerator = \ix ->
                           varAppE (pyonBuiltin the_store)
                           [TypM $ VarT $ pyonBuiltin the_int]
                           [varE $ pyonBuiltin the_repr_int, return ix]}
       | op_var `isPyonBuiltin` the_generate ->
           let [size_arg, type_arg] = ty_args
               [size_val, repr, writer] = args
           in Just $
              ShapeStream { ssShape = Just (TypM size_arg, size_val)
                          , ssType = type_arg
                          , ssRepr = repr
                          , ssGenerator = \ix ->
                              appE (return writer) [] [return ix]}
       | otherwise -> Nothing

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

