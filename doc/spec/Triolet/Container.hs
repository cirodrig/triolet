{-

Naming conventions 

In coremodule, type functions begin with a lowercase letter.
The type functions used here are "index", "offset", and "domain".

Naming convention for methods is {methodname}_{typename}.
For example, "at_View" is the name of the "at" method for type "View".

Naming convention for class instances is {dictname}_{typename}.
For example "Funct_Array1" is the name of the "Funct" instance for
type "Array1".  In this file, the dictname begins with a lowercase letter.

Stages of development:

1. Define 'Seq' and implement seq methods.  Refer to the preexisting
   'Sequence' data type for comparison.

2. Define 'Shape' with no fields.  Its type should be defined correctly.
   Fields will be added later.

3. Define 'Functor', 'Indexable', and 'SomeIndexable'.
   Implement functor and indexable methods for 'View'.

4. Define 'indexableToView' and 'someIndexableToView'.

5. Define 'array1Section'.  Implement functor and indexable methods
   for 'array1' and 'array1Section'.

6. Define 'Stream' and fields of 'Shape'.  Define a field accessor
   for each field of 'Shape'.

7. Define 'Shape' instance for 'list_dim'.
-}

{-# LANGUAGE GADTs, TypeFamilies, RankNTypes, ScopedTypeVariables #-}

module Triolet.Container where

import Triolet.Domain
import Triolet.Sequence

import qualified Data.Array as Array

data Store = Store

-------------------------------------------------------------------------------
-- Container classes

-- Exists in coremodule, named "shape"
type family Domain (t :: * -> *)

-- | A functor dictionary

-- coremodule data type "Functor", constructor "functor"
data Funct t =
  Funct
  { funct_map :: forall a b. (a -> b) -> t a -> t b
  }

-- | Objects whose contents can be accessed by index

-- Exists in coremodule but should be reimplemented from scratch
-- coremodule data type "Indexable", constructor "indexable"
data Indexable t =
  Indexable
  { ix_functor :: Funct t

    -- | Get the domain of an indexable object
  , ix_shape :: forall a. t a -> Domain t

    -- | Retrieve an element at an index, without bounds checking.
  , ix_at    :: forall a. t a -> Index (Domain t) -> a

    -- | Get the subset of an indexable object specified by
    --   the given domain.  Assume the given domain is a subset.
  , ix_slice :: forall a. t a -> Domain t -> Offset (Domain t) -> SomeIndexable (Domain t) a

    -- | Wrap the object so that it is not deconstructed by the optimizer.
    --   This can result in better optimization.
  , ix_preserveHint :: forall a. t a -> t a
  }

-- | An arbitrary 'Indexable'

-- coremodule data type "SomeIndexable", constructor "someIndexable"
data SomeIndexable d a where
  SomeIndexable :: Domain t ~ d =>
                   Indexable t -> t a -> SomeIndexable d a

someIndexableToView :: SomeIndexable d a -> View d a
someIndexableToView (SomeIndexable ix x) = indexableToView ix x

someIndexableToStream :: Shape d -> SomeIndexable d a -> Stream d a
someIndexableToStream sh si = traverse_View sh $ someIndexableToView si

data Traversable t =
  Traversable
  { -- | Create a stream that visits all elements of this data structure
    trv_traverse :: forall a. t a -> Stream (Domain t) a
    -- | Construct a new data structure from a stream
  , trv_build    :: forall a. Stream (Domain t) a -> t a
  }

-- | Shape dictionaries

-- Exists in coremodule but should be reimplemented from scratch
-- coremodule data type "Shape", constructor "shape"
data Shape d =
  Shape
  { sh_noOffset  :: Offset d
  , sh_addOffset :: Offset d -> Offset d -> Offset d
  , sh_appOffset :: Offset d -> Index d -> Index d
  , sh_intersect :: d -> d -> d
  , sh_member    :: Index d -> d -> Bool
    -- | Split into 2 pieces
  , sh_split     :: d -> Maybe (d, Offset d, d)
    -- | Split into N pieces
  , sh_splitN    :: Int -> d -> View ListDim (Offset d, d)
  , sh_peel      :: forall a r.
                    ParHint -> (a -> Stream ListDim a -> r) -> (() -> r)
                 -> View d (Stream ListDim a) -> r
  , sh_flatten   :: forall a. Stream d a -> Stream ListDim a
  , sh_generate  :: forall a. Offset d -> d -> (Index d -> a) -> Stream d a
  , sh_map       :: Funct (Stream d)
  , sh_zipWith   :: forall a b c. (a -> b -> c)
                 -> Stream d a -> Stream d b -> Stream d c
  , sh_fold      :: forall a acc. (a -> acc -> acc)
                 -> Stream d a -> acc -> acc
  , sh_foreach   :: forall acc.
                    d -> Offset d -> (Index d -> acc -> acc) -> acc -> acc
  }

-------------------------------------------------------------------------------
-- Views

-- Exists in coremodule, data type "view", constructor "mk_view"
data View d a = View d (Index d -> a)

type instance Domain (View d) = d

indexableToView :: Indexable t -> t a -> View (Domain t) a
indexableToView ix x = View (ix_shape ix x) (\i -> ix_at ix x i)

funct_View :: Funct (View d)
funct_View = Funct map_View

indexable_View :: Shape d -> Indexable (View d)
indexable_View sh = 
  Indexable
  { ix_functor = funct_View
  , ix_shape   = shape_View
  , ix_at      = at_View
  , ix_slice   = slice_View sh
  , ix_preserveHint = id
  }

shape_View :: View d a -> d
shape_View (View d _) = d

at_View :: View d a -> Index d -> a
at_View (View _ g) i = g i

slice_View :: Shape d -> View d a -> d -> Offset d -> SomeIndexable d a 
slice_View sh (View _ g) dom off =
  SomeIndexable (indexable_View sh) $
  View dom (\i -> g $ sh_appOffset sh off i)

traversable_View :: Shape d -> Traversable (View d)
traversable_View sh =
  Traversable
  { trv_traverse = traverse_View sh
  , trv_build = build_View sh
  }

traverse_View :: Shape d -> View d a -> Stream d a
traverse_View sh v =
  stream $ IxStream $ RStream id (SomeIndexable (indexable_View sh) v)

build_View :: forall d a. Shape d -> Stream d a -> View d a
build_View sh s =
  case s
  of Stream _ i_s ->
       case i_s
       of IxStream rs -> rStreamToView rs
          SeqStream _ -> via_array ()
          Splittable _ _ -> via_array ()
  where
    -- Write to an array, then create a view into the array
    via_array :: forall. d ~ ListDim => () -> View ListDim a
    via_array () =
      let l = build_List s
      in indexableToView indexable_List l

map_View :: (a -> b) -> View d a -> View d b
map_View f (View d g) = View d (\x -> f (g x))

zipWith_View :: Shape d -> (a -> b -> c) -> View d a -> View d b -> View d c
zipWith_View shape_dict f (View d1 g1) (View d2 g2) =
  View (sh_intersect shape_dict d1 d2) (\x -> f (g1 x) (g2 x))

singleton_View :: a -> View ListDim a
singleton_View x = View (ListDim (Just 1)) (\_ -> x)

-------------------------------------------------------------------------------
-- Low-level array operations

-- This function has a completely different implementation in
-- Triolet
build_arr1D :: (Int -> a) -> Int -> Array.Array Int a
build_arr1D g n = Array.listArray (0, n-1) [g i | i <- [0..n-1]]

-------------------------------------------------------------------------------
-- Lists (zero-indexed 1D arrays)

-- | A list is an array with an associated length.
--   In Triolet, the data type is called 'list' and the data constructor is
--   called 'make_list'.
data List a = List !Int !(Array.Array Int a)

type instance Domain List = ListDim

listToListSection :: List a -> ListSection a
listToListSection lst@(List n arr) = ListSection lst 0 n

funct_List :: Funct List
funct_List = Funct map_List

map_List :: (a -> b) -> List a -> List b
map_List f l = build_List $ map_Stream f $ traverse_List l

indexable_List :: Indexable List
indexable_List =
  Indexable
  { ix_functor = funct_List
  , ix_shape = shape_List
  , ix_at = at_List
  , ix_slice = slice_List
  , ix_preserveHint = id
  }

shape_List :: List a -> ListDim
shape_List (List n _) = ListDim (Just n)

at_List :: List a -> Int -> a
at_List (List n arr) i = arr Array.! i

slice_List :: List a -> ListDim -> Int -> SomeIndexable ListDim a
slice_List lst dom off =
  case dom
  of ListDim Nothing -> error "Unbounded list domain"
     ListDim (Just n) ->
       SomeIndexable indexable_ListSection $
       ListSection lst off n

traversable_List :: Traversable List
traversable_List = Traversable traverse_List build_List

traverse_List :: List a -> Stream ListDim a
traverse_List lst =
  let indexable = SomeIndexable indexable_ListSection (listToListSection lst)
      ra = RStream id indexable
  in stream $ IxStream ra

build_List :: Stream ListDim a -> List a
build_List s = 
  case s
  of Stream _ i_s ->
       case i_s
       of SeqStream s -> from_seq s
          Splittable sh rs -> from_seq (flattenSplittable sh rs)
          IxStream (RStream f ix) -> tabulate_List f ix
  where
    -- Implemented with a primitive array-appending function in Triolet;
    -- not defined in Haskell
    from_seq s = undefined

-- | A section of a list.
--   A section consists of a list, 
--   an offset within the list, and a length.
data ListSection a = ListSection !(List a) !Int !Int

type instance Domain ListSection = ListDim

funct_ListSection :: Funct ListSection
funct_ListSection = Funct map_ListSection

map_ListSection :: (a -> b) -> ListSection a -> ListSection b
map_ListSection f sec =
  build_ListSection $ map_Stream f $ traverse_ListSection sec

indexable_ListSection :: Indexable ListSection
indexable_ListSection =
  Indexable funct_ListSection shape_ListSection
            at_ListSection slice_ListSection preserve

shape_ListSection :: ListSection a -> ListDim
shape_ListSection (ListSection _ _ length) = ListDim (Just length)

at_ListSection :: ListSection a -> Int -> a
at_ListSection (ListSection lst offset _) i =
  at_List lst (offset + i)

slice_ListSection :: ListSection a -> ListDim -> Int -> SomeIndexable ListDim a
slice_ListSection (ListSection lst offset _) dom offset2 =
  slice_List lst dom (offset + offset2)

traversable_ListSection :: Traversable ListSection
traversable_ListSection = Traversable traverse_ListSection build_ListSection 

traverse_ListSection :: ListSection a -> Stream ListDim a
traverse_ListSection sec =
  stream $ IxStream $ RStream id (SomeIndexable indexable_ListSection sec)

build_ListSection :: Stream ListDim a -> ListSection a
build_ListSection s = listToListSection $ build_List s

-------------------------------------------------------------------------------
-- Arrays

-- This example uses a Haskell library data type instead of the Triolet type.
-- Exists in coremodule, data type "array1", data constructor "mk_array1"
type Array1 = Array.Array Int

type instance Domain Array1 = Dim1

funct_Array1 :: Funct Array1
funct_Array1 = Funct map_Array1

map_Array1 :: (a -> b) -> Array1 a -> Array1 b
map_Array1 f arr = fmap f arr

indexable_Array1 :: Indexable Array1
indexable_Array1 =
  Indexable
  { ix_functor = funct_Array1
  , ix_shape = array1_shape
  , ix_at = array1_at
  , ix_slice = array1_slice
  , ix_preserveHint = id
  }

array1_shape arr =
  let (lb, ub) = Array.bounds arr
  in Dim1 (Interval (Just lb) (Just (ub + 1))) identityMap

array1_at arr i = arr Array.! i

array1_slice arr dom off =
  let -- This example only handles this form of domains.
      -- The library will handle the more general case.
      Dim1 (Interval (Just lb) (Just ub)) (LinearMap 1 0) = dom
      section =
        -- Get the subset of the array that falls within the domain.
        -- The library will have a real "array section" object that
        -- references the original array.
        Array.listArray (lb, ub-1) [arr Array.! i | i <- [lb .. ub-1]]
  in SomeIndexable indexable_Array1Section $
     Array1Section dom section

-- | An array section consists of a domain and a reference to the raw array.
--
--   In Haskell, we model the reference by making a copy of the array.
data Array1Section a = Array1Section Dim1 (Array.Array Int a)

type instance Domain Array1Section = Dim1

funct_Array1Section =
  Funct
  { funct_map = array1Section_map
  }

array1Section_map f (Array1Section d arr) =
  Array1Section d (fmap f arr)

indexable_Array1Section :: Indexable Array1Section
indexable_Array1Section =
  Indexable
  { ix_functor = funct_Array1Section
  , ix_shape = array1Section_shape
  , ix_at = array1Section_at
  , ix_slice = array1Section_slice
  , ix_preserveHint = preserve
  }

array1Section_shape (Array1Section dom _) = dom

array1Section_at (Array1Section _ arr) i = arr Array.! i

array1Section_slice :: Array1Section a -> Dim1 -> () -> SomeIndexable Dim1 a
array1Section_slice (Array1Section _ arr) dom () =
  SomeIndexable indexable_Array1Section $ Array1Section dom arr

-------------------------------------------------------------------------------
-- Zipped indexables

-- | A zipped indexable.
--
--   Both sub-indexables must have the same domain.
data Zip2Indexable s t d a where
  Zip2Indexable :: (Domain s ~ d, Domain t ~ d) =>
                   (a -> b -> c)
                -> s a
                -> t b
                -> Zip2Indexable s t d c

type instance Domain (Zip2Indexable s t d) = d

-- | Zip two indexables.  They must have exactly the same domain.
zipSameDomainIndexables :: Shape d -> (a -> b -> c)
                        -> SomeIndexable d a -> SomeIndexable d b
                        -> SomeIndexable d c
zipSameDomainIndexables sh f (SomeIndexable ix1 i1) (SomeIndexable ix2 i2) =
  let ix = indexable_Zip2Indexable sh ix1 ix2
  in SomeIndexable ix (Zip2Indexable f i1 i2)


-- | Slice two objects and construct a 'Zip2Indexable' from them.
--   After slicing, the two objects must have the same domain; this is not 
--   checked.
sliceAndZipIndexables :: (Domain s ~ d, Domain t ~ d) =>
                         Shape d -> Indexable s -> Indexable t
                      -> (a -> b -> c)
                      -> s a -> t b -> d -> Offset d
                      -> SomeIndexable d c
sliceAndZipIndexables sh ix1 ix2 f i1 i2 dom off =
  zipSameDomainIndexables sh f (ix_slice ix1 i1 dom off) (ix_slice ix2 i2 dom off)
  
zip2Indexable :: (Domain s ~ d, Domain t ~ d) =>
                 Shape d -> Indexable s -> Indexable t 
              -> (a -> b -> c)
              -> s a -> t b -> SomeIndexable d c
zip2Indexable sh ix1 ix2 f i1 i2 =
  let dom = sh_intersect sh (ix_shape ix1 i1) (ix_shape ix2 i2)
      off = sh_noOffset sh
  in sliceAndZipIndexables sh ix1 ix2 f i1 i2 dom off

map_Zip2Indexable f (Zip2Indexable g i1 i2) =
  Zip2Indexable (\x y -> f (g x y)) i1 i2

funct_Zip2Indexable = Funct map_Zip2Indexable

indexable_Zip2Indexable :: (Domain s ~ d, Domain t ~ d) =>
                           Shape d -> Indexable s -> Indexable t
                        -> Indexable (Zip2Indexable s t d)
indexable_Zip2Indexable sh ix1 ix2 =
  Indexable 
  { ix_functor = funct_Zip2Indexable
  , ix_shape   = zip2Indexable_shape ix1 ix2
  , ix_at      = zip2Indexable_at ix1 ix2
  , ix_slice   = zip2Indexable_slice sh ix1 ix2
  , ix_preserveHint = zip2Indexable_preserveHint sh ix1 ix2
  }

zip2Indexable_shape :: Indexable s -> Indexable t -> Zip2Indexable s t d a -> d
zip2Indexable_shape ix1 ix2 (Zip2Indexable _ x _) = ix_shape ix1 x

zip2Indexable_at :: Indexable s -> Indexable t ->
                    Zip2Indexable s t d a -> Index d -> a
zip2Indexable_at ix1 ix2 (Zip2Indexable f x y) i =
  f (ix_at ix1 x i) (ix_at ix2 y i)

zip2Indexable_slice :: Shape d -> Indexable s -> Indexable t ->
                       Zip2Indexable s t d a -> d -> Offset d
                    -> SomeIndexable d a
zip2Indexable_slice sh ix1 ix2 (Zip2Indexable f x y) dom off =
  sliceAndZipIndexables sh ix1 ix2 f x y dom off

zip2Indexable_preserveHint :: Shape d -> Indexable s -> Indexable t ->
                              Zip2Indexable s t d a -> Zip2Indexable s t d a
zip2Indexable_preserveHint sh ix1 ix2 (Zip2Indexable f x y) =
  Zip2Indexable f (ix_preserveHint ix1 x) (ix_preserveHint ix2 y)

-------------------------------------------------------------------------------
-- Sequences

viewToSeq :: View ListDim a -> Seq a
viewToSeq (View d f) = Seq s g
  where
    s = 0
    g s = if case d
             of ListDim Nothing -> True
                ListDim (Just bound) -> s < bound
          then Yield (s+1) (f s)
          else Done

rStreamToSeq :: RStream ListDim a -> Seq a
rStreamToSeq (RStream f ix) = map_Seq f (viewToSeq (someIndexableToView ix))

rStreamToView :: RStream d a -> View d a
rStreamToView (RStream f ix) = map_View f (someIndexableToView ix)

viewToRStream :: Shape d -> View d a -> RStream d a
viewToRStream sh vw = RStream id (SomeIndexable (indexable_View sh) vw)

viewToSplittable :: Shape d -> View d (Stream ListDim a) -> IStream ListDim a 
viewToSplittable sh vw = Splittable sh $ viewToRStream sh vw

map_RStream :: (a -> b) -> RStream d a -> RStream d b
map_RStream f (RStream g x) = RStream (f . g) x

{-
viewToStream :: Shape d -> View d a -> Stream d a
viewToStream sh vw =
  IxStream id (SomeIndexable (indexable_View sh) vw)
-}


flattenSplittable :: forall d a.
                     Shape d -> RStream d (Stream ListDim a) -> Seq a
flattenSplittable sh (RStream (f :: b -> Stream ListDim a) ix) =
  let View dom g = someIndexableToView ix

      -- A sequence containing all indices in the outer container
      outer_indices :: forall. Seq (Index d)
      outer_indices = asSequence $ sh_flatten sh (indices sh dom)

  in bind_Seq outer_indices (\x -> asSequence $ f $ g x)

-- flattenChain :: Stream ListDim a -> Stream ListDim a -> Seq a
-- flattenChain s1 s2 = concat_Seq (asSequence s1) (asSequence s2)

-------------------------------------------------------------------------------
-- Domain instances

shape_Unit :: Shape ()
shape_Unit = undefined

shape_ChainDim :: Shape ChainDim
shape_ChainDim = undefined

shape_ListDim :: Shape ListDim
shape_ListDim =
  Shape 
  { sh_noOffset = 0 
  , sh_addOffset = addOffset_ListDim 
  , sh_appOffset = appOffset_ListDim
  , sh_intersect = intersect_ListDim 
  , sh_member = member_ListDim
  , sh_split = split_ListDim 
  , sh_splitN = splitN_ListDim
  , sh_peel = peel_ListDim 
  , sh_flatten = flatten_ListDim
  , sh_generate = generate_ListDim 
  , sh_map = funct_Stream 
  , sh_zipWith = zipWith_ListDim 
  , sh_fold = fold_ListDim
  , sh_foreach = foreach_ListDim
  }

addOffset_ListDim o p = o + p

appOffset_ListDim off i = i + off

intersect_ListDim (ListDim bound1) (ListDim bound2) =
  case bound1
  of Nothing -> ListDim bound2
     Just b1 -> case bound2
                of Nothing -> ListDim (Just b1)
                   Just b2 -> ListDim (Just (min b1 b2))

member_ListDim i (ListDim b) =
  case b
  of Nothing -> i >= 0
     Just u  -> i >= 0 && i < u

split_ListDim :: ListDim -> Maybe (ListDim, Int, ListDim)
split_ListDim (ListDim Nothing) = Nothing
split_ListDim (ListDim (Just n))
  | n <= 1    = Nothing
  | otherwise = let m = n `div` 2
                in Just (ListDim (Just m), m, ListDim (Just (n - m)))

splitN_ListDim :: Int -> ListDim -> View ListDim (Int, ListDim)
splitN_ListDim n dom = 
  case dom
  of ListDim Nothing  -> singleton_View (0, dom)
     ListDim (Just b) ->
       let get_i i =
             let start = (i * b)     `div` n
                 end   = ((i+1) * b) `div` n
             in (start, ListDim (Just (end - start)))
       in View (ListDim (Just n)) get_i

-- | Remove one value from a ListDim 
peelListDim :: ListDim -> Maybe ListDim
peelListDim (ListDim n) =
  case n
  of Nothing -> Just (ListDim Nothing)
     Just 0  -> Nothing
     Just n  -> Just (ListDim (Just (n-1)))

peelStream :: forall a r.
              (a -> Stream ListDim a -> r) -- ^ Success continuation
           -> (() -> r)                    -- ^ Empty continuation
           -> Stream ListDim a
           -> r
peelStream val_k emp_k (Stream h i_s) =
  case i_s
  of SeqStream sq -> case peel_Seq sq
                     of Just (x, sq') -> val_k x (Stream h $ SeqStream sq')
                        Nothing       -> emp_k ()

     Splittable shp rs -> sh_peel shp h val_k emp_k (rStreamToView rs)

     IxStream rs ->
       let View dom visit = rStreamToView rs
       in case peelListDim dom
          of Nothing -> emp_k ()
             Just dom' ->
               let visit' i = visit (1+i)
               in val_k (visit 0) (traverse_View shape_ListDim (View dom' visit'))

peel_ListDim :: forall a r.
                ParHint
             -> (a -> Stream ListDim a -> r)
             -> (() -> r)
             -> View ListDim (Stream ListDim a)
             -> r
peel_ListDim hint val_k emp_k (View (ListDim bound) visit) =
  -- Sequentially search 'visit' until a value is found 
  let search i =
        if case bound of {Nothing -> True; Just n -> i < n}
        then let found_value v s =
                   -- Get the rest of this chunk of the stream
                   let new_dom = case bound 
                                 of Nothing -> ListDim Nothing
                                    Just n  -> ListDim (Just (n - i))
                       remainder_input =
                         Stream hint $
                         viewToSplittable shape_ListDim $
                         View new_dom (\j -> visit (i + j))
                       remainder = chain s remainder_input
                   in val_k v remainder
                 not_found () = search (i+1)
             in peelStream found_value not_found (visit i)
        else emp_k ()
  in search 0

flatten_ListDim :: Stream ListDim a -> Stream ListDim a
flatten_ListDim x = x

generate_ListDim :: Int -> ListDim -> (Int -> a) -> Stream ListDim a 
generate_ListDim off dom g =
  traverse_View shape_ListDim (View dom (\x -> g (off + x)))

map_ListDim :: (a -> b) -> Stream ListDim a -> Stream ListDim b
map_ListDim f (Stream h s) =
  case s
  of SeqStream s -> Stream h $ SeqStream (map_Seq f s)
     Splittable shp rs -> Stream h $ Splittable shp $ map_RStream (map_Stream f) rs
     IxStream rs -> Stream h $ IxStream $ map_RStream f rs

zipWith_ListDim :: forall a b c.
                   (a -> b -> c)
                -> Stream ListDim a -> Stream ListDim b -> Stream ListDim c
zipWith_ListDim f (Stream h1 s) (Stream h2 t) =
  let u = case s
          of IxStream rs1 ->
               case t
               of IxStream rs2 -> IxStream $ zipWith_RStream shape_ListDim f rs1 rs2
                  _ -> use_sequences ()
             _ -> use_sequences ()
  in Stream (zipParHints h1 h2) u
  where
    use_sequences () =
      SeqStream $ zipWith_Seq f (asSequenceI s) (asSequenceI t)

zipWith_RStream :: Shape d ->
                   (a -> b -> c) -> RStream d a -> RStream d b -> RStream d c
zipWith_RStream sh f (RStream f1 i1) (RStream f2 i2) =
  let tup x y = (x, y) 
      f' (x, y) = f (f1 x) (f2 y)
  in case i1 
     of SomeIndexable ix1 c1 ->
          case i2
          of SomeIndexable ix2 c2 ->
               RStream f' $ zip2Indexable sh ix1 ix2 tup c1 c2


fold_ListDim :: (a -> acc -> acc) -> Stream ListDim a -> acc -> acc
{-# INLINE fold_ListDim #-}
fold_ListDim f s x = fold_Seq f (asSequence s) x

foreach_ListDim :: forall acc.
                   ListDim -> Int -> (Int -> acc -> acc) -> acc -> acc
foreach_ListDim (ListDim bound) off gen init =
  case bound
  of Nothing  -> error "foreach_ListDim"
     (Just b) ->
       let start    = off
           end      = b + off
           step i x = if i < end
                      then step (i+1) (gen i x)
                      else x
       in step start init

-------------------------------------------------------------------------------
-- Streams

data ParHint = HintAny | HintSeq | HintLocalPar | HintPar

zipParHints :: ParHint -> ParHint -> ParHint
zipParHints x y =
  case x
  of HintAny      -> y
     HintSeq      -> HintSeq
     HintLocalPar -> case y
                     of HintAny -> x
                        HintSeq -> HintSeq
                        _       -> HintLocalPar
     HintPar      -> y

data Stream d a = Stream !ParHint !(IStream d a)

stream s = Stream HintAny s

data IStream d a where
  -- | Values computed sequentially
  SeqStream :: Seq a -> IStream ListDim a

  -- | Partitionable sequences
  Splittable :: Shape d2 -> RStream d2 (Stream ListDim a) -> IStream ListDim a

  -- | Random-access sequences.
  --   We try to make the 'SomeIndexable' a manifest data structure,
  --   either an array or a section, whenever possible.
  --   If we want to map a function over this data structure, the map
  --   is deferred until when the stream is actually executed.
  IxStream :: RStream d a -> IStream d a

-- | A random-access stream
data RStream d a where
  RStream :: (b -> a) -> SomeIndexable d b -> RStream d a

indices :: Shape d -> d -> Stream d (Index d)
indices shp dom = sh_generate shp (sh_noOffset shp) dom id

chain :: Stream ListDim a -> Stream ListDim a -> Stream ListDim a
chain s1 s2 =
  stream $
  viewToSplittable shape_ChainDim $
  View ChainBoth (\i -> case i
                        of False -> s1
                           True  -> s2)

funct_Stream :: Funct (Stream d)
funct_Stream = Funct map_Stream

map_Stream :: (a -> b) -> Stream d a -> Stream d b
map_Stream f (Stream h s) =
  let u = case s
          of SeqStream sq -> SeqStream $ map_Seq f sq
             Splittable sh vw -> Splittable sh $ map_RStream (map_Stream f) vw
             IxStream rs -> IxStream $ map_RStream f rs
  in Stream h u

asSequence :: Stream ListDim a -> Seq a
{-# INLINE asSequence #-}
asSequence (Stream _ s) = asSequenceI s

asSequenceI :: IStream ListDim a -> Seq a
asSequenceI (SeqStream s) = s
asSequenceI (Splittable sh v) = flattenSplittable sh v
asSequenceI (IxStream rs) = rStreamToSeq rs


unit :: a -> Stream ListDim a
unit x = stream $ IxStream $ viewToRStream shape_ListDim $ singleton_View x

empty :: Stream ListDim a
empty = stream $ IxStream $ viewToRStream shape_ListDim $
        View (ListDim (Just 0)) (\_ -> error "empty")

guard :: Bool -> Stream ListDim a -> Stream ListDim a
guard b (Stream h s) =
  let u = case s
          of SeqStream sq -> SeqStream $ guard_Seq b sq
             Splittable sh rs -> Splittable sh $ map_RStream (guard b) rs
             IxStream _ ->
               -- TODO
               undefined
  in Stream h u

bind :: Stream ListDim a -> (a -> Stream ListDim b) -> Stream ListDim b
bind (Stream h s) k =
  let u = case s
          of SeqStream sq -> SeqStream $ bind_Seq sq (\x -> asSequence (k x))
             Splittable sh (RStream f ix) ->
               let f' x = bind (f x) k
               in Splittable sh (RStream f' ix)
             IxStream (RStream f (SomeIndexable ix x)) -> 
               let dom = ix_shape ix x
                   g i = k (f $ ix_at ix x i)
               in Splittable shape_ListDim $ viewToRStream shape_ListDim $ View dom g
  in Stream h u

-- RECURSIVE
reduce_Stream :: forall d a. Shape d -> (a -> a -> a) -> a -> Stream d a -> a
reduce_Stream sh f z (Stream par_hint s) =
  let reduce_unit () = z
      reduce_residual = undefined
  in case s
     of SeqStream sq ->
          fold_Seq f sq z

        Splittable (sh_local :: Shape d')
                   (RStream (g :: b -> Stream ListDim a)
                            (splittable_data :: SomeIndexable d' b)) ->
          let reduce_chunk :: SomeIndexable d' b -> a
              reduce_chunk si =
                reduce_Stream sh f z $
                Stream HintSeq $
                Splittable sh_local (RStream g si)
          in reduce sh_local par_hint reduce_unit
             reduce_chunk f reduce_residual splittable_data

        IxStream (RStream g splittable_data) ->
          let reduce_chunk si =
                reduce_Stream sh f z $
                Stream HintSeq $ IxStream (RStream g si)
          in reduce sh par_hint reduce_unit
             reduce_chunk f reduce_residual splittable_data

-- | Parallelizable reduction
reduce :: forall d a b.
          Shape d
       -> ParHint
       -> (() -> b)                -- reduce unit
       -> (SomeIndexable d a -> b) -- reduce slice
       -> (b -> b -> b)            -- reduce pair
       -> (Stream ListDim b -> b)  -- reduce residual
       -> SomeIndexable d a
       -> b
reduce sh par_hint reduce_none reduce_slice reduce_item reduce_resiudal si =
  reduce_slice si

-- | Distributed reduction
reduce_dist :: forall d a b.
               Shape d
            -> (SomeIndexable d a -> b -> b)
            -> (b -> b -> b)
            -> b
            -> SomeIndexable d a
            -> b
reduce_dist sh reduce_slice reduce_item z si@(SomeIndexable ix x) =
  let dom = ix_shape ix x
      distributed_dom = sh_splitN sh n_PROCESSORS dom
      
      -- Compute partial results
      worker :: SomeIndexable d a -> b
      worker chunk = reduce_slice chunk z

      distributed_inputs = distribute_indexable sh distributed_dom si worker
      partial_results = farm distributed_inputs

      -- Sequentially reduce the partial results
      result = reduce_Stream shape_ListDim reduce_item z $
               traverse_List partial_results

  in result

farm :: List (() -> b) -> List b
farm _ = undefined

-- | Stands for the dynamically identified number of distributed processors
n_PROCESSORS :: Int
n_PROCESSORS = 1

-- | Split an indexable object into slices, and apply a function to each slice.
--   This function is called to create worker functions for a distributed
--   computation.
distribute_indexable :: Shape d
                     -> View ListDim (Offset d, d)
                     -> SomeIndexable d a
                     -> (SomeIndexable d a -> b)
                     -> List (() -> b)
distribute_indexable sh sizes (SomeIndexable ix x) f =
  let apply_f (off, dom) =
        -- Compute the slice immediately; defer the application of 'f'.
        let s = ix_slice ix x dom off
        in \_ -> f s
  in build_List $ traverse_View shape_ListDim $ map_View apply_f sizes

{-
-- | Parallel doall
doallPar :: Shape d -> (a -> Store -> Store) -> Stream d a -> Store -> Store
doallPar sh gen s store =
  case s
  of SeqStream _ -> doallSeq sh gen s store
     Splittable sh' (View dom visit) ->
       let generator (local_dom, local_off) =
             let local_view =
                   View local_dom (\i -> visit (sh_appOffset sh' local_off i))
             in doallSeq sh' gen (Splittable sh' local_view)
       in blockedDoall (splitter sh') generator (dom, sh_noOffset sh') store
     IxStream transform (SomeIndexable ix i) ->
       let generator (local_dom, local_off) =
             let local_view = ix_slice ix i local_dom local_off
             in doallSeq sh gen (IxStream transform local_view)
           dom = ix_shape ix i
       in blockedDoall (splitter sh) generator (dom, sh_noOffset sh) store

doallSeq = undefined

-- | Parallel reduction with sequential fold
reduceFoldPar :: forall a b c d.
                 Shape d
              -> (a -> b -> b)
              -> (c -> c -> c)
              -> ((b -> b) -> c)
              -> c
              -> Stream d a
              -> c
reduceFoldPar sh f r wrap z s =
  case s
  of SeqStream _ -> wrap (sh_fold sh f s)
     Splittable (sh' :: Shape d') (View dom visit) ->
       let generator :: forall. (d', Offset d') -> c
           generator (local_dom, local_off) =
             let local_view =
                   View local_dom (\i -> visit (sh_appOffset sh' local_off i))
             in wrap (sh_fold sh f (Splittable sh' local_view))
       in blockedReduce (splitter sh') r z generator (dom, sh_noOffset sh')

-- | Parallel reduction
reducePar :: Shape d -> (a -> a -> a) -> a -> Stream d a -> a
reducePar sh f z s = 
  case s
  of SeqStream _ -> reduceSeq sh f z s
     Splittable sh' (View dom visit) ->
       let generator (local_dom, local_off) =
             let local_view =
                   View local_dom (\i -> visit (sh_appOffset sh' local_off i))
             in reduceSeq sh f z (Splittable sh' local_view)
       in blockedReduce (splitter sh') f z generator (dom, sh_noOffset sh')

reduceSeq :: Shape d -> (a -> a -> a) -> a -> Stream d a -> a
reduceSeq sh f z s = sh_fold sh f s z
-}

splitter :: Shape d -> ((d, Offset d) -> Maybe ((d, Offset d), (d, Offset d)))
splitter sh (dom, off) =
  case sh_split sh dom
  of Nothing -> Nothing
     Just (dom1, off1, dom2) ->
       Just ((dom1, off), (dom2, sh_addOffset sh off off1))

-- | External function for parallel doall
blockedDoall :: ((d, Offset d) -> Maybe ((d, Offset d), (d, Offset d)))
             -> ((d, Offset d) -> Store -> Store)
             -> (d, Offset d)
             -> Store
             -> Store
blockedDoall = undefined

-- | External function for parallel reduction
blockedReduce :: ((d, Offset d) -> Maybe ((d, Offset d), (d, Offset d)))
              -> (a -> a -> a)
              -> a
              -> ((d, Offset d) -> a)
              -> (d, Offset d)
              -> a
blockedReduce = undefined

-- | Construct a list.  All list elements can be computed in parallel.
tabulate_List :: (a -> b) -> SomeIndexable ListDim a -> List b
tabulate_List f ix =
  let View dom visit = map_View f $ someIndexableToView ix
  in case dom
     of ListDim (Just length) -> List length (build_arr1D visit length)
        ListDim Nothing -> error "Unbounded stream"

preserve x = x

{-
-- | Construct a list in parallel.  Same interface as 'tabulate_List'.
tabulate_List_par :: (a -> b) -> SomeIndexable ListDim a -> List b
tabulate_List_par f ix =
  let parts = distribute shape_ListDim n_PROCESSORS ix
      results = map (tabulate_List f) parts
  in undefined
  where
    n_PROCESSORS = 4
  

-- | Split a 'SomeIndexable' into N approximately equal-size pieces.
--   May produce fewer than N pieces if the object can't be split so much.
distribute :: Shape d -> Int -> SomeIndexable d a
           -> [(Offset d, SomeIndexable d a)]
distribute sh n (SomeIndexable ix_dict x) =
  let dom = ix_shape ix_dict x
  in fill n 0 dom
  where
    fill_singleton offset dom =
      [(offset, ix_slice ix_dict x dom offset)]

    fill count offset dom =
      case count
      of 0 -> []
         1 -> fill_singleton offset dom
         n -> -- Split the domain
           let lo_half = n `div` 2
               hi_half = n - lo_half
           in case sh_split dom
              of Nothing ->
                   fill_singleton offset dom
                 Just (d1, hi_off, d2) ->
                   fill lo_half offset d1 ++
                   fill hi_half (sh_addOffset offset hi_off) d2

-}