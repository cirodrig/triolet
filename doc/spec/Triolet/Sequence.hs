
{-# LANGUAGE GADTs, TypeFamilies, RankNTypes, ScopedTypeVariables #-}
module Triolet.Sequence where

-------------------------------------------------------------------------------
-- Sequences

data Seq a = forall s. Seq s (s -> SeqStep s a)

data SeqStep s a = Yield s a | Skip s | Done

peel_Seq :: Seq a -> Maybe (a, Seq a)
peel_Seq (Seq s g) = peel s
  where
    peel s =
      case g s
      of Yield s' x -> Just (x, Seq s' g)
         Skip s'    -> peel s'
         Done       -> Nothing
     
map_Seq :: (a -> b) -> Seq a -> Seq b
map_Seq f (Seq s g) =
  let g' s = case g s
             of Yield s' x -> Yield s' (f x)
                Skip s'    -> Skip s'
                Done       -> Done
  in Seq s g'

data BindState s a where 
  Outer :: s -> BindState s a 
  Inner :: s -> s' -> (s' -> SeqStep s' a) -> BindState s a

bind_Seq :: forall a b. Seq a -> (a -> Seq b) -> Seq b
bind_Seq (Seq s g) k =
  let g' (Outer s) =
        case g s
        of Yield s' x -> case k x of Seq s2 g2 -> Skip (Inner s' s2 g2)
           Skip s'    -> Skip (Outer s')
           Done       -> Done
      g' (Inner s s2 g2) =
        case g2 s2
        of Yield s2' x -> Yield (Inner s s2' g2) x
           Skip s2'    -> Skip (Inner s s2' g2)
           Done        -> Skip (Outer s)
  in Seq (Outer s) g'

zipWith_Seq :: (a -> b -> c) -> Seq a -> Seq b -> Seq c
zipWith_Seq = error "zipWith_Seq"

fold_Seq :: (a -> acc -> acc) -> Seq a -> acc -> acc 
{-# INLINE fold_Seq #-}
fold_Seq f (Seq s g) x = go s x
  where
    go s x =
      case g s
      of Yield s' y -> go s' (f y x)
         Skip s'    -> go s' x
         Done       -> x

concat_Seq :: Seq a -> Seq a -> Seq a
concat_Seq (Seq s1 g1) (Seq s2 g2) =
  let g' (Left s) =
        case g1 s
        of Yield s' x -> Yield (Left s') x
           Skip s'     -> Skip (Left s')
           Done       -> Skip (Right s2)
      g' (Right s) =
        case g2 s
        of Yield s' x -> Yield (Right s') x
           Skip s'    -> Skip (Right s')
           Done       -> Done
  in Seq (Left s1) g'


unit_Seq :: a -> Seq a
unit_Seq x =
  let f True  = Yield False x
      f False = Done
  in Seq True x