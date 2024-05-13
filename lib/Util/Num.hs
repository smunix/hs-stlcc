{-# LANGUAGE LambdaCase   #-}
{-# LANGUAGE ViewPatterns #-}

module Util.Num
    ( align
    , band
    , bor
    , bytes
    , castn
    , downTo
    , lg
    , seqMax
    , seqMin
    , upTo
    ) where

import           Data.Bits
import           Data.Function
import           Data.Semigroup
import           Optics
import           Util.Common

-- | enumerations
xxxTo
  ∷ ∀ f n
   . (Cons (f n) (f n) n n, AsEmpty (f n))
  ⇒ (n → n → Bool)
  → Fn n n
  → n
  → n
  → f n
xxxTo while nxt = fix \rec a@(nxt → a') b → if while a b then a :< rec a' b else Empty

downTo ∷ ∀ n. (Num n, Ord n) ⇒ n → n → [n]
downTo = xxxTo (>=) (subtract 1)

upTo ∷ ∀ n. (Num n, Ord n) ⇒ n → n → [n]
upTo = xxxTo (<=) (+ 1)

-- | Sequence operations
seqXXX
  ∷ (Ord a, Bounded (Arg a a), Monoid m)
  ⇒ Fn (Arg a a) m
  → Fn m (Arg a a)
  → a
  → [a]
  → a
seqXXX ctor dtor a ((a :<) → xs) = xs & foldMapOf folded (\a → ctor (Arg a a)) & view (to dtor % _2)

seqMax ∷ (Ord a, Bounded (Arg a a)) ⇒ a → [a] → a
seqMax = seqXXX Max getMax

seqMin ∷ (Ord a, Bounded (Arg a a)) ⇒ a → [a] → a
seqMin = seqXXX Min getMin

-- | min and max operations by operations
seqXXXBy ∷ (Monoid m) ⇒ Fn (Arg b a) m → Fn m (Arg b a) → Fn a b → a → [a] → a
seqXXXBy ctor dtor fn a ((a :<) → as) = as & foldMapOf folded (\a → ctor (Arg (fn a) a)) & view (to dtor % _2)

seqMaxBy ∷ (Ord b, Bounded (Arg b a)) ⇒ Fn a b → a → [a] → a
seqMaxBy = seqXXXBy Max getMax

seqMinBy ∷ (Ord b, Bounded (Arg b a)) ⇒ Fn a b → a → [a] → a
seqMinBy = seqXXXBy Min getMin

castn ∷ (Num b, Integral a) ⇒ a → b
castn = fromInteger . toInteger

alignXXX
  ∷ (Num b, Integral a, Fractional a, Integral b) ⇒ Fn a b → Fn a (Fn b b)
alignXXX fn v b = b * fn (castn v / castn b)

align ∷ (Integral b, Integral a, Fractional a, RealFrac a) ⇒ a → b → b
align = alignXXX ceiling

-- align' ∷ (Integral b, Integral a) ⇒ a → b → b
-- align' v b = alignXXX floor

lg ∷ (Floating a) ⇒ a → a
lg x = log x / log 2

bytes ∷ (Integral a) ⇒ a → a
bytes x = ceiling (lg (castn (x + 1)) / 8.0)

within ∷ (Ord a) ⇒ a → a → a → Bool
within x l t = l <= x && x <= t

-- | bit operations
bXXX ∷ (Bits a, Num a) ⇒ (Fn a (Fn a a)) → [a] → a
bXXX fn = \case
  Empty → 0
  (a :< as) → foldlOf' folded (fn) a as

band ∷ (Bits a, Num a) ⇒ [a] → a
band = bXXX (.&.)

bor ∷ (Bits a, Num a) ⇒ [a] → a
bor = bXXX (.|.)
