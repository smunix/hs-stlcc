{-# LANGUAGE LambdaCase   #-}
{-# LANGUAGE ViewPatterns #-}

module Util.String where

import           Control.Arrow
import           Util.Common
import           Util.Sequence

cdelim ∷ [a] → [[a]] → [a]
cdelim sep = ($ id) $ fix \rec k → \case
  Empty → k Empty
  a :< Empty → k a
  a :< as → rec (((a <> sep) <>) .> k) as

padr ∷ Int → a → [a] → [a]
padr n w ws = ws <> take (n - lengthOf folded ws) (repeat w)

padl ∷ Int → a → [a] → [a]
padl n w ws = take (n - lengthOf folded ws) (repeat w) <> ws

prfx ∷ (Show a) ⇒ String → a → String
prfx pfx x = unwords [pfx, ".", show x]

csplit ∷ (Eq a, IndexOf a) ⇒ [a] → [a] → [[a]]
csplit pat = \case
  (lsplit pat → ss)
    | (h, Empty) ← ss → h :< Empty
    | (h, as') ← ss → h :< csplit pat as'

lsplit ∷ (IndexOf a, Eq a) ⇒ [a] → [a] → ([a], [a])
lsplit pat@(lengthOf folded → patn) = \case
  as@(indexOf pat → Just n) → (take n as, drop (n + patn) as)
  other → (other, Empty)

rsplit ∷ (IndexOf a, Eq a) ⇒ [a] → [a] → ([a], [a])
rsplit pat@(inv → pat'@(lengthOf folded → patn)) = \case
  as@(inv → as'@(indexOf pat' → Just n)) → (inv .> drop (n + patn) &&& inv .> take n) as'
  other → (Empty, other)
