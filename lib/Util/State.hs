module Util.State where

import           Bluefin.Eff
import           Bluefin.State
import           Control.Monad

freshM ∷ (st :> es) ⇒ State Int st → (Int → Eff es r) → Eff es r
freshM counter kont = do
  r ← (get >=> kont) counter
  modify counter (+ 1)
  return r

fresh ∷ ∀ st es r. (st :> es) ⇒ State Int st → (Int → r) → Eff es r
fresh counter kont = freshM counter (pure . kont)
