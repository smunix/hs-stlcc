module STLC.Def where

import           Optics
import           STLC.Term  (Term)
import qualified STLC.Term  as Term
import           STLC.Type  (Ty)
import qualified STLC.Type  as Ty
import           Util
import           Util.Happy

data Def' ty term f where
  Extrn ∷ f (String, Ty ty) → Def' ty term f
  Alias ∷ f (String, Ty ty) → Def' ty term f
  Named ∷ f (String, [String], Ty ty, Term ty term) → Def' ty term f

type Def = Def' Span Span (Pair Span)
