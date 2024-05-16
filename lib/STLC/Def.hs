module STLC.Def where

import           Optics
import           STLC.Term  (Term)
import qualified STLC.Term  as Term
import           STLC.Type  (Ty)
import qualified STLC.Type  as Ty
import           Util
import           Util.Happy

data Definition' ty term f where
  Extrn ∷ f (String, Ty ty) → Definition' ty term f
  Alias ∷ f (String, Ty ty) → Definition' ty term f
  Named ∷ f (String, [String], Ty ty, Term ty term) → Definition' ty term f

type Definition = Definition' Span Span (Note Span)
