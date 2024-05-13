{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE PatternSynonyms        #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE ViewPatterns           #-}

module STLC.Term where

import           CPrim
import           Optics
import           STLC.Type (Ty)
import qualified STLC.Type as Ty
import           Util

data TermF ty f r where
  PrimF ∷ f (CPrim f) → TermF ty f r
  VarF ∷ f String → TermF ty f r
  RollF ∷ f (Ty ty, r) → TermF ty f r
  UnrollF ∷ f (Ty ty, r) → TermF ty f r
  AppF ∷ f (r, [r]) → TermF ty f r
  LetF ∷ f (String, r, r) → TermF ty f r
  VariantF ∷ f (String, r, [(String, Ty ty)]) → TermF ty f r
  CaseF ∷ f (r, [(String, String, r)]) → TermF ty f r
  RecordF ∷ f [(String, r)] → TermF ty f r
  ProjectF ∷ f (r, String) → TermF ty f r
  PackF ∷ f (r, Ty ty) → TermF ty f r
  UnpackF ∷ f (r, String, String, r) → TermF ty f r
  ArrayF ∷ f [r] → TermF ty f r
  AllocF ∷ f (Ty ty, r) → TermF ty f r
  IndexF ∷ f (r, r) → TermF ty f r

type Term ∷ Type → Type → Type
type Term ty term = Fix (TermF ty (Pair term))

instance View (TermF ty term) (Fix (TermF ty term)) where
  project = unFix
  inject = Fix

deriving instance
  ( Eq (f (r, String, String, r))
  , Eq (f (String, r, r))
  , Eq (f (String, r, [(String, Ty ty)]))
  , Eq (f (r, r))
  , Eq (f (r, [r]))
  , Eq (f (r, [(String, String, r)]))
  , Eq (f (r, String))
  , Eq (f (r, Ty ty))
  , Eq (f (Ty ty, r))
  , Eq (f (CPrim f))
  , Eq (f [r])
  , Eq (f [(String, r)])
  , Eq (f String)
  )
  ⇒ Eq (TermF ty f r)

deriving instance
  ( Ord (f (r, String, String, r))
  , Ord (f (String, r, r))
  , Ord (f (String, r, [(String, Ty ty)]))
  , Ord (f (r, r))
  , Ord (f (r, [r]))
  , Ord (f (r, [(String, String, r)]))
  , Ord (f (r, String))
  , Ord (f (r, Ty ty))
  , Ord (f (Ty ty, r))
  , Ord (f (CPrim f))
  , Ord (f [r])
  , Ord (f [(String, r)])
  , Ord (f String)
  )
  ⇒ Ord (TermF ty f r)

deriving instance
  ( Show (f (r, String, String, r))
  , Show (f (String, r, r))
  , Show (f (String, r, [(String, Ty ty)]))
  , Show (f (r, r))
  , Show (f (r, [r]))
  , Show (f (r, [(String, String, r)]))
  , Show (f (r, String))
  , Show (f (r, Ty ty))
  , Show (f (Ty ty, r))
  , Show (f (CPrim f))
  , Show (f [r])
  , Show (f [(String, r)])
  , Show (f String)
  )
  ⇒ Show (TermF ty f r)

pattern Prim
  ∷ ∀ a term ty termF cprim
   . ( cprim ~ CPrim (Pair a)
     , termF ~ TermF ty (Pair a)
     , term ~ Term ty a
     , View termF term
     )
  ⇒ a
  → cprim
  → term
pattern Prim a cprim ← (project @termF → PrimF (view coerced → (a, cprim)))
  where
    Prim a cprim = inject @termF $ PrimF $ MkPair a cprim

pattern Var
  ∷ ∀ a term ty termF cprim
   . ( cprim ~ CPrim (Pair a)
     , termF ~ TermF ty (Pair a)
     , term ~ Term ty a
     , View termF term
     )
  ⇒ a
  → String
  → term
pattern Var a str ← (project @termF → VarF (view coerced → (a, str)))
  where
    Var a str = inject @termF $ VarF $ MkPair a str

pattern Roll
  ∷ ∀ a term ty termF cprim
   . ( cprim ~ CPrim (Pair a)
     , termF ~ TermF ty (Pair a)
     , term ~ Term ty a
     , View termF term
     )
  ⇒ a
  → Ty ty
  → term
  → term
pattern Roll a ty term ← (project @termF → RollF (view coerced → (a, (ty, term))))
  where
    Roll a ty term = inject @termF $ RollF $ MkPair a (ty, term)

pattern Unroll
  ∷ ∀ a term ty termF cprim
   . ( cprim ~ CPrim (Pair a)
     , termF ~ TermF ty (Pair a)
     , term ~ Term ty a
     , View termF term
     )
  ⇒ a
  → Ty ty
  → term
  → term
pattern Unroll a ty term ← (project @termF → UnrollF (view coerced → (a, (ty, term))))
  where
    Unroll a ty term = inject @termF $ UnrollF $ MkPair a (ty, term)

pattern App
  ∷ ∀ a term ty termF cprim
   . ( cprim ~ CPrim (Pair a)
     , termF ~ TermF ty (Pair a)
     , term ~ Term ty a
     , View termF term
     )
  ⇒ a
  → term
  → [term]
  → term
pattern App a fn args ←
  (project @termF → AppF (view coerced → (a, (fn, args))))
  where
    App a fn args = inject @termF $ AppF $ MkPair a (fn, args)

pattern Let
  ∷ ∀ a term ty termF cprim
   . ( cprim ~ CPrim (Pair a)
     , termF ~ TermF ty (Pair a)
     , term ~ Term ty a
     , View termF term
     )
  ⇒ a
  → String
  → term
  → term
  → term
pattern Let a str term body ←
  (project @termF → LetF (view coerced → (a, (str, term, body))))
  where
    Let a str term body = inject @termF $ LetF $ MkPair a (str, term, body)

-- VariantF ∷ f (String, r, [(String, Ty ty)]) → TermF ty f r
pattern Variant
  ∷ ∀ a term ty termF cprim
   . ( cprim ~ CPrim (Pair a)
     , termF ~ TermF ty (Pair a)
     , term ~ Term ty a
     , View termF term
     )
  ⇒ a
  → String
  → term
  → [(String, Ty ty)]
  → term
pattern Variant a str term row ←
  (project @termF → VariantF (view coerced → (a, (str, term, row))))
  where
    Variant a str term row = inject @termF $ VariantF $ MkPair a (str, term, row)

-- CaseF ∷ f (r, [(String, String, r)]) → TermF ty f r
pattern Case
  ∷ ∀ a term ty termF cprim
   . ( cprim ~ CPrim (Pair a)
     , termF ~ TermF ty (Pair a)
     , term ~ Term ty a
     , View termF term
     )
  ⇒ a
  → term
  → [(String, String, term)]
  → term
pattern Case a scrtn branches ←
  (project @termF → CaseF (view coerced → (a, (scrtn, branches))))
  where
    Case a scrtn branches = inject @termF $ CaseF $ MkPair a (scrtn, branches)

-- RecordF ∷ f [(String, r)] → TermF ty f r
pattern Record
  ∷ ∀ a term ty termF cprim
   . ( cprim ~ CPrim (Pair a)
     , termF ~ TermF ty (Pair a)
     , term ~ Term ty a
     , View termF term
     )
  ⇒ a
  → [(String, term)]
  → term
pattern Record a row ←
  (project @termF → RecordF (view coerced → (a, row)))
  where
    Record a row = inject @termF $ RecordF $ MkPair a row

-- ProjectF ∷ f (r, String) → TermF ty f r
pattern Project
  ∷ ∀ a term ty termF cprim
   . ( cprim ~ CPrim (Pair a)
     , termF ~ TermF ty (Pair a)
     , term ~ Term ty a
     , View termF term
     )
  ⇒ a
  → term
  → String
  → term
pattern Project a rcrd fld ←
  (project @termF → ProjectF (view coerced → (a, (rcrd, fld))))
  where
    Project a rcrd fld = inject @termF $ ProjectF $ MkPair a (rcrd, fld)

-- PackF ∷ f (r, Ty ty) → TermF ty f r
pattern Pack
  ∷ ∀ a term ty termF cprim
   . ( cprim ~ CPrim (Pair a)
     , termF ~ TermF ty (Pair a)
     , term ~ Term ty a
     , View termF term
     )
  ⇒ a
  → term
  → Ty ty
  → term
pattern Pack a term ty ←
  (project @termF → PackF (view coerced → (a, (term, ty))))
  where
    Pack a term ty = inject @termF $ PackF $ MkPair a (term, ty)

-- UnpackF ∷ f (r, String, String, r) → TermF ty f r
-- ArrayF ∷ f [r] → TermF ty f r
pattern Array
  ∷ ∀ a term ty termF cprim
   . ( cprim ~ CPrim (Pair a)
     , termF ~ TermF ty (Pair a)
     , term ~ Term ty a
     , View termF term
     )
  ⇒ a
  → [term]
  → term
pattern Array a terms ←
  (project @termF → ArrayF (view coerced → (a, terms)))
  where
    Array a terms = inject @termF $ ArrayF $ MkPair a terms

-- AllocF ∷ f (Ty ty, r) → TermF ty f r
pattern Alloc
  ∷ ∀ a term ty termF cprim
   . ( cprim ~ CPrim (Pair a)
     , termF ~ TermF ty (Pair a)
     , term ~ Term ty a
     , View termF term
     )
  ⇒ a
  → Ty ty
  → term
  → term
pattern Alloc a ty term ← (project @termF → AllocF (view coerced → (a, (ty, term))))
  where
    Alloc a ty term = inject @termF $ AllocF $ MkPair a (ty, term)

-- IndexF ∷ f (r, r) → TermF ty f r
pattern Index
  ∷ ∀ a term ty termF cprim
   . ( cprim ~ CPrim (Pair a)
     , termF ~ TermF ty (Pair a)
     , term ~ Term ty a
     , View termF term
     )
  ⇒ a
  → term
  → term
  → term
pattern Index a arr ndx ← (project @termF → IndexF (view coerced → (a, (arr, ndx))))
  where
    Index a arr ndx = inject @termF $ IndexF $ MkPair a (arr, ndx)
