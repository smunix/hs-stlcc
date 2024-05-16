{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE PatternSynonyms        #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE ViewPatterns           #-}

module STLC.Term where

import           CPrim
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
  deriving (Functor, Foldable)

type Term ∷ Type → Type → Type
type Term ty term = Fix (TermF ty (Note term))

-- | a definition
data Def a where
  Def
    ∷ { _nameDef ∷ String
      , _argsDef ∷ [String]
      , _tyDef ∷ Ty a
      , _bodyDef ∷ Term a a
      }
    → Def a

makeLenses ''Def

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

-- PrimF ∷ f (CPrim f) → TermF ty f r
pattern Prim
  ∷ ∀ a term ty termF cprim
   . ( cprim ~ CPrim (Note a)
     , termF ~ TermF ty (Note a)
     , term ~ Term ty a
     , View termF term
     )
  ⇒ a
  → cprim
  → term
pattern Prim a cprim ← (project @termF → PrimF (view coerced → (a, cprim)))
  where
    Prim a cprim = inject @termF $ PrimF $ MkNote a cprim

-- VarF ∷ f String → TermF ty f r
pattern Var
  ∷ ∀ a term ty termF cprim
   . ( cprim ~ CPrim (Note a)
     , termF ~ TermF ty (Note a)
     , term ~ Term ty a
     , View termF term
     )
  ⇒ a
  → String
  → term
pattern Var a str ← (project @termF → VarF (view coerced → (a, str)))
  where
    Var a str = inject @termF $ VarF $ MkNote a str

-- RollF ∷ f (Ty ty, r) → TermF ty f r
pattern Roll
  ∷ ∀ a term ty termF cprim
   . ( cprim ~ CPrim (Note a)
     , termF ~ TermF ty (Note a)
     , term ~ Term ty a
     , View termF term
     )
  ⇒ a
  → Ty ty
  → term
  → term
pattern Roll a ty term ← (project @termF → RollF (view coerced → (a, (ty, term))))
  where
    Roll a ty term = inject @termF $ RollF $ MkNote a (ty, term)

-- UnrollF ∷ f (Ty ty, r) → TermF ty f r
pattern Unroll
  ∷ ∀ a term ty termF cprim
   . ( cprim ~ CPrim (Note a)
     , termF ~ TermF ty (Note a)
     , term ~ Term ty a
     , View termF term
     )
  ⇒ a
  → Ty ty
  → term
  → term
pattern Unroll a ty term ← (project @termF → UnrollF (view coerced → (a, (ty, term))))
  where
    Unroll a ty term = inject @termF $ UnrollF $ MkNote a (ty, term)

-- AppF ∷ f (r, [r]) → TermF ty f r
pattern App
  ∷ ∀ a term ty termF cprim
   . ( cprim ~ CPrim (Note a)
     , termF ~ TermF ty (Note a)
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
    App a fn args = inject @termF $ AppF $ MkNote a (fn, args)

-- LetF ∷ f (String, r, r) → TermF ty f r
pattern Let
  ∷ ∀ a term ty termF cprim
   . ( cprim ~ CPrim (Note a)
     , termF ~ TermF ty (Note a)
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
    Let a str term body = inject @termF $ LetF $ MkNote a (str, term, body)

-- VariantF ∷ f (String, r, [(String, Ty ty)]) → TermF ty f r
pattern Variant
  ∷ ∀ a term ty termF cprim
   . ( cprim ~ CPrim (Note a)
     , termF ~ TermF ty (Note a)
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
    Variant a str term row = inject @termF $ VariantF $ MkNote a (str, term, row)

-- CaseF ∷ f (r, [(String, String, r)]) → TermF ty f r
pattern Case
  ∷ ∀ a term ty termF cprim
   . ( cprim ~ CPrim (Note a)
     , termF ~ TermF ty (Note a)
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
    Case a scrtn branches = inject @termF $ CaseF $ MkNote a (scrtn, branches)

-- RecordF ∷ f [(String, r)] → TermF ty f r
pattern Record
  ∷ ∀ a term ty termF cprim
   . ( cprim ~ CPrim (Note a)
     , termF ~ TermF ty (Note a)
     , term ~ Term ty a
     , View termF term
     )
  ⇒ a
  → [(String, term)]
  → term
pattern Record a row ←
  (project @termF → RecordF (view coerced → (a, row)))
  where
    Record a row = inject @termF $ RecordF $ MkNote a row

-- ProjectF ∷ f (r, String) → TermF ty f r
pattern Project
  ∷ ∀ a term ty termF cprim
   . ( cprim ~ CPrim (Note a)
     , termF ~ TermF ty (Note a)
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
    Project a rcrd fld = inject @termF $ ProjectF $ MkNote a (rcrd, fld)

-- PackF ∷ f (r, Ty ty) → TermF ty f r
pattern Pack
  ∷ ∀ a term ty termF cprim
   . ( cprim ~ CPrim (Note a)
     , termF ~ TermF ty (Note a)
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
    Pack a term ty = inject @termF $ PackF $ MkNote a (term, ty)

-- UnpackF ∷ f (r, String, String, r) → TermF ty f r
pattern Unpack
  ∷ ∀ a term ty termF cprim
   . ( cprim ~ CPrim (Note a)
     , termF ~ TermF ty (Note a)
     , term ~ Term ty a
     , View termF term
     )
  ⇒ a
  → term
  → String
  → String
  → term
  → term
pattern Unpack a v vn ty b ←
  (project @termF → UnpackF (view coerced → (a, (v, vn, ty, b))))
  where
    Unpack a v vn ty b = inject @termF $ UnpackF $ MkNote a (v, vn, ty, b)

-- ArrayF ∷ f [r] → TermF ty f r
pattern Array
  ∷ ∀ a term ty termF cprim
   . ( cprim ~ CPrim (Note a)
     , termF ~ TermF ty (Note a)
     , term ~ Term ty a
     , View termF term
     )
  ⇒ a
  → [term]
  → term
pattern Array a terms ←
  (project @termF → ArrayF (view coerced → (a, terms)))
  where
    Array a terms = inject @termF $ ArrayF $ MkNote a terms

-- AllocF ∷ f (Ty ty, r) → TermF ty f r
pattern Alloc
  ∷ ∀ a term ty termF cprim
   . ( cprim ~ CPrim (Note a)
     , termF ~ TermF ty (Note a)
     , term ~ Term ty a
     , View termF term
     )
  ⇒ a
  → Ty ty
  → term
  → term
pattern Alloc a ty term ← (project @termF → AllocF (view coerced → (a, (ty, term))))
  where
    Alloc a ty term = inject @termF $ AllocF $ MkNote a (ty, term)

-- IndexF ∷ f (r, r) → TermF ty f r
pattern Index
  ∷ ∀ a term ty termF cprim
   . ( cprim ~ CPrim (Note a)
     , termF ~ TermF ty (Note a)
     , term ~ Term ty a
     , View termF term
     )
  ⇒ a
  → term
  → term
  → term
pattern Index a arr ndx ← (project @termF → IndexF (view coerced → (a, (arr, ndx))))
  where
    Index a arr ndx = inject @termF $ IndexF $ MkNote a (arr, ndx)

-- | Free variables of a term
fvs ∷ ∀ ty term. Term ty term → Set String
fvs = cata \case
  VarF (view _2 → x) → setOf folded [x]
  LetF (view _2 → (x, sans x → term, body)) → setOf (folded % folded) [term, body]
  UnpackF (view _2 → (term, x, _, sans x → body)) → setOf (folded % folded) [term, body]
  termF → foldOf folded termF

-- | type of a term
inferTy
  ∷ ∀ tyEnv a termF term ty
   . ( termF ~ TermF a (Note a)
     , term ~ Fix termF
     , ty ~ Ty a
     , Eq a
     , Ty.Env tyEnv a
     )
  ⇒ tyEnv
  → Term a a
  → ty
inferTy = fix \rec tyEnv → para \case
  PrimF (view _2 → prim) → Ty.fromC prim
  VarF (view _2 → x)
    | Just ty ← Ty.infer x tyEnv → ty
    | otherwise → error $ unwords ["undefined variable: ", x]
  RollF (view _2 → (ty, (_, ty'))) → Ty.roll ty ty'
  UnrollF (view _2 → (ty, (_, ty'))) → Ty.unroll ty ty'
  AppF (view _2 → ((_, fn), _)) -- TODO: smunix: no checks !
    | Ty.Fun _ _ rty ← fn → rty
    | otherwise → error $ unwords ["expected a function application"]
  LetF (view _2 → (x, (_, ty), (b, _))) → rec (Ty.push x ty tyEnv) b
  VariantF (view _1 &&& view _2 → (a, (_, _, row))) → Ty.Variant a row
  -- CaseF ∷ f (r, [(String, String, r)]) → TermF ty f r
  CaseF (view _2 → ((_, scrtnTy), headOf folded → branch))
    | Ty.Variant _ scrtnRow ← scrtnTy
    , Just (lbl, x, (term, _)) ← branch
    , Just (_, lblTy) ←
        ifindOf (folded % ifolded) (\str → const (str == lbl)) scrtnRow →
        rec (Ty.push x lblTy tyEnv) term
    | Ty.Variant _ Empty ← scrtnTy → error $ unwords ["unsupported empty case {}"]
    | otherwise → error $ unwords ["unsupported case"]
  -- RecordF ∷ f [(String, r)] → TermF ty f r
  RecordF (view _1 &&& view _2 → (a, fmap (_2 %~ (view _2)) → row)) → Ty.Record a row
  -- ProjectF ∷ f (r, String) → TermF ty f r
  ProjectF (view _2 → ((_, recTy), lbl))
    | Ty.Record _ row ← recTy
    , Just (_, lblTy) ← ifindOf (folded % ifolded) (\x → const (x == lbl)) row →
        lblTy
    | otherwise → error $ unwords ["projection of lbl ", lbl, " wasn't found"]
  -- PackF ∷ f (r, Ty ty) → TermF ty f r
  PackF (view _2 → (_, ty)) → ty
  -- UnpackF ∷ f (r, String, String, r) → TermF ty f r
  UnpackF (view _2 → ((_, existsTy), x, tv, (bdy, _)))
    | Ty.Exists _ xE xTy ← existsTy →
        rec (Ty.push x (Ty.rename xE tv xTy) tyEnv) bdy
  -- ArrayF ∷ f [r] → TermF ty f r
  ArrayF (view _1 &&& view _2 → (a, ((_, ty) :< _))) → Ty.Array a ty
  -- AllocF ∷ f (Ty ty, r) → TermF ty f r
  AllocF (view _1 &&& view _2 → (a, (ty, _))) → Ty.Array a ty
  -- IndexF ∷ f (r, r) → TermF ty f r
  IndexF (view _2 → ((_, arr), (_, ndx)))
    | Ty.Array _ eTy ← arr → eTy
    | otherwise → error $ unwords ["expected array"]

-- | substitute a variable with a term
replace
  ∷ ∀ tn tyn term termF ty
   . ( termF ~ TermF tn (Note tyn)
     , term ~ Fix termF
     , ty ~ Ty tyn
     )
  ⇒ String
  → term
  → term
  → term
replace x0 term0 = para \case
  -- VarF ∷ f String → TermF ty f r
  VarF (view _2 → x) | x == x0 → term0
  -- LetF ∷ f (String, r, r) → TermF ty f r
  LetF (view _1 &&& view _2 → (tn, (x, v, b))) | x == x0 → Let tn x (v ^. _2) (b ^. _1)
  -- CaseF ∷ f (r, [(String, String, r)]) → TermF ty f r
  CaseF (view _1 &&& view _2 → (tn, (scrtn, branches))) → Case tn (scrtn ^. _2) (go <$> branches)
    where
      go (lbl, x, term)
        | x == x0 = (lbl, x, term ^. _1)
        | otherwise = (lbl, x, term ^. _2)
  -- UnpackF ∷ f (r, String, String, r) → TermF ty f r
  UnpackF (view _1 &&& view _2 → (tn, (v, vn, exists, b)))
    | x0 == vn → Unpack tn (v ^. _2) vn exists (b ^. _1)
    | otherwise → Unpack tn (v ^. _2) vn exists (b ^. _2)
  termF → inject $ view _2 <$> termF

-- | expand inner types
expand ∷ Ty.Frame tyn → Term tyn tn → Term tyn tn
expand subst = cata \case
  RollF (view _1 &&& view _2 → (tn, (Ty.expand subst → ty, term))) → Roll tn ty term
  UnrollF (view _1 &&& view _2 → (tn, (Ty.expand subst → ty, term))) → Unroll tn ty term
  VariantF
    (view _1 &&& view _2 → (tn, (lbl, term, fmap (second (Ty.expand subst)) → row))) → Variant tn lbl term row
  PackF (view _1 &&& view _2 → (tn, (e, Ty.expand subst → ty))) → Pack tn e ty
  AllocF (view _1 &&& view _2 → (tn, (Ty.expand subst → ty, term))) → Alloc tn ty term
  termF → inject $ termF
