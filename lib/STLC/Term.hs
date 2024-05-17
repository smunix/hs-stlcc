{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE PatternSynonyms        #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE ViewPatterns           #-}

module STLC.Term where

import           CPrim
import qualified STLC.Type as Ty
import           STLC.Type (Ty)
import           Util

import qualified Data.Set  as Set

-- | The 'TermF' data type represents different forms of terms in our language.
data TermF ty f r where
  -- | 'PrimF' represents a primitive constant.
  PrimF    :: f (CPrim f) -> TermF ty f r

  -- | 'VarF' represents a variable.
  VarF     :: f String -> TermF ty f r

  -- | 'RollF' represents a rolling operation which packages a value and its type.
  RollF    :: f (Ty ty, r) -> TermF ty f r

  -- | 'UnrollF' represents an unrolling operation which unpacks a value and its type.
  UnrollF  :: f (Ty ty, r) -> TermF ty f r

  -- | 'AppF' represents an application of a function to a list of arguments.
  AppF     :: f (r, [r]) -> TermF ty f r

  -- | 'LetF' represents a let-binding, introducing a new variable.
  LetF     :: f (String, r, r) -> TermF ty f r

  -- | 'VariantF' represents a variant, which is a tagged union type.
  VariantF :: f (String, r, [(String, Ty ty)]) -> TermF ty f r

  -- | 'CaseF' represents a case analysis on a variant.
  CaseF    :: f (r, [(String, String, r)]) -> TermF ty f r

  -- | 'RecordF' represents a record, which is a collection of named fields.
  RecordF  :: f [(String, r)] -> TermF ty f r

  -- | 'ProjectF' represents a projection from a record, accessing a specific field.
  ProjectF :: f (r, String) -> TermF ty f r

  -- | 'PackF' represents packing a value with its type.
  PackF    :: f (r, Ty ty) -> TermF ty f r

  -- | 'UnpackF' represents unpacking a value with its type.
  UnpackF  :: f (r, String, String, r) -> TermF ty f r

  -- | 'ArrayF' represents an array of terms.
  ArrayF   :: f [r] -> TermF ty f r

  -- | 'AllocF' represents allocation of memory for a term with a specific type.
  AllocF   :: f (Ty ty, r) -> TermF ty f r

  -- | 'IndexF' represents indexing into an array.
  IndexF   :: f (r, r) -> TermF ty f r

  -- | The 'Functor' and 'Foldable' instances are derived for 'TermF'.
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


-- | 'fvs' computes the set of free variables in a given term.
fvs ∷ ∀ ty term. Term ty term → Set String
fvs = cata \case
  -- If the term is a variable, return a set with the variable's name.
  VarF (view _2 → x) → Set.singleton x

  -- If the term is a let-binding, return the union of free variables in the term and the body,
  -- excluding the bound variable.
  LetF (view _2 → (x, sans x → term, body)) → Set.union term body

  -- If the term is an unpack operation, return the union of free variables in the term and the body,
  -- excluding the bound variable.
  UnpackF (view _2 → (term, x, _, sans x → body)) → Set.union term body

  -- For all other terms, recursively collect free variables.
  termF → foldMap id termF

-- | 'inferTy' infers the type of a given term.
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
  -- For primitive constants, infer the type from the primitive.
  PrimF (view _2 → prim) → Ty.fromC prim

  -- For variables, look up the type in the type environment.
  VarF (view _2 → x)
    | Just ty ← Ty.infer x tyEnv → ty
    | otherwise → error $ unwords ["undefined variable:", x]

  -- For rolling, infer the rolled type.
  RollF (view _2 → (ty, (_, ty'))) → Ty.roll ty ty'

  -- For unrolling, infer the unrolled type.
  UnrollF (view _2 → (ty, (_, ty'))) → Ty.unroll ty ty'

  -- For function applications, infer the return type if the function type matches.
  AppF (view _2 → ((_, fn), _))
    | Ty.Fun _ _ rty ← fn → rty
    | otherwise → error "expected a function application"

  -- For let-bindings, infer the type of the body in an extended type environment.
  LetF (view _2 → (x, (_, ty), (b, _))) → rec (Ty.push x ty tyEnv) b

  -- For variant types, infer the type from the tag and the row type.
  VariantF (view _1 &&& view _2 → (a, (_, _, row))) → Ty.Variant a row

  -- For case analysis, infer the type of the branches if the scrutiny type matches.
  CaseF (view _2 → ((_, scrtnTy), headOf folded → branch))
    | Ty.Variant _ scrtnRow ← scrtnTy
    , Just (lbl, x, (term, _)) ← branch
    , Just (_, lblTy) ← ifindOf (folded % ifolded) (\str → const (str == lbl)) scrtnRow →
        rec (Ty.push x lblTy tyEnv) term
    | Ty.Variant _ Empty ← scrtnTy → error "unsupported empty case {}"
    | otherwise → error "unsupported case"

  -- For records, infer the type of each field.
  RecordF (view _1 &&& view _2 → (a, fmap (_2 %~ (view _2)) → row)) → Ty.Record a row

  -- For projections, infer the type of the projected field.
  ProjectF (view _2 → ((_, recTy), lbl))
    | Ty.Record _ row ← recTy
    , Just (_, lblTy) ← ifindOf (folded % ifolded) (\x → const (x == lbl)) row →
        lblTy
    | otherwise → error $ unwords ["projection of lbl", lbl, "wasn't found"]

  -- For pack, return the type directly.
  PackF (view _2 → (_, ty)) → ty

  -- For unpack, infer the type of the body in an extended type environment.
  UnpackF (view _2 → ((_, existsTy), x, tv, (bdy, _)))
    | Ty.Exists _ xE xTy ← existsTy →
        rec (Ty.push x (Ty.rename xE tv xTy) tyEnv) bdy

  -- For arrays, infer the element type.
  ArrayF (view _1 &&& view _2 → (a, ((_, ty) :< _))) → Ty.Array a ty

  -- For allocation, infer the array type.
  AllocF (view _1 &&& view _2 → (a, (ty, _))) → Ty.Array a ty

  -- For indexing, infer the element type if the array type matches.
  IndexF (view _2 → ((_, arr), (_, ndx)))
    | Ty.Array _ eTy ← arr → eTy
    | otherwise → error "expected array"

-- | 'replace' substitutes a variable with a term within another term.
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
  -- Replace a variable if it matches the target variable.
  VarF (view _2 → x) | x == x0 → term0

  -- Replace within let-bindings, only if the bound variable does not match the target variable.
  LetF (view _1 &&& view _2 → (tn, (x, v, b))) | x == x0 → Let tn x (v ^. _2) (b ^. _1)

  -- Replace within case branches, only if the bound variable does not match the target variable.
  CaseF (view _1 &&& view _2 → (tn, (scrtn, branches))) → Case tn (scrtn ^. _2) (go <$> branches)
    where
      go (lbl, x, term)
        | x == x0 = (lbl, x, term ^. _1)
        | otherwise = (lbl, x, term ^. _2)

  -- Replace within unpack operations, only if the bound variable does not match the target variable.
  UnpackF (view _1 &&& view _2 → (tn, (v, vn, exists, b)))
    | x0 == vn → Unpack tn (v ^. _2) vn exists (b ^. _1)
    | otherwise → Unpack tn (v ^. _2) vn exists (b ^. _2)

  -- For all other terms, recursively apply replacement.
  termF → inject $ view _2 <$> termF

-- | 'expand' applies type substitution to expand inner types within a term.
expand ∷ Ty.Subst tyn → Term tyn tn → Term tyn tn
expand subst = cata \case
  -- Expand types within rolling operations.
  RollF (view _1 &&& view _2 → (tn, (Ty.expand subst → ty, term))) → Roll tn ty term

  -- Expand types within unrolling operations.
  UnrollF (view _1 &&& view _2 → (tn, (Ty.expand subst → ty, term))) → Unroll tn ty term

  -- Expand types within variant types.
  VariantF
    (view _1 &&& view _2 → (tn, (lbl, term, fmap (second (Ty.expand subst)) → row))) → Variant tn lbl term row

  -- Expand types within pack operations.
  PackF (view _1 &&& view _2 → (tn, (e, Ty.expand subst → ty))) → Pack tn e ty

  -- Expand types within allocation operations.
  AllocF (view _1 &&& view _2 → (tn, (Ty.expand subst → ty, term))) → Alloc tn ty term

  -- For all other terms, recursively apply type expansion.
  termF → inject $ termF
