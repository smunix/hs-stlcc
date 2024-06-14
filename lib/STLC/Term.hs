{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE PatternSynonyms        #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE ViewPatterns           #-}

module STLC.Term where

import           CPrim
import qualified Data.Set  as Set
import           STLC.Type (Ty)
import qualified STLC.Type as Ty
import           Util

-- | The 'Term'' data type represents different forms of terms in our language.
data Term' ty f r where
  Prim'
    ∷ f (CPrim f)
    → Term' ty f r
    -- ^ 'Prim'' represents a primitive constant.
  Var'
    ∷ f String
    → Term' ty f r
    -- ^ 'Var'' represents a variable.
  Roll'
    ∷ f (Ty ty, r)
    → Term' ty f r
    -- ^ 'Roll'' represents a rolling operation which packages a value and its type.
  Unroll'
    ∷ f (Ty ty, r)
    → Term' ty f r
    -- ^ 'Unroll'' represents an unrolling operation which unpacks a value and its type.
  App'
    ∷ f (r, [r])
    → Term' ty f r
    -- ^ 'App'' represents an application of a function to a list of arguments.
  Let'
    ∷ f (String, r, r)
    → Term' ty f r
    -- ^ 'Let'' represents a let-binding, introducing a new variable.
  Variant'
    ∷ f (String, r, [(String, Ty ty)])
    → Term' ty f r
    -- ^ 'Variant'' represents a variant, which is a tagged union type.
  Case'
    ∷ f (r, [(String, String, r)])
    → Term' ty f r
    -- ^ 'Case'' represents a case analysis on a variant.
  Record'
    ∷ f [(String, r)]
    → Term' ty f r
    -- ^ 'Record'' represents a record, which is a collection of named fields.
  Project'
    ∷ f (r, String)
    → Term' ty f r
    -- ^ 'Project'' represents a projection from a record, accessing a specific field.
  Pack'
    ∷ f (r, Ty ty)
    → Term' ty f r
    -- ^ 'Pack'' represents packing a value with its type.
  Unpack'
    ∷ f (r, String, String, r)
    → Term' ty f r
    -- ^ 'Unpack'' represents unpacking a value with its type.
  Array'
    ∷ f [r]
    → Term' ty f r
    -- ^ 'Array'' represents an array of terms.
  Alloc'
    ∷ f (Ty ty, r)
    → Term' ty f r
    -- ^ 'Alloc'' represents allocation of memory for a term with a specific type.
  Index'
    ∷ f (r, r)
    → Term' ty f r
    -- ^ 'Index'' represents indexing into an array.
  deriving (Functor, Foldable)

type Term ∷ Type → Type → Type
type Term ty term = Fix (Term' ty (Note term))

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

instance View (Term' ty term) (Fix (Term' ty term)) where
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
  ⇒ Eq (Term' ty f r)

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
  ⇒ Ord (Term' ty f r)

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
  ⇒ Show (Term' ty f r)

-- Prim' ∷ f (CPrim f) → Term' ty f r
pattern Prim
  ∷ ∀ a term ty term' cprim
   . ( cprim ~ CPrim (Note a)
     , term' ~ Term' ty (Note a)
     , term ~ Term ty a
     , View term' term
     )
  ⇒ a
  → cprim
  → term
pattern Prim a cprim ← (project @term' → Prim' (view coerced → (a, cprim)))
  where
    Prim a cprim = inject @term' $ Prim' $ MkNote a cprim

-- Var' ∷ f String → Term' ty f r
pattern Var
  ∷ ∀ a term ty term' cprim
   . ( cprim ~ CPrim (Note a)
     , term' ~ Term' ty (Note a)
     , term ~ Term ty a
     , View term' term
     )
  ⇒ a
  → String
  → term
pattern Var a str ← (project @term' → Var' (view coerced → (a, str)))
  where
    Var a str = inject @term' $ Var' $ MkNote a str

-- Roll' ∷ f (Ty ty, r) → Term' ty f r
pattern Roll
  ∷ ∀ a term ty term' cprim
   . ( cprim ~ CPrim (Note a)
     , term' ~ Term' ty (Note a)
     , term ~ Term ty a
     , View term' term
     )
  ⇒ a
  → Ty ty
  → term
  → term
pattern Roll a ty term ← (project @term' → Roll' (view coerced → (a, (ty, term))))
  where
    Roll a ty term = inject @term' $ Roll' $ MkNote a (ty, term)

-- Unroll' ∷ f (Ty ty, r) → Term' ty f r
pattern Unroll
  ∷ ∀ a term ty term' cprim
   . ( cprim ~ CPrim (Note a)
     , term' ~ Term' ty (Note a)
     , term ~ Term ty a
     , View term' term
     )
  ⇒ a
  → Ty ty
  → term
  → term
pattern Unroll a ty term ← (project @term' → Unroll' (view coerced → (a, (ty, term))))
  where
    Unroll a ty term = inject @term' $ Unroll' $ MkNote a (ty, term)

-- App' ∷ f (r, [r]) → Term' ty f r
pattern App
  ∷ ∀ a term ty term' cprim
   . ( cprim ~ CPrim (Note a)
     , term' ~ Term' ty (Note a)
     , term ~ Term ty a
     , View term' term
     )
  ⇒ a
  → term
  → [term]
  → term
pattern App a fn args ←
  (project @term' → App' (view coerced → (a, (fn, args))))
  where
    App a fn args = inject @term' $ App' $ MkNote a (fn, args)

-- Let' ∷ f (String, r, r) → Term' ty f r
pattern Let
  ∷ ∀ a term ty term' cprim
   . ( cprim ~ CPrim (Note a)
     , term' ~ Term' ty (Note a)
     , term ~ Term ty a
     , View term' term
     )
  ⇒ a
  → String
  → term
  → term
  → term
pattern Let a str term body ←
  (project @term' → Let' (view coerced → (a, (str, term, body))))
  where
    Let a str term body = inject @term' $ Let' $ MkNote a (str, term, body)

-- Variant' ∷ f (String, r, [(String, Ty ty)]) → Term' ty f r
pattern Variant
  ∷ ∀ a term ty term' cprim
   . ( cprim ~ CPrim (Note a)
     , term' ~ Term' ty (Note a)
     , term ~ Term ty a
     , View term' term
     )
  ⇒ a
  → String
  → term
  → [(String, Ty ty)]
  → term
pattern Variant a str term row ←
  (project @term' → Variant' (view coerced → (a, (str, term, row))))
  where
    Variant a str term row = inject @term' $ Variant' $ MkNote a (str, term, row)

-- Case' ∷ f (r, [(String, String, r)]) → Term' ty f r
pattern Case
  ∷ ∀ a term ty term' cprim
   . ( cprim ~ CPrim (Note a)
     , term' ~ Term' ty (Note a)
     , term ~ Term ty a
     , View term' term
     )
  ⇒ a
  → term
  → [(String, String, term)]
  → term
pattern Case a scrtn branches ←
  (project @term' → Case' (view coerced → (a, (scrtn, branches))))
  where
    Case a scrtn branches = inject @term' $ Case' $ MkNote a (scrtn, branches)

-- Record' ∷ f [(String, r)] → Term' ty f r
pattern Record
  ∷ ∀ a term ty term' cprim
   . ( cprim ~ CPrim (Note a)
     , term' ~ Term' ty (Note a)
     , term ~ Term ty a
     , View term' term
     )
  ⇒ a
  → [(String, term)]
  → term
pattern Record a row ←
  (project @term' → Record' (view coerced → (a, row)))
  where
    Record a row = inject @term' $ Record' $ MkNote a row

-- Project' ∷ f (r, String) → Term' ty f r
pattern Project
  ∷ ∀ a term ty term' cprim
   . ( cprim ~ CPrim (Note a)
     , term' ~ Term' ty (Note a)
     , term ~ Term ty a
     , View term' term
     )
  ⇒ a
  → term
  → String
  → term
pattern Project a rcrd fld ←
  (project @term' → Project' (view coerced → (a, (rcrd, fld))))
  where
    Project a rcrd fld = inject @term' $ Project' $ MkNote a (rcrd, fld)

-- Pack' ∷ f (r, Ty ty) → Term' ty f r
pattern Pack
  ∷ ∀ a term ty term' cprim
   . ( cprim ~ CPrim (Note a)
     , term' ~ Term' ty (Note a)
     , term ~ Term ty a
     , View term' term
     )
  ⇒ a
  → term
  → Ty ty
  → term
pattern Pack a term ty ←
  (project @term' → Pack' (view coerced → (a, (term, ty))))
  where
    Pack a term ty = inject @term' $ Pack' $ MkNote a (term, ty)

-- Unpack' ∷ f (r, String, String, r) → Term' ty f r
pattern Unpack
  ∷ ∀ a term ty term' cprim
   . ( cprim ~ CPrim (Note a)
     , term' ~ Term' ty (Note a)
     , term ~ Term ty a
     , View term' term
     )
  ⇒ a
  → term
  → String
  → String
  → term
  → term
pattern Unpack a v vn ty b ←
  (project @term' → Unpack' (view coerced → (a, (v, vn, ty, b))))
  where
    Unpack a v vn ty b = inject @term' $ Unpack' $ MkNote a (v, vn, ty, b)

-- Array' ∷ f [r] → Term' ty f r
pattern Array
  ∷ ∀ a term ty term' cprim
   . ( cprim ~ CPrim (Note a)
     , term' ~ Term' ty (Note a)
     , term ~ Term ty a
     , View term' term
     )
  ⇒ a
  → [term]
  → term
pattern Array a terms ←
  (project @term' → Array' (view coerced → (a, terms)))
  where
    Array a terms = inject @term' $ Array' $ MkNote a terms

-- Alloc' ∷ f (Ty ty, r) → Term' ty f r
pattern Alloc
  ∷ ∀ a term ty term' cprim
   . ( cprim ~ CPrim (Note a)
     , term' ~ Term' ty (Note a)
     , term ~ Term ty a
     , View term' term
     )
  ⇒ a
  → Ty ty
  → term
  → term
pattern Alloc a ty term ← (project @term' → Alloc' (view coerced → (a, (ty, term))))
  where
    Alloc a ty term = inject @term' $ Alloc' $ MkNote a (ty, term)

-- Index' ∷ f (r, r) → Term' ty f r
pattern Index
  ∷ ∀ a term ty term' cprim
   . ( cprim ~ CPrim (Note a)
     , term' ~ Term' ty (Note a)
     , term ~ Term ty a
     , View term' term
     )
  ⇒ a
  → term
  → term
  → term
pattern Index a arr ndx ← (project @term' → Index' (view coerced → (a, (arr, ndx))))
  where
    Index a arr ndx = inject @term' $ Index' $ MkNote a (arr, ndx)

-- | 'fvs' computes the set of free variables in a given term.
fvs ∷ ∀ ty term. Term ty term → Set String
fvs = cata \case
  -- If the term is a variable, return a set with the variable's name.
  Var' (view _2 → x) → Set.singleton x
  -- If the term is a let-binding, return the union of free variables in the term and the body,
  -- excluding the bound variable.
  Let' (view _2 → (x, sans x → term, body)) → Set.union term body
  -- If the term is an unpack operation, return the union of free variables in the term and the body,
  -- excluding the bound variable.
  Unpack' (view _2 → (term, x, _, sans x → body)) → Set.union term body
  -- For all other terms, recursively collect free variables.
  term' → foldOf folded term'

-- | 'inferTy' infers the type of a given term.
inferTy
  ∷ ∀ tyEnv a term' term ty
   . ( term' ~ Term' a (Note a)
     , term ~ Fix term'
     , ty ~ Ty a
     , Eq a
     , Ty.Env tyEnv a
     )
  ⇒ tyEnv
  → Term a a
  → ty
inferTy = fix \rec tyEnv → para \case
  -- For primitive constants, infer the type from the primitive.
  Prim' (view _2 → prim) → Ty.fromC prim
  -- For variables, look up the type in the type environment.
  Var' (view _2 → x)
    | Just ty ← Ty.infer x tyEnv → ty
    | otherwise → error $ unwords ["undefined variable:", x]
  -- For rolling, infer the rolled type.
  Roll' (view _2 → (ty, (_, ty'))) → Ty.roll ty ty'
  -- For unrolling, infer the unrolled type.
  Unroll' (view _2 → (ty, (_, ty'))) → Ty.unroll ty ty'
  -- For function applications, infer the return type if the function type matches.
  App' (view _2 → ((_, fn), _))
    | Ty.Fun _ _ rty ← fn → rty
    | otherwise → error "expected a function application"
  -- For let-bindings, infer the type of the body in an extended type environment.
  Let' (view _2 → (x, (_, ty), (b, _))) → rec (Ty.push x ty tyEnv) b
  -- For variant types, infer the type from the tag and the row type.
  Variant' (view _1 &&& view _2 → (a, (_, _, row))) → Ty.Variant a row
  -- For case analysis, infer the type of the branches if the scrutiny type matches.
  Case' (view _2 → ((_, scrtnTy), headOf folded → branch))
    | Ty.Variant _ scrtnRow ← scrtnTy
    , Just (lbl, x, (term, _)) ← branch
    , Just (_, lblTy) ←
        ifindOf (folded % ifolded) (\str → const (str == lbl)) scrtnRow →
        rec (Ty.push x lblTy tyEnv) term
    | Ty.Variant _ Empty ← scrtnTy → error "unsupported empty case {}"
    | otherwise → error "unsupported case"
  -- For records, infer the type of each field.
  Record' (view _1 &&& view _2 → (a, fmap (_2 %~ view _2) → row)) → Ty.Record a row
  -- For projections, infer the type of the projected field.
  Project' (view _2 → ((_, recTy), lbl))
    | Ty.Record _ row ← recTy
    , Just (_, lblTy) ← ifindOf (folded % ifolded) (\x → const (x == lbl)) row →
        lblTy
    | otherwise → error $ unwords ["projection of lbl", lbl, "wasn't found"]
  -- For pack, return the type directly.
  Pack' (view _2 → (_, ty)) → ty
  -- For unpack, infer the type of the body in an extended type environment.
  Unpack' (view _2 → ((_, existsTy), x, tv, (bdy, _)))
    | Ty.Exists _ xE xTy ← existsTy →
        rec (Ty.push x (Ty.rename xE tv xTy) tyEnv) bdy
  -- For arrays, infer the element type.
  Array' (view _1 &&& view _2 → (a, (_, ty) :< _)) → Ty.Array a ty
  -- For allocation, infer the array type.
  Alloc' (view _1 &&& view _2 → (a, (ty, _))) → Ty.Array a ty
  -- For indexing, infer the element type if the array type matches.
  Index' (view _2 → ((_, arr), (_, ndx)))
    | Ty.Array _ eTy ← arr → eTy
    | otherwise → error "expected array"

-- | 'replace' substitutes a variable with a term within another term.
replace
  ∷ ∀ tn tyn term term' ty
   . ( term' ~ Term' tn (Note tyn)
     , term ~ Fix term'
     , ty ~ Ty tyn
     )
  ⇒ String
  → term
  → term
  → term
replace x0 term0 = para \case
  -- Replace a variable if it matches the target variable.
  Var' (view _2 → x) | x == x0 → term0
  -- Replace within let-bindings, only if the bound variable does not match the target variable.
  Let' (view _1 &&& view _2 → (tn, (x, v, b))) | x == x0 → Let tn x (v ^. _2) (b ^. _1)
  -- Replace within case branches, only if the bound variable does not match the target variable.
  Case' (view _1 &&& view _2 → (tn, (scrtn, branches))) → Case tn (scrtn ^. _2) (go <$> branches)
    where
      go (lbl, x, term)
        | x == x0 = (lbl, x, term ^. _1)
        | otherwise = (lbl, x, term ^. _2)

  -- Replace within unpack operations, only if the bound variable does not match the target variable.
  Unpack' (view _1 &&& view _2 → (tn, (v, vn, exists, b)))
    | x0 == vn → Unpack tn (v ^. _2) vn exists (b ^. _1)
    | otherwise → Unpack tn (v ^. _2) vn exists (b ^. _2)
  -- For all other terms, recursively apply replacement.
  term' → inject $ view _2 <$> term'

-- | 'expand' appies type substitution to expand inner types within a term.
expand ∷ Ty.Subst tyn → Term tyn tn → Term tyn tn
expand subst = cata \case
  -- Expand types within rolling operations.
  Roll' (view _1 &&& view _2 → (tn, (Ty.expand subst → ty, term))) → Roll tn ty term
  -- Expand types within unrolling operations.
  Unroll' (view _1 &&& view _2 → (tn, (Ty.expand subst → ty, term))) → Unroll tn ty term
  -- Expand types within variant types.
  Variant'
    (view _1 &&& view _2 → (tn, (lbl, term, fmap (second (Ty.expand subst)) → row))) → Variant tn lbl term row
  -- Expand types within pack operations.
  Pack' (view _1 &&& view _2 → (tn, (e, Ty.expand subst → ty))) → Pack tn e ty
  -- Expand types within allocation operations.
  Alloc' (view _1 &&& view _2 → (tn, (Ty.expand subst → ty, term))) → Alloc tn ty term
  -- For all other terms, recursively apply type expansion.
  term' → inject term'
