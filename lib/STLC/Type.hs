{-# LANGUAGE DeriveFoldable         #-}
{-# LANGUAGE DeriveFunctor          #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE PatternSynonyms        #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE ViewPatterns           #-}

module STLC.Type where

import           CPrim
import           Data.Set.Optics
import           Optics
import           Util

-- | Type representations using Generalized Algebraic Data Types (GADTs)
type Ty' ∷ (Type → Type) → Type → Type
data Ty' f r where
  Prim'
    ∷ f String
    → Ty' f r
    -- ^ Primitive type, represented by a string
  Var'
    ∷ f String
    → Ty' f r
    -- ^ Type variable, represented by a string
  Fun'
    ∷ f ([r], r)
    → Ty' f r
    -- ^ Function type, represented by a list of argument types and a return type
  Variant'
    ∷ f [(String, r)]
    → Ty' f r
    -- ^ Variant type, represented by a list of (label, type) pairs
  Record'
    ∷ f [(String, r)]
    → Ty' f r
    -- ^ Record type, represented by a list of (label, type) pairs
  Exists'
    ∷ f (String, r)
    → Ty' f r
    -- ^ Existential type, represented by a (bound variable, type) pair
  Array'
    ∷ f r
    → Ty' f r
    -- ^ Array type, represented by an element type
  Mu'
    ∷ f (String, r)
    → Ty' f r
    -- ^ Recursive type, represented by a (bound variable, type) pair
  deriving (Functor, Foldable)

-- | Equality instance for 'Ty''
deriving instance
  ( Eq a
  , Eq (f a)
  , Eq (f ([a], a))
  , Eq (f (String, a))
  , Eq (f [(String, a)])
  , Eq (f String)
  )
  ⇒ Eq (Ty' f a)

-- | Ordering instance for 'Ty''
deriving instance
  ( Ord a
  , Ord (f a)
  , Ord (f ([a], a))
  , Ord (f (String, a))
  , Ord (f [(String, a)])
  , Ord (f String)
  )
  ⇒ Ord (Ty' f a)

-- | Show instance for 'Ty''
deriving instance
  ( Show a
  , Show (f a)
  , Show (f ([a], a))
  , Show (f (String, a))
  , Show (f [(String, a)])
  , Show (f String)
  )
  ⇒ Show (Ty' f a)

-- | Type environments
class (AsEmpty env) ⇒ Env env a | env → a where
  -- | Check if a variable is defined at the top level
  isTopLevel ∷ String → env → Maybe (Ty a)

  -- | Infer the type of a variable
  infer ∷ String → env → Maybe (Ty a)

  -- | Push multiple (variable, type) pairs onto the environment
  pushN ∷ [(String, Ty a)] → env → env

  -- | Push a single (variable, type) pair onto the environment
  push ∷ String → Ty a → env → env
  push x ty = pushN [(x, ty)]

  -- | Push multiple (variable, type) pairs onto the top level of the environment
  pushTopN ∷ [(String, Ty a)] → env → env

  -- | Push a single (variable, type) pair onto the top level of the environment
  pushTop ∷ String → Ty a → env → env
  pushTop x ty = pushTopN [(x, ty)]

  -- | Get all variables from the environment
  vars ∷ env → [String]

  -- | Map a function over the environment
  mapEnv ∷ (String → Ty a → Ty a) → env → env

  -- | Update the type of a variable in the environment
  update ∷ String → Fn (Ty a) (Ty a) → env → env

-- | A function frame, representing a mapping of variable names to types
type Frame a = [(String, Ty a)]

-- | A type substitution, representing a mapping of variable names to types
type Subst a = [(String, Ty a)]

-- | A type environment, represented as a list of frames
type TyEnv a = [Frame a]

-- | Type alias for types, parameterized by 'ty'
type Ty ∷ Type → Type
type Ty ty = Fix (Ty' (Note ty))

-- | Instance of the 'Env' class for 'TyEnv'
instance Env (TyEnv a) a where
  isTopLevel x = fix \rec → \case
    -- Check if the variable is in the topmost frame
    fr :< Empty → ifindOf (folded % ifolded) (\x' → const $ x' == x) fr <&> view _2
    -- Recursively check the rest of the frames
    fr :< frs
      | Just {} ← ifindOf (folded % ifolded) (\x' → const $ x' == x) fr → Empty
      | otherwise → rec frs
    _other → Nothing

  infer x = fix \rec → \case
    -- Check if the variable is in the current frame
    fr :< frs
      | Just (_, ty) ← ifindOf (folded % ifolded) (\x' → const $ x' == x) fr → Just ty
      | otherwise → rec frs

  -- Push a frame onto the environment
  pushN fr = (fr :<)

  -- Push definitions onto the top level of the environment
  pushTopN defs = ($ id) $ fix \rec kont → \case
    Empty → kont [defs]
    fr :< Empty → kont [fr <> defs]
    fr :< frs → rec ((fr :<) .> kont) frs

  -- Get all variable names from the environment
  vars =
    ifoldrOf
      (folded % folded % ifolded)
      (\x → const (x :<))
      Empty

  -- Map a function over the environment
  mapEnv fn =
    fmap $
      ifoldrOf
        (folded % ifolded)
        (\x (fn x → ty) → ((x, ty) :<))
        Empty

  -- Update the type of a variable in the environment
  update x fn =
    fmap $
      ifoldrOf
        (folded % ifolded)
        (\x' ty@(fn → ty') → ((if x == x' then (x, ty') else (x, ty)) :<))
        Empty

-- | View instance for 'Ty''
instance View (Ty' ty) (Fix (Ty' ty)) where
  project = unFix
  inject = Fix

-- | Annotation instance for 'Ty'
instance Ann (Ty a) a where
  ann = lens get' (flip set')
    where
      -- \| Set the annotation
      set' a = cata \case
        Prim' f → inject $ Prim' $ set _1 a f
        Var' f → inject $ Var' $ set _1 a f
        Fun' f → inject $ Fun' $ set _1 a f
        Variant' f → inject $ Variant' $ set _1 a f
        Record' f → inject $ Record' $ set _1 a f
        Exists' f → inject $ Exists' $ set _1 a f
        Array' f → inject $ Array' $ set _1 a f
        Mu' f → inject $ Mu' $ set _1 a f

      -- \| Get the annotation
      get' = cata \case
        Prim' f → f ^. _1
        Var' f → f ^. _1
        Fun' f → f ^. _1
        Variant' f → f ^. _1
        Record' f → f ^. _1
        Exists' f → f ^. _1
        Array' f → f ^. _1
        Mu' f → f ^. _1

  -- \| Get all annotations
  anns = to $ cata \case
    Prim' (view _1 .> pure → a) → a
    Var' (view _1 .> pure → a) → a
    Fun' f@(view _1 .> pure → a) → foldOf folded [a, args, ret]
      where
        args = f & foldOf (folded % _1 % folded)
        ret = f & foldOf (folded % folded)
    Variant' f@(view _1 .> pure → a) → foldOf folded [a, row f]
    Record' f@(view _1 .> pure → a) → foldOf folded [a, row f]
    Exists' f@(view _1 .> pure → a) → foldOf folded [a, exists f]
    Array' f@(view _1 .> pure → a) → foldOf folded [a, array f]
    Mu' f@(view _1 .> pure → a) → foldOf folded [a, mu f]
    where
      row = foldOf (folded % folded % folded)
      exists = foldOf (folded % folded)
      array = foldOf folded
      mu = foldOf (folded % folded)

pattern Prim
  ∷ ∀ a f ty. (f ~ Ty' (Note a), ty ~ Ty a, View f ty) ⇒ a → String → ty
pattern Prim a str ← (project @f → Prim' (view coerced → (a, str)))
  where
    Prim a str
      | Just ty ← prim a str = ty
      | otherwise = error $ unwords [str, " is not a primitive type"]

pattern Var
  ∷ ∀ a f ty. (f ~ Ty' (Note a), ty ~ Ty a, View f ty) ⇒ a → String → ty
pattern Var a str ← (project @f → Var' (view coerced → (a, str)))
  where
    Var a str = inject $ Var' $ MkNote a str

pattern Fun
  ∷ ∀ a f ty. (f ~ Ty' (Note a), ty ~ Ty a, View f ty) ⇒ a → [ty] → ty → ty
pattern Fun a args ret ← (project @f → Fun' (view coerced → (a, (args, ret))))
  where
    Fun a args ret = inject $ Fun' $ MkNote a (args, ret)

pattern Variant
  ∷ ∀ a f ty. (f ~ Ty' (Note a), ty ~ Ty a, View f ty) ⇒ a → [(String, ty)] → ty
pattern Variant a row ← (project @f → Variant' (view coerced → (a, row)))
  where
    Variant a row = inject $ Variant' $ MkNote a row

pattern Record
  ∷ ∀ a f ty. (f ~ Ty' (Note a), ty ~ Ty a, View f ty) ⇒ a → [(String, ty)] → ty
pattern Record a row ← (project @f → Record' (view coerced → (a, row)))
  where
    Record a row = inject $ Record' $ MkNote a row

pattern Exists
  ∷ ∀ a f ty. (f ~ Ty' (Note a), ty ~ Ty a, View f ty) ⇒ a → String → ty → ty
pattern Exists a str ty ←
  (project @f → Exists' (view coerced → (a, (str, ty))))
  where
    Exists a str ty = inject $ Exists' $ MkNote a (str, ty)

pattern Array
  ∷ ∀ a f ty. (f ~ Ty' (Note a), ty ~ Ty a, View f ty) ⇒ a → ty → ty
pattern Array a ty ← (project @f → Array' (view coerced → (a, ty)))
  where
    Array a ty = inject $ Array' $ MkNote a ty

pattern Mu
  ∷ ∀ a f ty. (f ~ Ty' (Note a), ty ~ Ty a, View f ty) ⇒ a → String → ty → ty
pattern Mu a str ty ←
  (project @f → Mu' (view _1 &&& view _2 → (a, (str, ty))))
  where
    Mu a str ty = inject $ Mu' $ MkNote a (str, ty)

-- | This function checks if a given string represents a primitive type.
-- | If it does, it returns the corresponding type wrapped in a 'Just'.
-- | Otherwise, it returns 'Nothing'.
prim ∷ a → String → Maybe (Ty a)
prim a x
  -- Check if the string 'x' is one of the primitive types
  | elemOf folded x $
      setOf folded ["unit", "byte", "char", "short", "int", "float", "string"] =
      -- If it is, wrap it in a 'Prim'' constructor and return it
      Just $ inject $ Prim' $ MkNote a x
  -- If 'x' is not a primitive type, return 'Nothing'
  | otherwise = Empty

-- | This function converts a primitive constant ('CPrim') to a type ('Ty').
fromPrim
  ∷ ( Ann (f ()) a
    , Ann (f Word8) a
    , Ann (f Char) a
    , Ann (f Int) a
    , Ann (f Float) a
    , Ann (f String) a
    )
  ⇒ CPrim f
  → Ty a
fromPrim = fromC

-- | This function maps each 'CPrim' constructor to its corresponding type representation.
fromC
  ∷ ( Ann (f ()) a
    , Ann (f Word8) a
    , Ann (f Char) a
    , Ann (f Int) a
    , Ann (f Float) a
    , Ann (f String) a
    )
  ⇒ CPrim f
  → Ty a
fromC = \case
  -- Map each 'CPrim' constructor to its corresponding type
  CUnit (view ann → a) → Prim a "unit"
  CByte (view ann → a) → Prim a "byte"
  CChar (view ann → a) → Prim a "char"
  CShort (view ann → a) → Prim a "short"
  CInt (view ann → a) → Prim a "int"
  CFloat (view ann → a) → Prim a "float"
  CString (view ann → a) → Prim a "string"

-- | This function renames variables in a type.
-- | It replaces occurrences of 'from' with 'to'.
rename ∷ String → String → Ty a → Ty a
rename from to = cata \case
  -- For variable types, replace 'from' with 'to'
  Var' f@(view _2 → x)
    | x == from → inject $ Var' $ f & _2 .~ to
    | otherwise → inject $ Var' f
  -- For existential types, replace 'from' with 'to'
  Exists' f@(view (_2 % _1) → x)
    | x == from → inject $ Exists' $ f & _2 % _1 .~ to
    | otherwise → inject $ Exists' f
  -- For recursive types, replace 'from' with 'to'
  Mu' f@(view (_2 % _1) → x)
    | x == from → inject $ Mu' $ f & _2 % _1 .~ to
    | otherwise → inject $ Mu' f
  -- For all other types, return the type unchanged
  ty → inject ty

-- | This function collects all binders in a type.
binders ∷ Ty a → [String]
binders = cata \case
  -- Collect binders from existential types
  Exists' f@(view _2 → (b, bs)) → b :< bs
  -- Collect binders from recursive types
  Mu' (view _2 → (b, bs)) → b :< bs
  -- For all other types, collect recursively
  ty → foldOf folded ty

-- | This function generates a fresh binder that does not conflict with existing binders in the type.
newBinder ∷ Ty a → String
newBinder = flip withBinder id

-- | This function generates a fresh binder from a given type, using a provided continuation.
withBinder ∷ Ty a → (String → r) → r
withBinder ty@(binders → used) k =
  -- Generate names and find the first one not already used
  names
    & headOf (folded % filtered (flip (elemOf folded) used .> not))
    & fromMaybe (error "<impossible>")
    & k
  where
    -- Generate potential names for binders
    names = fmap show ['a' .. 'z'] <> do i ← [0 ..]; return ("t" <> show i)

-- | This function rolls a type.
-- | It creates a recursive type that represents the given type.
roll ∷ ∀ a f. (Eq a, f ~ Note a) ⇒ Ty a → Ty a → Ty a
roll rty@(project → rtyF) ty@(view ann &&& newBinder → (a, x)) = Mu a x (cata alg ty)
  where
    -- Helper function to process each type constructor
    alg ∷ Ty' f (Ty a) → Ty a
    alg = \case
      -- If the type matches the rolled type, create a variable
      rty'
        | rty' == rtyF → inject $ Var' (MkNote a x)
        | otherwise → inject rty'

-- | This function unrolls a recursive type.
-- | It expands the recursive definition of the type.
unroll ∷ ∀ a. (Eq a) ⇒ Ty a → Ty a → Ty a
unroll rty = cata alg
  where
    -- Helper function to process each type constructor
    alg = \case
      -- If the type matches the rolled type, rewrite the body
      rty'@(Mu' (MkNote a (x, body))) | rty' == project rty → rewrite rty x body
      -- For all other types, return the type unchanged
      rty' → inject rty'

-- | This function rewrites a type by replacing every free variable 'x' with 'rty'.
rewrite ∷ ∀ a f. (f ~ Note a) ⇒ Ty a → String → Ty a → Ty a
rewrite rty x = para phi
  where
    -- Helper function to process each type constructor
    phi ∷ Fn (Ty' f (Ty a, Ty a)) (Ty a)
    phi = \case
      -- If the type is a variable and matches 'x', replace it with 'rty'
      Var' (view _2 → x')
        | x' == x → rty
      -- For existential types, handle bound variables
      Exists' f@(view (_2 % _1) &&& view (_2 % _2) → (x', (b0, _)))
        | x == x' → inject $ Exists' $ f & (_2 % _2) .~ b0
      -- For recursive types, handle bound variables
      Mu' f@(view (_2 % _1) &&& view (_2 % _2) → (x', (b0, _)))
        | x == x' → inject $ Mu' $ f & (_2 % _2) .~ b0
      -- For all other types, return the type unchanged
      ty' → inject $ view _2 <$> ty'

-- | This function expands variables found in a type frame.
expand ∷ ∀ a. Frame a → Ty a → Ty a
expand frame = cata \case
  -- If the type is a variable and is found in the frame, replace it with the corresponding type
  Var' (view _2 → x)
    | Just (_, ty) ← ifindOf (folded % ifolded) (\x' → const (x' == x)) frame →
        ty
  -- For all other types, return the type unchanged
  ty' → inject ty'

-- | This function collects the free variables of a type.
fvs ∷ ∀ a. Ty a → Set String
fvs = cata \case
  -- If the type is a variable, return it as a free variable
  Var' (view _2 → x) → setOf folded [x]
  -- For existential types, exclude bound variables
  Exists' (view _2 → (x, xs)) → sans x xs
  -- For recursive types, exclude bound variables
  Mu' (view _2 → (x, xs)) → sans x xs
  -- For all other types, collect free variables recursively
  ty' → foldOf folded ty'
