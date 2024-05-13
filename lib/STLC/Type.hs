{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE PatternSynonyms        #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE ViewPatterns           #-}

module STLC.Type where

import           CPrim
import           Data.Set.Optics
import           Optics
import           Util

-- | Type environments
class (AsEmpty env) ⇒ Env env a | env → a where
  isTopLevel ∷ String → env → Maybe (Ty a)
  tyOf ∷ String → env → Maybe (Ty a)
  pushN ∷ [(String, Ty a)] → env → env
  push ∷ String → Ty a → env → env
  push x ty = pushN [(x, ty)]
  pushTopN ∷ [(String, Ty a)] → env → env
  pushTop ∷ String → Ty a → env → env
  pushTop x ty = pushTopN [(x, ty)]
  vars ∷ env → [String]
  mapEnv ∷ (String → Ty a → Ty a) → env → env
  update ∷ String → Fn (Ty a) (Ty a) → env → env

type Frame a = [(String, Ty a)]

-- | Type representations
type TyF ∷ (Type → Type) → Type → Type
data TyF f r where
  PrimF ∷ f String → TyF f r
  VarF ∷ f String → TyF f r
  FunF ∷ f ([r], r) → TyF f r
  VariantF ∷ f [(String, r)] → TyF f r
  RecordF ∷ f [(String, r)] → TyF f r
  ExistsF ∷ f (String, r) → TyF f r
  ArrayF ∷ f r → TyF f r
  MuF ∷ f (String, r) → TyF f r
  deriving (Functor, Foldable)

deriving instance
  ( Eq a
  , Eq (f a)
  , Eq (f ([a], a))
  , Eq (f (String, a))
  , Eq (f [(String, a)])
  , Eq (f String)
  )
  ⇒ Eq (TyF f a)

deriving instance
  ( Ord a
  , Ord (f a)
  , Ord (f ([a], a))
  , Ord (f (String, a))
  , Ord (f [(String, a)])
  , Ord (f String)
  )
  ⇒ Ord (TyF f a)

deriving instance
  ( Show a
  , Show (f a)
  , Show (f ([a], a))
  , Show (f (String, a))
  , Show (f [(String, a)])
  , Show (f String)
  )
  ⇒ Show (TyF f a)

type Ty ∷ Type → Type
type Ty ty = Fix (TyF (Pair ty))

instance Env [Frame a] a where
  isTopLevel x = fix \rec → \case
    fr :< Empty → ifindOf (folded % ifolded) (\x' → const $ x' == x) fr <&> view _2
    fr :< frs
      | Just {} ← ifindOf (folded % ifolded) (\x' → const $ x' == x) fr → Empty
      | otherwise → rec frs
    _other → Nothing

  tyOf x = fix \rec → \case
    fr :< frs
      | Just (_, ty) ← ifindOf (folded % ifolded) (\x' → const $ x' == x) fr → Just ty
      | otherwise → rec frs
  pushN fr = (fr :<)
  pushTopN defs = ($ id) $ fix \rec kont → \case
    Empty → kont [defs]
    fr :< Empty → kont [fr <> defs]
    fr :< frs → rec ((fr :<) .> kont) frs
  vars =
    ifoldrOf
      (folded % folded % ifolded)
      (\x → const (x :<))
      Empty
  mapEnv fn =
    fmap $
      ifoldrOf
        (folded % ifolded)
        (\x (fn x → ty) → ((x, ty) :<))
        Empty
  update x fn =
    fmap $
      ifoldrOf
        (folded % ifolded)
        (\x' ty@(fn → ty') → ((if x == x' then (x, ty') else (x, ty)) :<))
        Empty

instance View (TyF ty) (Fix (TyF ty)) where
  project = unFix
  inject = Fix

instance Ann (Ty a) a where
  ann = lens get' (flip set')
    where
      set' a = cata \case
        PrimF f → inject $ PrimF $ set _1 a f
        VarF f → inject $ VarF $ set _1 a f
        FunF f → inject $ FunF $ set _1 a f
        VariantF f → inject $ VariantF $ set _1 a f
        RecordF f → inject $ RecordF $ set _1 a f
        ExistsF f → inject $ ExistsF $ set _1 a f
        ArrayF f → inject $ ArrayF $ set _1 a f
        MuF f → inject $ MuF $ set _1 a f
      get' = cata \case
        PrimF f → f ^. _1
        VarF f → f ^. _1
        FunF f → f ^. _1
        VariantF f → f ^. _1
        RecordF f → f ^. _1
        ExistsF f → f ^. _1
        ArrayF f → f ^. _1
        MuF f → f ^. _1

  anns = to $ cata \case
    PrimF (view _1 .> pure → a) → a
    VarF (view _1 .> pure → a) → a
    FunF f@(view _1 .> pure → a) → foldOf folded [a, args, ret]
      where
        args = f & foldOf (folded % _1 % folded)
        ret = f & foldOf (folded % folded)
    VariantF f@(view _1 .> pure → a) → foldOf folded [a, row f]
    RecordF f@(view _1 .> pure → a) → foldOf folded [a, row f]
    ExistsF f@(view _1 .> pure → a) → foldOf folded [a, exists f]
    ArrayF f@(view _1 .> pure → a) → foldOf folded [a, array f]
    MuF f@(view _1 .> pure → a) → foldOf folded [a, mu f]
    where
      row = foldOf (folded % folded % folded)
      exists = foldOf (folded % folded)
      array = foldOf folded
      mu = foldOf (folded % folded)

prim ∷ a → String → Maybe (Ty a)
prim a x
  | elemOf folded x $
      setOf folded ["unit", "byte", "char", "short", "int", "float", "string"] =
      Just $ inject $ PrimF $ MkPair a x
  | otherwise = Empty

pattern Prim
  ∷ ∀ a f ty. (f ~ TyF (Pair a), ty ~ Ty a, View f ty) ⇒ a → String → ty
pattern Prim a str ← (project @f → PrimF (view coerced → (a, str)))
  where
    Prim a str
      | Just ty ← prim a str = ty
      | otherwise = error $ unwords [str, " is not a primitive type"]

pattern Var
  ∷ ∀ a f ty. (f ~ TyF (Pair a), ty ~ Ty a, View f ty) ⇒ a → String → ty
pattern Var a str ← (project @f → VarF (view coerced → (a, str)))
  where
    Var a str = inject $ VarF $ MkPair a str

pattern Fun
  ∷ ∀ a f ty. (f ~ TyF (Pair a), ty ~ Ty a, View f ty) ⇒ a → [ty] → ty → ty
pattern Fun a args ret ← (project @f → FunF (view coerced → (a, (args, ret))))
  where
    Fun a args ret = inject $ FunF $ MkPair a (args, ret)

pattern Variant
  ∷ ∀ a f ty. (f ~ TyF (Pair a), ty ~ Ty a, View f ty) ⇒ a → [(String, ty)] → ty
pattern Variant a row ← (project @f → VariantF (view coerced → (a, row)))
  where
    Variant a row = inject $ VariantF $ MkPair a row

pattern Record
  ∷ ∀ a f ty. (f ~ TyF (Pair a), ty ~ Ty a, View f ty) ⇒ a → [(String, ty)] → ty
pattern Record a row ← (project @f → RecordF (view coerced → (a, row)))
  where
    Record a row = inject $ RecordF $ MkPair a row

pattern Exists
  ∷ ∀ a f ty. (f ~ TyF (Pair a), ty ~ Ty a, View f ty) ⇒ a → String → ty → ty
pattern Exists a str ty ←
  (project @f → ExistsF (view coerced → (a, (str, ty))))
  where
    Exists a str ty = inject $ ExistsF $ MkPair a (str, ty)

pattern Array
  ∷ ∀ a f ty. (f ~ TyF (Pair a), ty ~ Ty a, View f ty) ⇒ a → ty → ty
pattern Array a ty ← (project @f → ArrayF (view coerced → (a, ty)))
  where
    Array a ty = inject $ ArrayF $ MkPair a ty

pattern Mu
  ∷ ∀ a f ty. (f ~ TyF (Pair a), ty ~ Ty a, View f ty) ⇒ a → String → ty → ty
pattern Mu a str ty ←
  (project @f → MuF (view _1 &&& view _2 → (a, (str, ty))))
  where
    Mu a str ty = inject $ MuF $ MkPair a (str, ty)

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
  CUnit (view ann → a) → Prim a "unit"
  CByte (view ann → a) → Prim a "byte"
  CChar (view ann → a) → Prim a "char"
  CShort (view ann → a) → Prim a "short"
  CInt (view ann → a) → Prim a "int"
  CFloat (view ann → a) → Prim a "float"
  CString (view ann → a) → Prim a "string"

rename ∷ String → String → Ty a → Ty a
rename from to = cata \case
  VarF f@(view _2 → x)
    | x == from → inject $ VarF $ f & _2 .~ to
    | otherwise → inject $ VarF f
  ExistsF f@(view (_2 % _1) → x)
    | x == from → inject $ ExistsF $ f & _2 % _1 .~ to
    | otherwise → inject $ ExistsF f
  MuF f@(view (_2 % _1) → x)
    | x == from → inject $ MuF $ f & _2 % _1 .~ to
    | otherwise → inject $ MuF f
  ty → inject ty

binders ∷ Ty a → [String]
binders = cata \case
  ExistsF f@(view _2 → (b, bs)) → b :< bs
  MuF f@(view _2 → (b, bs)) → b :< bs
  ty → foldOf folded ty

newBinder ∷ Ty a → String
newBinder = flip withBinder id

withBinder ∷ Ty a → (String → r) → r
withBinder ty@(binders → used) k =
  names
    & headOf (folded % filtered (flip (elemOf folded) used .> not))
    & fromMaybe (error "<impossible>")
    & k
  where
    names = fmap show ['a' .. 'z'] <> do i ← [0 ..]; return ("t" <> show i)

roll ∷ ∀ a. (Eq a) ⇒ Ty a → Ty a → Ty a
roll rty ty@(view ann &&& newBinder → (a, x)) = Mu a x (cata alg rty)
  where
    alg ∷ TyF (Pair a) (Ty a) → Ty a
    alg = \case
      rty'
        | rty' == project rty → inject $ VarF (Pair (a, x))
        | otherwise → inject rty'

unroll ∷ ∀ a. (Eq a) ⇒ Ty a → Ty a → Ty a
unroll rty xrty = cata alg rty
  where
    alg = \case
      rty'@(MuF (Pair (a, (x, body)))) | rty' == project rty → rewrite body x rty
      rty' → inject rty'

rewrite ∷ ∀ a. Ty a → String → Ty a → Ty a
rewrite rty x body = para alg body
  where
    alg ∷ Fn (TyF (Pair a) (Ty a, Fix (TyF (Pair a)))) (Ty a)
    alg = \case
      VarF f@(view _2 → x')
        | x' == x → rty
      ExistsF f@(view (_2 % _1) &&& view (_2 % _2) → (x', (b0, _)))
        | x == x' → inject $ ExistsF $ f & (_2 % _2) .~ b0
      MuF f@(view (_2 % _1) &&& view (_2 % _2) → (x', (b0, _)))
        | x == x' → inject $ MuF $ f & (_2 % _2) .~ b0
      tyF → inject $ view _2 <$> tyF

expand ∷ ∀ a. [(String, Ty a)] → Ty a → Ty a
expand defs = cata \case
  VarF (view _2 → x)
    | Just (_, ty) ← ifindOf (folded % ifolded) (\x' → const (x' == x)) defs →
        ty
  tyF → inject tyF

fvs ∷ ∀ a. Ty a → [String]
fvs = cata \case
  VarF (view _2 → x) → pure x
  ExistsF (view _2 → (x, xs)) → xs \\ [x]
  MuF (view _2 → (x, xs)) → xs \\ [x]
  tyF → foldOf folded tyF
