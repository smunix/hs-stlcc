{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns    #-}

module Util.P4.P4 where

import qualified Data.Char   as Char
import           Optics
import           Util.Common

class (Eq c) ⇒ NL c where
  nL ∷ c

data Mod c b where
  Mod
    ∷ { _cond ∷ Fn c Bool
      , _prod ∷ Fn c b
      }
    → Mod c b

-- | A parser that consumes a stream of @c@ and return @a@
data P4 c a where
  Ret ∷ a → P4 c a
  Bind ∷ P4 c a → FnM a (P4 c) b → P4 c b
  NoErr ∷ P4 c a → P4 c a
  Sat ∷ Mod c b → P4 c b
  Alt ∷ P4 c a → P4 c a → P4 c a
  Fail ∷ P4 c a

instance Eq (P4 c a) where
  a == b = case (a, b) of
    (Fail, Fail) → True
    _other       → False

instance Functor (P4 c) where fmap = liftM

instance Applicative (P4 c) where pure = Ret; (<*>) = ap

instance Monad (P4 c) where (>>=) = Bind

instance Alternative (P4 c) where empty = Fail; (<|>) = Alt

instance AsEmpty (P4 c a) where
  _Empty = nearly Fail (== Fail)

-- | Parsing result
data R c a where
  Ok ∷ a → Pos → [c] → R c a
  Ko ∷ Pos → [c] → R c a
  deriving (Show)

-- | Four continuations
data K4 c a b where
  K4
    ∷ { _epsK ∷ a → R c b -- success; _no_ input consumed
      , _succK ∷ a → [c] → R c b -- success; input consumed
      , _failK ∷ R c b -- failure; _no_ input consumed
      , _errK ∷ [c] → R c b -- failure; input consumed though
      }
    → K4 c a b

makeLenses ''K4
makeLenses ''Mod

{-# INLINEABLE alts #-}
alts ∷ ∀ f c a. (Foldable f) ⇒ f (P4 c a) → P4 c a
alts = foldlOf' folded Alt Fail

{-# INLINEABLE sepBy1 #-}
sepBy1
  ∷ ∀ f c sep a fa
   . (fa ~ f a, AsEmpty fa, Cons fa fa a a)
  ⇒ P4 c sep
  → P4 c a
  → P4 c (f a)
sepBy1 sep p = fix \rec → alts [(:< Empty) <$> p, sep >> (:<) <$> p <*> rec]

{-# INLINEABLE sepBy0 #-}
sepBy0
  ∷ ∀ f c sep a fa
   . (fa ~ f a, AsEmpty fa, Cons fa fa a a)
  ⇒ P4 c sep
  → P4 c a
  → P4 c (f a)
sepBy0 sep p = alts [pure Empty, sepBy1 sep p]

opt ∷ P4 c a → P4 c (Maybe a)
opt p = alts [pure Empty, Just <$> p]

lit ∷ (Eq c) ⇒ c → P4 c ()
lit c = Sat Mod {_cond = (== c), _prod = const ()}

-- | reserved keyword
kw ∷ (Eq c, Foldable f) ⇒ f c → P4 c ()
kw = flip forM_ lit .> noErr

noErr ∷ P4 c a → P4 c a
noErr = NoErr

run ∷ ∀ c a. (NL c) ⇒ P4 c a → [c] → R c a
run p0 str0@(lengthOf folded → n0) =
  walk
    K4
      { _epsK = \a → Ok a (pos str0) str0
      , _succK = \a rest → Ok a (pos rest) rest
      , _failK = Ko (pos str0) str0
      , _errK = \rest@(pos → p) → Ko p rest
      }
    str0
    p0
  where
    pos ∷ ∀ c. (NL c) ⇒ [c] → Pos
    pos str@(lengthOf folded → n) = str & cursor .> toPos
      where
        cursor ∷ [c] → Int
        cursor (lengthOf folded → n) = n - n0

        toPos ∷ Int → Pos
        toPos cur@(flip take str0 → head0) = (fn id (== nL), fn inv (/= nL))
          where
            fn modFn xFn = head0 & modFn & lengthOf (folded % filtered xFn)

    walk ∷ ∀ a b. K4 c a b → [c] → P4 c a → R c b
    walk K4 {..} str = \case
      Ret a → _epsK a
      Bind p k →
        walk
          K4
            { _epsK = \(k → k) → walk K4 {..} str k
            , _succK = \(k → k) str →
                walk
                  K4
                    { _epsK = flip _succK str
                    , _failK = _errK str
                    , ..
                    }
                  str
                  k
            , ..
            }
          str
          p
      NoErr p → walk K4 {_errK = const _failK, ..} str p
      Sat Mod {..} → case str of
        Empty → _failK
        c :< cs
          | _cond c → _succK (_prod c) cs
          | otherwise → _failK
      Alt p1 p2 →
        walk
          K4
            { _epsK = \a →
                -- If p1 doesn't consume, continue with p2.
                -- If p2 doesn't consume either, p1 prevails
                walk
                  K4
                    { _epsK = const $ _epsK a
                    , _failK = _epsK a
                    , ..
                    }
                  str
                  p2
            , _failK = walk K4 {..} str p2
            , ..
            }
          str
          p1
      Fail → _failK
