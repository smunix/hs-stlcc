{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns    #-}

module Util.P4.P4 where

import qualified Data.Char   as Char
import           Optics
import           Util.Common

-- | Newline type class, requiring an 'Eq' instance.
-- | Defines a newline character for a given type 'c'.
class (Eq c) ⇒ NL c where
  nL ∷ c

-- | Instance of 'NL' for 'Char', defining the newline character as '\n'.
instance NL Char where
  nL = '\n'

-- | Data type representing a modification of type 'c' to type 'b'.
data Mod c b where
  Mod
    ∷ { _cond ∷ Fn c Bool
      -- ^ Condition to match elements of type 'c'.
      , _prod ∷ Fn c b
      -- ^ Production function to transform elements of type 'c' to type 'b'.
      }
    → Mod c b

-- | A parser that consumes a stream of 'c' and returns 'a'.
data P4 c a where
  Ret
    ∷ a
    → P4 c a
    -- ^ Return a value.
  Bind
    ∷ P4 c a
    → FnM a (P4 c) b
    → P4 c b
    -- ^ Bind operation for sequencing parsers.
  NoErr
    ∷ P4 c a
    → P4 c a
    -- ^ Parser that does not produce an error.
  Sat
    ∷ Mod c b
    → P4 c b
    -- ^ Satisfy a condition and produce a value.
  Alt
    ∷ P4 c a
    → P4 c a
    → P4 c a
    -- ^ Alternative parser, tries the first parser, if it fails, tries the second.
  Fail ∷ P4 c a
    -- ^ Failing parser.

-- | 'Eq' instance for 'P4' that only checks for equality of 'Fail' parsers.
instance Eq (P4 c a) where
  a == b = case (a, b) of
    (Fail, Fail) → True
    _other       → False

-- | 'Functor' instance for 'P4'.
instance Functor (P4 c) where
  fmap = liftM

-- | 'Applicative' instance for 'P4'.
instance Applicative (P4 c) where
  pure = Ret
  (<*>) = ap

-- | 'Monad' instance for 'P4'.
instance Monad (P4 c) where
  (>>=) = Bind

-- | 'Alternative' instance for 'P4'.
instance Alternative (P4 c) where
  empty = Fail
  (<|>) = Alt

-- | 'AsEmpty' instance for 'P4'.
instance AsEmpty (P4 c a) where
  _Empty = nearly Fail (== Fail)

-- | Parsing result data type.
data R c a where
  Ok
    ∷ a
    → Pos
    → [c]
    → R c a
    -- ^ Success result with value, position, and remaining input.
  Ko
    ∷ Pos
    → [c]
    → R c a
    -- ^ Failure result with position and remaining input.
  deriving (Show)

-- | Four continuations used in the parsing process.
data K4 c a b where
  K4
    ∷ { _epsK ∷ a → R c b
      -- ^ Success with no input consumed.
      , _succK ∷ a → [c] → R c b
      -- ^ Success with input consumed.
      , _failK ∷ R c b
      -- ^ Failure with no input consumed.
      , _errK ∷ [c] → R c b
      -- ^ Failure with input consumed.
      }
    → K4 c a b

-- | Generate lenses for 'K4' and 'Mod'.
makeLenses ''K4
makeLenses ''Mod

-- | Combine a foldable collection of parsers into a single parser using alternatives.
{-# INLINEABLE alts #-}
alts ∷ ∀ f c a. (Foldable f) ⇒ f (P4 c a) → P4 c a
alts = foldlOf' folded Alt Fail

endBy0
  ∷ ∀ f c sep a fa
   . (fa ~ f a, AsEmpty fa, Cons fa fa a a)
  ⇒ P4 c sep
  → P4 c a
  → P4 c (f a)
endBy0 end p = fix \rec → alts [pure Empty, (:<) <$> (p <* end) <*> rec]

-- | Parse one or more occurrences of 'p' separated by 'sep'.
{-# INLINEABLE sepBy1 #-}
sepBy1
  ∷ ∀ f c sep a fa
   . (fa ~ f a, AsEmpty fa, Cons fa fa a a)
  ⇒ P4 c sep
  → P4 c a
  → P4 c (f a)
sepBy1 sep p = fix \rec → alts [(:< Empty) <$> p, sep >> (:<) <$> p <*> rec]

-- | Parse zero or more occurrences of 'p' separated by 'sep'.
{-# INLINEABLE sepBy0 #-}
sepBy0
  ∷ ∀ f c sep a fa
   . (fa ~ f a, AsEmpty fa, Cons fa fa a a)
  ⇒ P4 c sep
  → P4 c a
  → P4 c (f a)
sepBy0 sep p = alts [pure Empty, sepBy1 sep p]

-- | Optional parser that returns 'Just' the result if it succeeds or 'Nothing' if it fails.
opt ∷ P4 c a → P4 c (Maybe a)
opt p = alts [pure Nothing, Just <$> p]

-- | Literal parser that matches a single character 'c'.
lit ∷ (Eq c) ⇒ c → P4 c ()
lit c = Sat Mod {_cond = (== c), _prod = const ()}

-- | Reserved keyword parser that matches a foldable collection of characters.
kw ∷ (Eq c, Foldable f) ⇒ f c → P4 c ()
kw = mapM_ lit .> noErr

-- | Parser that does not produce an error.
noErr ∷ P4 c a → P4 c a
noErr = NoErr

-- | Run a parser on a given input and return the result.
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
    -- \| Calculate the current position in the input stream.
    pos ∷ ∀ c. (NL c) ⇒ [c] → Pos
    pos str@(lengthOf folded → n) = str & cursor .> toPos
      where
        -- \| Calculate the cursor position based on the length of the input.
        cursor ∷ [c] → Int
        cursor (lengthOf folded → n) = n - n0

        -- \| Convert the cursor position to a 'Pos' data type.
        toPos ∷ Int → Pos
        toPos cur@(flip take str0 → head0) = (fn id (== nL), fn inv (/= nL))
          where
            -- \| Helper function to count occurrences based on a condition.
            fn modFn xFn = head0 & modFn & lengthOf (folded % filtered xFn)

    -- \| Walk through the input stream and apply the parser.
    walk ∷ ∀ a b. K4 c a b → [c] → P4 c a → R c b
    walk K4 {..} str = \case
      Ret a → _epsK a -- If the parser returns a value, use the epsilon continuation.
      Bind p k →
        walk
          K4
            { _epsK = \(k → k) → walk K4 {..} str k -- Bind the parser result to the next parser.
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
      NoErr p → walk K4 {_errK = const _failK, ..} str p -- Parse without producing an error.
      Sat Mod {..} → case str of
        Empty → _failK -- If the input is empty, fail.
        c :< cs
          | _cond c → _succK (_prod c) cs -- If the condition matches, succeed with the production function result.
          | otherwise → _failK -- If the condition does not match, fail.
      Alt p1 p2 →
        walk
          K4
            { _epsK = \a →
                -- If the first parser succeeds without consuming input, try the second parser.
                walk
                  K4
                    { _epsK = const $ _epsK a
                    , _failK = _epsK a
                    , ..
                    }
                  str
                  p2
            , _failK = walk K4 {..} str p2 -- If the first parser fails, try the second parser.
            , ..
            }
          str
          p1
      Fail → _failK -- If the parser fails, use the fail continuation.
