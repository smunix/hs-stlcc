{-# LANGUAGE TemplateHaskell #-}

module Util.Happy where

import           Bluefin
import           Bluefin.State
import           Optics
import           Util.Common

-- | file span
data Span where
  Span
    ∷ { _name ∷ FilePath
      , _start ∷ Pos
      , _end ∷ Pos
      }
    → Span
  deriving (Eq, Show)

-- | Parser tracking state
data Track where
  Track
    ∷ { _file ∷ String
      , _rest ∷ String
      , _spans ∷ [Span]
      , _pos ∷ Pos
      }
    → Track
  deriving (Eq, Show)

data Diff a where
  Diff
    ∷ { _txt ∷ String
      , _ns ∷ Int
      , _cs ∷ Int
      , _sn ∷ Int
      , _sc ∷ Int
      , _res ∷ a
      }
    → Diff a
  deriving (Eq, Show)

data R a where
  Ok ∷ a → Track → R a
  Ko ∷ String → Track → R a
  deriving (Eq, Show)

data P a where
  Ret ∷ a → P a
  Bind ∷ P a → FnM a P b → P b
  Reduce ∷ Fn Span a → Int → P a

instance Functor P where fmap = liftM

instance Applicative P where pure = Ret; (<*>) = ap

instance Monad P where (>>=) = Bind

makeLenses ''Span
makeLenses ''Track

reduce ∷ Int → Fn Span a → P a
reduce = flip Reduce

span ∷ Fn String (Diff a) → FnM a P b → P b
span stepFn kont = undefined
