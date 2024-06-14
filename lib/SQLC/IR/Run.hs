{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}

module SQLC.IR.Run where

import           Control.Monad
import           SQLC.Core
import           SQLC.IR.IR    (IR)
import qualified SQLC.IR.IR    as IR

data Asm a where
  Pure ∷ a → Asm a
  Then ∷ Asm a → (a → Asm b) → Asm b
  Stop ∷ Asm ()
  Load ∷ FilePath → Asm Table
  Trace ∷ String → Asm a → Asm a

instance Functor Asm where fmap = liftM

instance Applicative Asm where pure = Pure; (<*>) = ap

instance Monad Asm where (>>=) = Then

asm ∷ IR → Asm ()
asm = undefined
