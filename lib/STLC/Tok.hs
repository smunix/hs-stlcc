module STLC.Tok where

import           Util.Happy

data Tok
  = TType
  | TMuT
  | TEx
  | TExtern
  | TFrom
  | TLet
  | TIn
  | TCase
  | TOf
  | TRoll
  | TUnroll
  | TPack
  | TAs
  | TUnpack
  | TNew
  | TInt Int
  | TSym String
  | TStr String
  | TUnit
  | THasTy
  | TDot
  | TEqual
  | TLT
  | TGT
  | TBar
  | TLBracket
  | TRBracket
  | TLParen
  | TRParen
  | TComma
  | TFnArrow
  | TColon
  | TSemiColon
  | TLBrace
  | TRBrace
  | TPlus
  | TMinus
  | EoF
  deriving (Eq, Show)

step ∷ String → Diff a
step = undefined
