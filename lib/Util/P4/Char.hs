{-# LANGUAGE LambdaCase   #-}
{-# LANGUAGE MultiWayIf   #-}
{-# LANGUAGE ViewPatterns #-}

module Util.P4.Char where

import           Data.Char
import           Optics
import           Util.Common
import           Util.Num
import           Util.P4.P4  as X

type P a = P4 Char a

sat ∷ Fn Char Bool → P Char
sat cond = Sat Mod {_cond = cond, _prod = id}

dot ∷ P Char
dot = sat (/= '\n')

sp ∷ P ()
sp = lit ' '

ws0 ∷ P ()
ws0 = void $ many sp

ws1 ∷ P ()
ws1 = sp >> ws0

nl ∷ P ()
nl = lit '\n'

char ∷ P Char
char = sat (const True)

upper ∷ P Char
upper = sat (isUpper)

lower ∷ P Char
lower = sat (isLower)

digit ∷ P Int
digit = sat isDigit <&> (ord .> subtract (ord '0'))

nat ∷ P Int
nat = some digit <&> foldlOf' folded ((* 10) .> (+)) 0

int ∷ P Int
int = alts [lit '-' *> (negate <$> nat), lit '+' *> nat, nat]

float ∷ (Floating f) ⇒ P f
float = alts [lit '-' *> (negate <$> block), lit '+' *> block, block]
  where
    block =
      alts
        [ do
            (castn → e) ← nat
            lit '.'
            d@(show .> length → n) ← nat
            pure $ e + (toFrac (castn d) n)
        , castn <$> nat
        ]
    toFrac = fix \rec !d !p →
      if
        | p <= 0    → d
        | otherwise → rec (d / 10.0) (p - 1)

word ∷ P String
word = some $ sat isAlpha

key ∷ String → P ()
key = kw
