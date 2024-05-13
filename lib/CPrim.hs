{-# LANGUAGE UndecidableInstances #-}

module CPrim where

import           Optics
import           Util

-- | C primitive types
data CPrim f where
  CUnit ∷ f () → CPrim f
  CByte ∷ f Word8 → CPrim f
  CChar ∷ f Char → CPrim f
  CShort ∷ f Int → CPrim f
  CInt ∷ f Int → CPrim f
  CFloat ∷ f Float → CPrim f
  CString ∷ f String → CPrim f

deriving instance
  ( Eq (f ())
  , Eq (f String)
  , Eq (f Char)
  , Eq (f Word8)
  , Eq (f Int)
  , Eq (f Float)
  )
  ⇒ Eq (CPrim f)

deriving instance
  ( Ord (f ())
  , Ord (f String)
  , Ord (f Char)
  , Ord (f Word8)
  , Ord (f Int)
  , Ord (f Float)
  )
  ⇒ Ord (CPrim f)
