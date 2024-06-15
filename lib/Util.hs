{-# LANGUAGE CPP #-}

module Util (module Util, module X) where

import           Control.Monad.IO.Class
import           Data.Maybe
import           Optics                 as X
import           Optics.Core.Extras     as X
import           Text.Pretty.Simple     as X
import           Util.Common            as X
import           Util.Recurse           as X
import           Util.Sequence          as X

unJust ∷ String → Maybe a → a
unJust msg = fromMaybe (error msg)

#if 0
print' ::forall a m. (MonadIO m, Show a) => a ->m ()
print' = pPrint
#else
print' ::forall a m. (m ~ IO, MonadIO m, Show a) => a ->m ()
print' = print
#endif
