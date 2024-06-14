module Util (module Util, module X) where

import           Data.Maybe
import           Optics             as X
import           Optics.Core.Extras as X
import           Util.Common        as X
import           Util.Recurse       as X
import           Util.Sequence      as X

unJust ∷ String → Maybe a → a
unJust msg = fromMaybe (error msg)
