module SQLC.CSV where

import           SQLC.Core
import           Util.P4

toRecordList ∷ String → List Record
toRecordList = undefined
  where

-- quoted = do
--   lit '"'
--   xs <- many
--   lit '"'
-- word  = alts [quoted, unquoted]
-- record = sepBy1 tab word
-- records = do
--   cols <- sepBy1 tab word; nl
--   vss <- endBy0 nl record
--   return cols
