{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RoleAnnotations   #-}
{-# LANGUAGE ViewPatterns      #-}

module SQLC.Top where

import           Data.Array  as Array
import qualified Data.Array  as Array
import           Data.String
import           SQLC.Core   (Dom (..), Name)
import qualified SQLC.Core   as SQL
import qualified SQLC.IR     as IR
import           SQLC.Query  (Query)
import qualified SQLC.Query  as Query
import qualified SQLC.Term   as Term
import           Util

lower ∷ String → Query → IO ()
lower txt@(lengthOf folded .> flip replicate '=' → ln) query = do
  let
    indent str = replicate 10 ' ' <> str
  putStrLn txt
  putStrLn ln
  print' query
  putStrLn $ indent "| |"
  putStrLn $ indent "\\ /"
  putStrLn $ indent " +"
  let
    ir = IR.ir query
  print' ir
  putStrLn $ indent "|||"
  putStrLn $ indent "\\ /"
  putStrLn $ indent " +"
  (IR.asm .> IR.exec) ir
  putStrLn ""

io ∷ IO ()
io = traverseOf_ traversed (\(_i, (n, q)) → lower n q) (Array.assocs queries)
  where
    queries ∷ Array Int (String, Query)
    queries = arr
      where
        arr =
          Array.listArray
            (0, lengthOf folded qs - 1)
            [(n, q ln) | (ln, (i, n, q)) ← zip [0 ..] qs]

        qs ∷ [(Int, String, Int → Query)]
        qs =
          [ (0, "ScanFile", mkQ scanFileQuery (-1))
          , (1, "Project", mkQ projectQuery 0)
          , (2, "Filter0", mkQ filterQuery0 1)
          , (3, "Filter1", mkQ filterQuery1 1)
          , (4, "Filter2", mkQ filterQuery2 1)
          , (5, "Join", mkQ joinQuery0 1)
          , (6, "GroupBy", mkQ groupByQuery0 1)
          , (7, "Expand", mkQ expandQuery0 6)
          , (8, "Count", mkQ countQuery0 6)
          ]

        mkQ q i ln
          | i < ln = q (arr ! i ^. _2)
          | otherwise = error "failed to construct query"

    scanFileQuery =
      const $
        Query.ScanFile
          [("Name", SQL.String), ("Age", SQL.I32), ("City", SQL.String)]
          "<filepath>"
    filterQuery0 =
      Query.Filter
        ( Query.Ne
            "ID"
            (Query.Val "Kaze")
        )
    filterQuery1 =
      Query.Filter
        ( Query.Ge
            "Maturity"
            (Query.Val 18)
        )
    filterQuery2 =
      Query.Filter
        ( Query.And
            ( Query.Ne
                "ID"
                (Query.Val "Kaze")
            )
            ( Query.Le
                "Maturity"
                (Query.Val 18)
            )
        )
    -- joinQuery0 q = Query.Join (as "L" $ filterQuery0 q) (as "R" $ filterQuery1 q)
    -- joinQuery0 q = Query.ProjectAs ["R.ID", "L.ID"] ["R", "L"] do Query.Join (Query.as "L" $ filterQuery0 q) (Query.as "R" $ filterQuery1 q)
    joinQuery0 q =
      Query.ProjectAs ["L.ID", "L.Maturity"] ["ID", "Age"] do
        Query.Filter (Query.Eq "L.ID" "R.ID") do
          Query.Join (Query.as "L" $ filterQuery0 q) (Query.as "R" $ filterQuery1 q)

    expandQuery0 = Query.Expand "G"

    groupByQuery0 =
      Query.GroupBy
        (toMapOf (folded % ifolded) [("Maturity", SQL.I32), ("Location", SQL.String)])
        "G"

    -- countQuery0 = Query.Count "G" "Count"
    countQuery0 q =
      Query.ProjectAs ["Count", "Maturity", "Location"] ["CountN", "Age", "City"] do
        Query.Count "G" "Count" q
    projectQuery =
      Query.ProjectAs
        ["Name", "Age", "City"]
        ["ID", "Maturity", "Location"]
