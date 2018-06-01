module Language

import SqlTypes
import Database
import Util
import Language.PartialQuery
import Language.CompleteQuery

import Data.Vect

-- ----
-- sub :
--     (query : PartialQuery a)
--     -> { prf : QueryHasExactlyOneColumn (collapseToAst query) }
--     -> ColumnExpression (getSqlTypeFromQueryWithOneColumn (collapseToAst query) {f=prf})
--
-- sub query {prf} =
--     let
--         x = SubQueryExpression query {prf = prf}
--     in
--         x
--
--
-- subQuery : PartialQuery ()
-- subQuery = Select [ (INTEGER ** ColumnT "id") ]
--
-- one_column : QueryHasExactlyOneColumn (collapseToAst Language.subQuery)
-- one_column = Language.QueryHasExactlyOneColumn.Because {prf = Util.ListHasExactlyOneElement.Because}
--
-- -- subQuery1 : ColumnExpression INTEGER
-- -- subQuery1 = SubQueryExpression subQuery {prf = one_column}
--
--
-- subQuery1 : ColumnExpression INTEGER
-- subQuery1 =
--     let
--         x = SubQueryExpression subQuery {prf = one_column}
--     in
--         x


-- query2 : PartialQuery ()
-- query2 = do
--     Select
--         [ (INTEGER ** ColumnT "id"), (_ ** subQuery1) ]
--     From
--         (SubQuery $ Select [ (INTEGER ** ColumnT "id") ])


query3 : PartialQuery ()
query3 = do
    Select
        [ (INTEGER ** ColumnInTableT "SomeTable" "id") ]
    From
        (Table "SomeTable")

query3comp : Either (ErrorPartialToComplete) CompleteQuery
query3comp = partialToComplete query3


query4 : PartialQuery ()
query4 = do
    Select
        [
            (_ ** Column "id"), (_ ** Column "name"), (_ ** Column "salary")
            , (_ ** ColumnInTable "Z" "salary")
        ]
    From
        (As (Table "User") "U")

query4comp : Either (ErrorPartialToComplete) CompleteQuery
query4comp = partialToComplete query4
