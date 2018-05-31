module LanguageReduced

import SqlTypes
import Database
import Util
import LanguageReduced
import Data.Vect

----
sub :
    (query : PartialQuery a)
    -> { prf : QueryHasExactlyOneColumn (collapseToAst query) }
    -> ColumnExpression (getSqlTypeFromQueryWithOneColumn (collapseToAst query) {f=prf})

sub query {prf} =
    let
        x = SubQueryExpression query {prf = prf}
    in
        x


subQuery : PartialQuery ()
subQuery = Select [ (INTEGER ** Column "id") ]

one_column : QueryHasExactlyOneColumn (collapseToAst LanguageReduced.subQuery)
one_column = LanguageReduced.QueryHasExactlyOneColumn.Because {prf = Util.ListHasExactlyOneElement.Because}

-- subQuery1 : ColumnExpression INTEGER
-- subQuery1 = SubQueryExpression subQuery {prf = one_column}


subQuery1 : ColumnExpression INTEGER
subQuery1 =
    let
        x = SubQueryExpression subQuery {prf = one_column}
    in
        x


query2 : PartialQuery ()
query2 = do
    Select
        [ (INTEGER ** Column "id"), (_ ** subQuery1) ]
    From
        (SubQuery $ Select [ (INTEGER ** Column "id") ])


query3 : PartialQuery ()
query3 = do
    Select
        [ (INTEGER ** ColumnInTable "SomeTable" "id"), (_ ** subQuery1) ]
    From
        (Table "SomeTable")

query3comp : Either (ErrorPartialToComplete) CompleteQuery
query3comp = partialToComplete query3
