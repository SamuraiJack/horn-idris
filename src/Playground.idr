module Playground

import SqlTypes
import Language
import Database

import Data.So

%default total
%language ElabReflection

selectIdAndName : SqlQueryParts () (MkQueryAstState joinState) (MkQueryAstState joinState)
selectIdAndName = do
    assert_total $ Select [
        (INTEGER ** Column "id")
        -- ,
        -- (INTEGER ** Column "id")
        -- ,
        -- (_ ** SubQueryExpression $ Select {joinState = NoTables} [ (INTEGER ** Column "id") ])

        -- ,
        -- (_ ** Column {columnType = TEXT} "name")
    ]

subQuery'' : SqlQueryParts () (MkQueryAstState NoTables) (MkQueryAstState NoTables)
subQuery'' = Select {joinState = NoTables} [ (INTEGER ** Column "id") ]

one_column' : QueryHasExactlyOneColumn (collapseToAst Playground.subQuery'')
one_column' = assert_total $ Because

subQuery1 : ColumnExpression INTEGER
subQuery1 = SubQueryExpression subQuery'' {prf=one_column'}

-- subQuery' : AnyColumnExpression'
-- subQuery' = (_ ** SubQueryExpression $ subQuery'')

ast : QueryAbstractSyntaxTree
ast = query (selectIdAndName {joinState=NoTables})

-- bb : QueryAbstractSyntaxTree
-- bb = MkQueryAbstractSyntaxTree False
--     [(INTEGER **
--         Column "id")]
--     Nothing
--     []
--     (BooleanLiteral True)

-- cc : QueryHasExactlyOneColumn Playground.bb
-- cc = (assert_total Because) Playground.bb

-- subQuery : ColumnExpression INTEGER
-- subQuery = SubQueryExpression ast

one_column : QueryHasExactlyOneColumn Playground.ast
one_column = assert_total $ Because

-- joinWithZZ : SqlQueryParts () (MkQueryAstState HasTables) (MkQueryAstState HasTables)
-- joinWithZZ = do
--     LeftJoin (Table "Company") (BooleanLiteral True)


-- selectFromUser : SqlQueryParts () (MkQueryAstState NoTables) (MkQueryAstState HasTables)
-- selectFromUser = do
--     From (Table "User" `AsSource` "U")

-- aa : QuerySource
-- aa = Table "User" `AsSource` "U"

-- whereCond : SqlQueryParts () (MkQueryAstState joinState) (MkQueryAstState joinState)
-- whereCond = do
--     Where (Column {columnType = TEXT} "name" == TextLiteral "Some")


-- wholeQuery : SqlQueryParts () (MkQueryAstState NoTables) (MkQueryAstState HasTables)
-- wholeQuery = do
--     selectIdAndName
--     selectFromUser
--     whereCond
--     joinWithZZ




-- -- compiled : Query SampleDatabase
-- -- compiled = compileQueryForDatabase wholeQuery
