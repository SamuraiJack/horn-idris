module Playground

import SqlTypes
import Language
import Database

import Data.So

%default total

selectIdAndName : SqlQueryParts () (MkQueryAstState joinState) (MkQueryAstState joinState)
selectIdAndName = do
    Select [
        (INTEGER ** Column "id"),
        (INTEGER ** Column "id")
        -- ,
        -- (_ ** SubQueryExpression $ query $ Select {joinState = NoTables} [ (INTEGER ** Column "id") ])
    
        -- ,
        -- (_ ** Column {columnType = TEXT} "name")
    ]

subQuery' : SqlQueryParts () (MkQueryAstState NoTables) (MkQueryAstState NoTables)
subQuery' = Select [ (INTEGER ** Column "id") ]

ast : QueryAbstractSyntaxTree
ast = query subQuery'

subQuery : ColumnExpression INTEGER
subQuery = SubQueryExpression ast


-- some : QueryHasExactlyOneColumn Playground.selectIdAndName
-- some = Because

joinWithZZ : SqlQueryParts () (MkQueryAstState HasTables) (MkQueryAstState HasTables)
joinWithZZ = do
    LeftJoin (Table "Company") (BooleanLiteral True)


selectFromUser : SqlQueryParts () (MkQueryAstState NoTables) (MkQueryAstState HasTables)
selectFromUser = do
    From (Table "User" `AsSource` "U")

aa : QuerySource
aa = Table "User" `AsSource` "U"

whereCond : SqlQueryParts () (MkQueryAstState joinState) (MkQueryAstState joinState)
whereCond = do
    Where (Column {columnType = TEXT} "name" == TextLiteral "Some")


wholeQuery : SqlQueryParts () (MkQueryAstState NoTables) (MkQueryAstState HasTables)
wholeQuery = do
    selectIdAndName
    selectFromUser
    whereCond
    joinWithZZ




-- compiled : Query SampleDatabase
-- compiled = compileQueryForDatabase wholeQuery
