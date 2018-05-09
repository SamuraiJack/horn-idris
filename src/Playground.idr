module Playground

import SqlTypes
import Language
import Database

import Data.So


selectIdAndName : SqlQueryParts () (MkQueryAstState joinState) (MkQueryAstState joinState)
selectIdAndName = do
    Select [
        (_ ** Column {columnType = INTEGER} "id"),
        (_ ** Column {columnType = TEXT} "name")
    ]

joinWithZZ : SqlQueryParts () (MkQueryAstState HasTables) (MkQueryAstState HasTables)
joinWithZZ = do
    LeftJoin (Table "Company") (BooleanLiteral True)


selectFromUser : SqlQueryParts () (MkQueryAstState NoTables) (MkQueryAstState HasTables)
selectFromUser = do
    From (Table "User" `As` "U")


whereCond : SqlQueryParts () (MkQueryAstState joinState) (MkQueryAstState joinState)
whereCond = do
    Where (Column {columnType = TEXT} "name" == TextLiteral "Some")


wholeQuery : SqlQueryParts () (MkQueryAstState NoTables) (MkQueryAstState HasTables)
wholeQuery = do
    selectIdAndName
    selectFromUser
    whereCond
    joinWithZZ


compiled : Query SampleDatabase
compiled = compileQueryForDatabase wholeQuery
