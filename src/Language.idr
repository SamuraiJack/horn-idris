module Language

import SqlTypes
import Database

import Control.ST
import Control.Monad.State
import Data.So


data ColumnExpression : SqlType -> Type where
    BooleanLiteral  : Bool -> ColumnExpression BOOLEAN
    TextLiteral     : String -> ColumnExpression TEXT
    IntegerLiteral  : Int -> ColumnExpression INTEGER
    FloatLiteral    : Double -> ColumnExpression FLOAT

    Column          : {auto columnType : SqlType} -> (columnName : String) -> ColumnExpression columnType
    ColumnInTable   : {auto columnType : SqlType} -> (tableName : String) -> (columnName : String) -> ColumnExpression columnType

    -- TODO use (Num t =>) constraint instead
    (+)             : {auto prf : SqlTypeIsNumeric t} -> ColumnExpression t -> ColumnExpression t -> ColumnExpression t
    (-)             : {auto prf : SqlTypeIsNumeric t} -> ColumnExpression t -> ColumnExpression t -> ColumnExpression t

    -- TODO use (Eq t =>) constraint instead
    (==)            : ColumnExpression t -> ColumnExpression t -> ColumnExpression BOOLEAN

    -- TODO use (Ord t =>) constraint instead
    (>)             : {auto prf : SqlTypeIsNumeric t} -> ColumnExpression t -> ColumnExpression t -> ColumnExpression BOOLEAN
    (<)             : {auto prf : SqlTypeIsNumeric t} -> ColumnExpression t -> ColumnExpression t -> ColumnExpression BOOLEAN
    (<=)            : {auto prf : SqlTypeIsNumeric t} -> ColumnExpression t -> ColumnExpression t -> ColumnExpression BOOLEAN
    (>=)            : {auto prf : SqlTypeIsNumeric t} -> ColumnExpression t -> ColumnExpression t -> ColumnExpression BOOLEAN

    And             : ColumnExpression BOOLEAN -> ColumnExpression BOOLEAN -> ColumnExpression BOOLEAN
    Or              : ColumnExpression BOOLEAN -> ColumnExpression BOOLEAN -> ColumnExpression BOOLEAN

data AnyColumnExpression : Type where
    MkAnyColumnExpression : ColumnExpression sqlType -> AnyColumnExpression


    
namespace TableJoinExpression
    data TableJoinExpression : Type -> Type where
        Empty           : TableJoinExpression ()
        SingleTable     : (tableName : String) -> TableJoinExpression ()
        InnerJoin       : (tableName : String) -> (joinExpression : ColumnExpression BOOLEAN) -> TableJoinExpression ()
        LeftJoin        : (tableName : String) -> (joinExpression : ColumnExpression BOOLEAN) -> TableJoinExpression ()
        RightJoin       : (tableName : String) -> (joinExpression : ColumnExpression BOOLEAN) -> TableJoinExpression ()

        Pure            : a -> TableJoinExpression a
        (>>=)           : TableJoinExpression a -> (a -> TableJoinExpression b) -> TableJoinExpression b

cons : a -> List a -> List a
cons = Prelude.List.(::)

extractTableNames : TableJoinExpression a -> List String
extractTableNames expr =
    execState (extractTableNamesHelper expr) []
    where
        extractTableNamesHelper : TableJoinExpression a -> State (List String) a
        extractTableNamesHelper Empty = put Prelude.List.Nil
        extractTableNamesHelper (SingleTable tableName) = modify (cons tableName)
        extractTableNamesHelper (InnerJoin tableName joinExpression) = modify (cons tableName)
        extractTableNamesHelper (LeftJoin tableName joinExpression) = modify (cons tableName)
        extractTableNamesHelper (RightJoin tableName joinExpression) = modify (cons tableName)
        extractTableNamesHelper (Pure x) = pure x
        extractTableNamesHelper (x >>= f) = do
            res <- extractTableNamesHelper x
            extractTableNamesHelper (f res)

record QueryAbstractSyntaxTree where
    constructor MkQueryAbstractSyntaxTree

    distinct        : Bool

    fields          : List AnyColumnExpression
    tables          : TableJoinExpression ()
    -- default value will be just `TRUE`
    whereCondition  : ColumnExpression BOOLEAN


data SqlQueryParts : (result : Type) -> Type where
    Select          : List AnyColumnExpression -> SqlQueryParts ()
    From            : TableJoinExpression () -> SqlQueryParts ()
    Where           : ColumnExpression BOOLEAN -> SqlQueryParts ()

    Pure            : a -> SqlQueryParts a
    (>>=)           : SqlQueryParts a -> (a -> SqlQueryParts b) -> SqlQueryParts b


selectIdAndName : SqlQueryParts ()
selectIdAndName = do
    Select [
        MkAnyColumnExpression (Column {columnType = INTEGER} "id"),
        MkAnyColumnExpression (Column {columnType = TEXT} "name")
    ]

selectFromUser : SqlQueryParts ()
selectFromUser = do
    From (SingleTable "User")

whereCond : SqlQueryParts ()
whereCond = do
    Where (Column {columnType = TEXT} "name" == TextLiteral "Some")


wholeQuery : SqlQueryParts ()
wholeQuery = do
    selectIdAndName
    selectFromUser
    whereCond


collapseToAst : SqlQueryParts a -> QueryAbstractSyntaxTree
collapseToAst x =
    execState (collapseToAstHelper x) (MkQueryAbstractSyntaxTree False [] Empty (BooleanLiteral True))
    where
        collapseToAstHelper : SqlQueryParts a -> State QueryAbstractSyntaxTree a

        collapseToAstHelper (Select expressions) = do
            modify (record { fields $= (++ expressions) })

        collapseToAstHelper (From tableJoinExpr) = do
            modify (record { tables $= (\prev => do prev; tableJoinExpr) })

        collapseToAstHelper (Where columnExpression) = do
            modify (record { whereCondition = columnExpression })

        collapseToAstHelper (Pure x) = pure x

        collapseToAstHelper (x >>= f) = do
            res <- collapseToAstHelper x
            collapseToAstHelper (f res)


-- databaseHasTable : (dbSchema : DatabaseSchema) -> (tableName : String) -> Bool
-- databaseHasTable dbSchema tableName = foldl
--     (\acc, table => acc || (name table) == tableName)
--     False
--     (tables dbSchema)


astMatchesDatabaseSchema : (dbSchema : DatabaseSchema) -> QueryAbstractSyntaxTree -> Bool
astMatchesDatabaseSchema dbSchema ast = 
    let
        tableNames          = extractTableNames $ tables ast
        tablesNotInSchema   = filter (not . (databaseHasTable dbSchema)) tableNames
    in
        tablesNotInSchema == []
        

data Query : (db : DatabaseSchema) -> Type where
    MkQuery : Query db

compileQueryForDatabase : 
    (freeQuery : SqlQueryParts ()) 
    -> {auto prf : So (astMatchesDatabaseSchema db (collapseToAst freeQuery)) } 
    -> Query db

compileQueryForDatabase {db} freeQuery = MkQuery


compiled : Query SampleDatabase
compiled = compileQueryForDatabase wholeQuery

-- -- data HasWhereCondition : QueryAbstractSyntaxTree -> Type where
-- --     Because :
-- --         HasWhereCondition
-- --             (MkQueryAbstractSyntaxTree
-- --                 fields
-- --                 tables
-- --                 (Just whereColumnExpression))

-- -- hasNoWhereCondition : (queryAst : QueryAbstractSyntaxTree) -> Type

-- -- data Access = LoggedOut | LoggedIn
-- -- data LoginResult = OK | BadPassword

-- interface ISqlQueryLanguage (m : Type -> Type) where
--     TSqlQueryLanguage : Type

--     setWhereCondition : ST m Var [ add (ColumnExpression BOOLEAN) ]

--     select : (query : Var) -> List AnyColumnExpression -> ST m () [ query ::: State QueryAbstractSyntaxTree ]

--     from : (query : Var) -> TableJoinExpression -> ST m () [ query ::: State QueryAbstractSyntaxTree ]

--     whereCondition : (query : Var) -> (cond : ColumnExpression BOOLEAN) -> ST m () [ query ::: State QueryAbstractSyntaxTree ]


-- data MyMonad : Type -> Type where
--     QueryExpression : MyMonad a

-- implementation ISqlQueryLanguage MyMonad where
--     TSqlQueryLanguage = ?ISqlQueryLanguage_rhs_1

--     setWhereCondition = ?ISqlQueryLanguage_rhs_2

--     select query expressions = do
--         queryData <- read query
--         let
--             addedExpressions = record { fields $= (++ expressions) } queryData
--         write query addedExpressions

--     from query x = ?ISqlQueryLanguage_rhs_4

--     whereCondition query cond = ?ISqlQueryLanguage_rhs_5

-- -- doSelect : (ISqlQueryLanguage m) => (query : Var) -> List AnyColumnExpression -> ST m () [ query ::: State QueryAbstractSyntaxTree ]
-- -- doSelect query expressions = do
-- --     queryData <- read query
-- --     let
-- --         addedExpressions = record { fields $= (++ expressions) } queryData
-- --     write query addedExpressions



-- -- select : (db : DatabaseSchema) -> (fields : List String) -> (tableName : String) -> Maybe Query
-- -- select db fields tableName = Just $ MkQuery fields tableName db


-- -- queryToSqlText : Query -> String
-- -- queryToSqlText (MkQuery fields tableName db) = "select" ++ (show fields) ++ " from " ++ tableName


-- -- query : Query

-- -- query = select sampleDatabase [ "name" ] "user"

{-

selectIdAndName : FreeQuery
selectIdAndName = do
    select [ "id", "name" ]


selectFromUser : FreeQuery
selectFromUser = do
    from "user"

whereCond : FreeQuery
whereCond = do
    where (column("name") == "Some")


wholeQuery : FreeQuery
wholeQuery = do
    selectIdAndName
    selectFromUser
    whereCond


database : DatabaseSchema

compiledQuery : Query database
compiledQuery = compileQueryForDatabase wholeQuery

compileQueryForDatabase : FreeQuery -> Query db
compileQueryForDatabase {db} freeQuery = ?aa

-}