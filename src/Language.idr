module Language

import SqlTypes
import Database

-- import Control.ST
import Control.Monad.State
import Data.So
import Data.Vect

%default total

%access public export

mutual
    data QuerySource : Type where
        Table           : (tableName : String) -> QuerySource
        SubQuery        : SqlQueryParts () before after -> QuerySource
        As              : (source : QuerySource) -> {auto prf : QuerySourceIsNotAliased source} -> (aliasName : String) -> QuerySource

    data QuerySourceIsNotAliased : QuerySource -> Type where
        BecauseItIsTable        : QuerySourceIsNotAliased (Table tableName)
        BecauseItIsSubquery     : QuerySourceIsNotAliased (SubQuery query)
            

    nameOfQuerySource : (source : QuerySource) -> Maybe String
    nameOfQuerySource source = Nothing

    tableNameFromQuerySource : (source : QuerySource) -> Maybe String
    tableNameFromQuerySource (Table tableName) = Just tableName
    tableNameFromQuerySource (SubQuery x) = Nothing
    tableNameFromQuerySource (As (Table tableName) _) = Just tableName
    tableNameFromQuerySource (As _ _) = Nothing


    data ColumnExpression : SqlType -> Type where
        BooleanLiteral  : Bool -> ColumnExpression BOOLEAN
        TextLiteral     : String -> ColumnExpression TEXT
        IntegerLiteral  : Int -> ColumnExpression INTEGER
        FloatLiteral    : Double -> ColumnExpression FLOAT

        Column          : {columnType : SqlType} -> (columnName : String) -> ColumnExpression columnType
        ColumnInTable   : {columnType : SqlType} -> (tableName : String) -> (columnName : String) -> ColumnExpression columnType

        ColumnAs        : {columnType : SqlType} -> (columnName : String) -> (columnAlias : String) -> ColumnExpression columnType
        ColumnInTableAs : {columnType : SqlType} -> (tableName : String) -> (columnName : String) -> (columnAlias : String) -> ColumnExpression columnType

        Alias           : {aliasType : SqlType} -> (columnName : String) -> ColumnExpression aliasType

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

    AnyColumnExpression' : Type
    AnyColumnExpression' = (sqlType ** ColumnExpression sqlType)


    data TableJoiningType = Inner | Outer | Left | Right
    data TableJoining = MkTableJoining QuerySource TableJoiningType (ColumnExpression BOOLEAN)

    record QueryAbstractSyntaxTree where
        constructor MkQueryAbstractSyntaxTree

        distinct        : Bool

        fields          : List AnyColumnExpression'
        baseTable       : Maybe QuerySource
        joins           : List TableJoining
        -- tables          : TableJoinExpression () before after
        -- default value will be just `TRUE`
        whereCondition  : ColumnExpression BOOLEAN


    data TableJoiningState = NoTables | HasTables

    record QueryAstState where
        constructor MkQueryAstState

        joinState               : TableJoiningState


    data SqlQueryParts : (result : Type) -> (before : QueryAstState) -> (after : QueryAstState) -> Type where
        Select :
            List AnyColumnExpression'
            -> SqlQueryParts
                ()
                (MkQueryAstState
                    joinState
                )
                (MkQueryAstState
                    joinState
                )
        AlsoSelect :
            List AnyColumnExpression'
            -> SqlQueryParts
                ()
                (MkQueryAstState
                    joinState
                )
                (MkQueryAstState
                    joinState
                )

        From :
            (source : QuerySource)
            -> SqlQueryParts
                ()
                (MkQueryAstState
                    NoTables
                )
                (MkQueryAstState
                    HasTables
                )

        LeftJoin :
            (source : QuerySource)
            -> (joinExpression : ColumnExpression BOOLEAN)
            -> SqlQueryParts
                ()
                (MkQueryAstState
                    HasTables
                )
                (MkQueryAstState
                    HasTables
                )
        Where :
            ColumnExpression BOOLEAN ->
            SqlQueryParts
                ()
                (MkQueryAstState joinState)
                (MkQueryAstState joinState)

        Pure            : a -> SqlQueryParts a before before
        (>>=)           : SqlQueryParts a st1 st2 -> (a -> SqlQueryParts b st2 st3) -> SqlQueryParts b st1 st3

collapseToAst : SqlQueryParts a before after -> QueryAbstractSyntaxTree
collapseToAst x =
    execState (collapseToAstHelper x) (MkQueryAbstractSyntaxTree False [] Nothing [] (BooleanLiteral True))
    where
        collapseToAstHelper : SqlQueryParts a before after -> State QueryAbstractSyntaxTree a

        collapseToAstHelper (Select expressions) = do
            modify (record { fields $= (++ expressions) })

        collapseToAstHelper (AlsoSelect expressions) = do
            modify (record { fields $= (++ expressions) })

        collapseToAstHelper (From querySource) = do
            modify (record { baseTable = Just querySource })

        collapseToAstHelper (LeftJoin querySource joinExpression) = do
            modify (record { joins $= ((MkTableJoining querySource Left joinExpression) ::) })

        collapseToAstHelper (Where columnExpression) = do
            modify (record { whereCondition = columnExpression })

        collapseToAstHelper (Pure x) = pure x

        collapseToAstHelper (x >>= f) = do
            res <- collapseToAstHelper x
            collapseToAstHelper (f res)


total
extractTableNames : (ast : QueryAbstractSyntaxTree) -> List String
extractTableNames (MkQueryAbstractSyntaxTree distinct fields baseSource joins whereCondition) =
    let
        sources         = map (\(MkTableJoining source _ _) => source) joins
        tableNames      = filter (isJust) $ map (tableNameFromQuerySource) sources
        joinTables      = map (fromMaybe "") tableNames
    in
        case baseSource of
            Nothing     => joinTables
            Just source => case tableNameFromQuerySource source of
                Nothing             => joinTables
                Just tableName      => tableName :: joinTables

astTablesInSchema : (dbSchema : DatabaseSchema) -> QueryAbstractSyntaxTree -> Bool
astTablesInSchema dbSchema ast =
    let
        tableNames          = extractTableNames ast
        tablesNotInSchema   = filter (not . (databaseHasTable dbSchema)) tableNames
    in
        tablesNotInSchema == []
        
            
data Query : (db : DatabaseSchema) -> Type where
    MkQuery : Query db

compileQueryForDatabase :
    (freeQuery : SqlQueryParts () before after)
    -> {auto prf : So (astTablesInSchema db (collapseToAst freeQuery)) }
    -> Query db

compileQueryForDatabase {db} freeQuery = MkQuery

