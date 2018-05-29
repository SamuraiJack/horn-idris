module Language

import SqlTypes
import Database

-- import Control.ST
import Control.Monad.State
import Data.So
import Data.Vect

%default total

%access public export

data Image : {A, B : Type} -> (f : A -> B) -> B -> Type where
    MkImage   : (x : ty) -> Image f (f x)


data TableJoiningState  = NoTables | HasTables
data TableJoiningType   = Inner | Outer | Left | Right

namespace ListHasExactlyOneElement
    data ListHasExactlyOneElement : (a : Type) -> List a -> Type where
        Because     : ListHasExactlyOneElement ty (x :: [])

getElementFromProof : (prf : ListHasExactlyOneElement ty xs) -> ty
getElementFromProof (Because {x}) = assert_total x


data DecResolvedToYes : (prop : Type) -> (dec : Dec prop) -> Type where
    MkDecResolvedToYes : (prf : prop) -> DecResolvedToYes prop (Yes prf)

-- someList : List Nat
-- someList = [ 1 ]

-- exactOne : ListHasExactlyOneElement Nat Language.someList
-- exactOne = Because

-- oneEl : Nat
-- oneEl = getElementFromProof exactOne

mutual
    data QuerySource : Type where
        Table           : (tableName : String) -> QuerySource
        SubQuery        : QueryAbstractSyntaxTree -> QuerySource
        -- -> {auto prf : QuerySourceIsNotAliased source}
        -- `prf` breaks totality
        AsSource        : (source : QuerySource) -> (aliasName : String) -> QuerySource

    data QuerySourceIsNotAliased : QuerySource -> Type where
        BecauseItIsTable        : QuerySourceIsNotAliased (Table tableName)
        BecauseItIsSubquery     : QuerySourceIsNotAliased (SubQuery query)


    nameOfQuerySource : (source : QuerySource) -> Maybe String
    nameOfQuerySource source = Nothing

    tableNameFromQuerySource : (source : QuerySource) -> Maybe String
    tableNameFromQuerySource (Table tableName) = Just tableName
    tableNameFromQuerySource (SubQuery x) = Nothing
    tableNameFromQuerySource (AsSource (Table tableName) _) = Just tableName
    tableNameFromQuerySource (AsSource _ _) = Nothing

    data ColumnExpression : SqlType -> Type where
        BooleanLiteral  : Bool -> ColumnExpression BOOLEAN
        TextLiteral     : String -> ColumnExpression TEXT
        IntegerLiteral  : Int -> ColumnExpression INTEGER
        FloatLiteral    : Double -> ColumnExpression FLOAT

        SubQueryExpression :
            (query : SqlQueryParts a before after)
            -- -> { auto im : Image queryHasExactlyOneColumn query }
            -> { auto im : DecResolvedToYes (QueryHasExactlyOneColumn (collapseToAst query)) (queryHasExactlyOneColumn (collapseToAst query)) }
            -- -> { prf : QueryHasExactlyOneColumn (collapseToAst query) }
            -> ColumnExpression (Language.getSqlTypeFromQueryWithOneColumn (collapseToAst query) {f=prf})

        Column          : {columnType : SqlType} -> (columnName : String) -> ColumnExpression columnType
        ColumnInTable   : {columnType : SqlType} -> (tableName : String) -> (columnName : String) -> ColumnExpression columnType

        AsExpr          : ColumnExpression sqlType -> (aliasName : String) -> ColumnExpression sqlType

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

    fieldsAcc : QueryAbstractSyntaxTree -> List AnyColumnExpression'
    fieldsAcc = fields

    -- fieldDecEq : (ast : QueryAbstractSyntaxTree) -> {


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


    namespace QueryHasExactlyOneColumn
        data QueryHasExactlyOneColumn : (ast : QueryAbstractSyntaxTree) -> Type where
            Because     : { ast : QueryAbstractSyntaxTree}
                -> { auto prf : ListHasExactlyOneElement AnyColumnExpression' (fields ast) }
                -> QueryHasExactlyOneColumn ast


    -- namespace QueryIsValid
    --     data QueryIsValid : (query : SqlQueryParts () before after) -> Type where
    --         Because     :
    --             -- { auto prf : ListHasExactlyOneElement AnyColumnExpression' (fields (collapseToAst query)) }
    --             -- ->
    --             QueryIsValid query


    getSqlTypeFromQueryWithOneColumn : (query : QueryAbstractSyntaxTree) -> { auto f : QueryHasExactlyOneColumn query } -> SqlType

    getSqlTypeFromQueryWithOneColumn query {f} = assert_total (
        case assert_total f of
            QueryHasExactlyOneColumn.Because {prf} =>
                let
                    (sqlType ** expression) = assert_total $ getElementFromProof prf
                in
                    assert_total sqlType
    )

    queryHasExactlyOneColumn : (ast : QueryAbstractSyntaxTree) -> Dec (QueryHasExactlyOneColumn ast)

    noColsProof : (p : [] = fieldsAcc ast) -> (colProof : QueryHasExactlyOneColumn ast) -> Void
    noColsProof p (Because {ast} {prf=singleColProof}) = assert_total $ case singleColProof of
        Because impossible

    twoAndMoreProof : (p : (x :: (y :: xs)) = fieldsAcc ast) -> (colProof : QueryHasExactlyOneColumn ast) -> Void
    twoAndMoreProof p (Because {ast} {prf=singleColProof}) = assert_total $ case singleColProof of
        Because impossible


    queryHasExactlyOneColumn ast with (fields ast) proof p

        queryHasExactlyOneColumn ast | ([]) = assert_total $
            No (\colProof => noColsProof p colProof)

        queryHasExactlyOneColumn ast | (x :: []) = assert_total $
            Yes $ Because {ast = ast} {prf = rewrite sym p in (Because {x = x})}

        queryHasExactlyOneColumn ast | (x :: y :: xs) = assert_total $
            No (\colProof => twoAndMoreProof p colProof)


-- EOF mutual




-- subQueryExpression :
--     (query : SqlQueryParts a before after)
--     -> { prf : QueryHasExactlyOneColumn (collapseToAst query) }
--     -- -> { pp : So (queryHasExactlyOneColumn query
--     -> ColumnExpression (Language.getSqlTypeFromQueryWithOneColumn (collapseToAst query) {f=prf})


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


query : SqlQueryParts a before after -> QueryAbstractSyntaxTree
query x = collapseToAst x
