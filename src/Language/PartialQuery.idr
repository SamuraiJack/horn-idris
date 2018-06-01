module Language.PartialQuery

import SqlTypes
import Database
import Util

import Control.Monad.State
import Data.So
import Data.Vect

%default total
%access public export

mutual
    ----
    namespace QuerySource
        data QuerySource : Type where
            Table           : (tableName : TableName) -> QuerySource
            SubQuery        : (query : PartialQuery a) -> QuerySource
            As              : (source : QuerySource) -> (aliasName : TableName) -> QuerySource

    querySourceName : (source : QuerySource) -> Maybe TableName
    querySourceName (Table tableName) = Just tableName
    querySourceName (SubQuery x) = Nothing
    querySourceName (As source aliasName) = Just aliasName


    ----
    data TableJoiningType   = Inner | Outer | Left | Right

    data TableJoining       = MkTableJoining QuerySource TableJoiningType (ColumnExpression BOOLEAN)

    querySourceFromTableJoining : TableJoining -> QuerySource
    querySourceFromTableJoining (MkTableJoining querySource _ _) = querySource


    ----
    namespace ColumnExpression
        data ColumnExpression : SqlType -> Type where
            BooleanLiteral  : Bool -> ColumnExpression BOOLEAN
            IntegerLiteral  : Int -> ColumnExpression INTEGER
            StringLiteral   : String -> ColumnExpression TEXT

            ColumnT         : {columnType : SqlType} -> (columnName : String) -> ColumnExpression columnType
            ColumnInTableT  : {columnType : SqlType} -> (tableName : String) -> (columnName : String) -> ColumnExpression columnType

            Column          : (columnName : String) -> ColumnExpression UNKNOWN
            ColumnInTable   : (tableName : String) -> (columnName : String) -> ColumnExpression UNKNOWN

            As              : ColumnExpression sqlType -> (aliasName : String) -> ColumnExpression sqlType

            SubQueryExpression :
                (query : PartialQuery a)
                -> { prf : QueryHasExactlyOneColumn (collapseToAst query) }
                -> ColumnExpression (getSqlTypeFromQueryWithOneColumn (collapseToAst query) {f = prf})

            (+)             : ColumnExpression sqlType -> ColumnExpression sqlType -> ColumnExpression sqlType

    ----
    AnyColumnExpression : Type
    AnyColumnExpression = (sqlType ** ColumnExpression sqlType)

    ----
    record QueryAbstractSyntaxTree where
        constructor MkQueryAbstractSyntaxTree

        fields          : List AnyColumnExpression
        baseTable       : List QuerySource
        joins           : List TableJoining


    -- workaround for: https://github.com/idris-lang/Idris-dev/issues/4444
    fieldsAcc : QueryAbstractSyntaxTree -> List AnyColumnExpression
    fieldsAcc = fields

    baseTableAcc : QueryAbstractSyntaxTree -> List QuerySource
    baseTableAcc = baseTable


    ----
    data PartialQuery : (result : Type) -> Type where
        Select          : List AnyColumnExpression -> PartialQuery ()
        Pure            : a -> PartialQuery a
        From            : (source : QuerySource) -> PartialQuery ()
        LeftJoin        : (source : QuerySource) -> (joinExpression : ColumnExpression BOOLEAN) -> PartialQuery ()

        (>>=)           : PartialQuery a -> (a -> PartialQuery b) -> PartialQuery b


    ----
    collapseToAst : PartialQuery a -> QueryAbstractSyntaxTree
    collapseToAst x =
        execState (collapseToAstHelper x) (MkQueryAbstractSyntaxTree [] [] [])
        where
            collapseToAstHelper : PartialQuery a -> State QueryAbstractSyntaxTree a

            collapseToAstHelper (Select expressions) = do
                modify (record { fields $= (++ expressions) })

            collapseToAstHelper (Pure x) = pure x

            collapseToAstHelper (From querySource) = do
                modify (record { baseTable $= (querySource ::) })

            collapseToAstHelper (LeftJoin querySource joinExpression) = do
                modify (record { joins $= ((MkTableJoining querySource Left joinExpression) ::) })

            collapseToAstHelper (x >>= f) = do
                res <- collapseToAstHelper x
                collapseToAstHelper (f res)

    ----
    namespace QueryHasExactlyOneColumn
        data QueryHasExactlyOneColumn : (ast : QueryAbstractSyntaxTree) -> Type where
            Because     : { ast : QueryAbstractSyntaxTree }
                -> { auto prf : ListHasExactlyOneElement AnyColumnExpression (fields ast) }
                -> QueryHasExactlyOneColumn ast

        noColsProof : (p : [] = fieldsAcc ast) -> (colProof : QueryHasExactlyOneColumn ast) -> Void
        noColsProof p (Because {ast} {prf=singleColProof}) = assert_total $ case singleColProof of
            Because impossible

        twoAndMoreProof : (p : (x :: (y :: xs)) = fieldsAcc ast) -> (colProof : QueryHasExactlyOneColumn ast) -> Void
        twoAndMoreProof p (Because {ast} {prf=singleColProof}) = assert_total $ case singleColProof of
            Because impossible

        queryHasExactlyOneColumn : (ast : QueryAbstractSyntaxTree) -> Dec (QueryHasExactlyOneColumn ast)
        queryHasExactlyOneColumn ast with (fields ast) proof p

            queryHasExactlyOneColumn ast | ([]) = assert_total $
                No (\colProof => noColsProof p colProof)

            queryHasExactlyOneColumn ast | (x :: []) = assert_total $
                Yes $ Because {ast = ast} {prf = rewrite sym p in (Because {x = x})}

            queryHasExactlyOneColumn ast | (x :: y :: xs) = assert_total $
                No (\colProof => twoAndMoreProof p colProof)

    ----
    namespace QueryHasExactlyOneBaseTable
        data QueryHasExactlyOneBaseTable : (ast : QueryAbstractSyntaxTree) -> Type where
            Because     : { ast : QueryAbstractSyntaxTree }
                -> { auto prf : ListHasExactlyOneElement QuerySource (baseTableAcc ast) }
                -> QueryHasExactlyOneBaseTable ast

        noColsProof : (p : [] = baseTableAcc ast) -> QueryHasExactlyOneBaseTable ast -> Void
        -- noColsProof p (Because {ast} {prf}) = case p of
        --     Refl impossible

        twoAndMoreProof : (p : (x :: (y :: xs)) = baseTableAcc ast) -> (colProof : QueryHasExactlyOneBaseTable ast) -> Void
        -- twoAndMoreProof p (Because {ast} {prf=singleColProof}) = assert_total $ case singleColProof of
        --     Because impossible

        queryHasExactlyOneBaseTable : (ast : QueryAbstractSyntaxTree) -> Dec (QueryHasExactlyOneBaseTable ast)
        queryHasExactlyOneBaseTable ast with (baseTableAcc ast) proof p

            queryHasExactlyOneBaseTable ast | ([]) = assert_total $
                No (\colProof => noColsProof p colProof)

            queryHasExactlyOneBaseTable ast | (x :: []) = assert_total $
                Yes $ Because {ast = ast} {prf = rewrite sym p in (Because {x = x})}

            queryHasExactlyOneBaseTable ast | (x :: y :: xs) = assert_total $
                No (\colProof => twoAndMoreProof p colProof)


    ----
    getSqlTypeFromQueryWithOneColumn : (query : QueryAbstractSyntaxTree) -> { auto f : QueryHasExactlyOneColumn query } -> SqlType

    getSqlTypeFromQueryWithOneColumn query {f} = assert_total (
        case assert_total f of
            QueryHasExactlyOneColumn.Because {prf} =>
                let
                    (sqlType ** expression) = assert_total $ getElementFromProof prf
                in
                    assert_total sqlType
    )

-- EOF mutual

----
getExpressionSources' : AnyColumnExpression -> List TableName
getExpressionSources' (sqlType ** pf) = assert_total $ case pf of
    (BooleanLiteral x) => []
    (IntegerLiteral x) => []
    (Column columnName) => []
    (ColumnInTable tableName columnName) => [ tableName ]
    (As x aliasName) => getExpressionSources' (sqlType ** x)
    (SubQueryExpression query) => []
    (x + y) => getExpressionSources' (sqlType ** x) ++ getExpressionSources' (sqlType ** y)


getExpressionSources : (ast : QueryAbstractSyntaxTree) -> List TableName
getExpressionSources (MkQueryAbstractSyntaxTree fields baseTable joins) = concat $ map getExpressionSources' fields

getExpressionSourcesVect : (ast : QueryAbstractSyntaxTree) -> Vect (length (getExpressionSources ast)) TableName
getExpressionSourcesVect ast = fromList (getExpressionSources ast)

----
getQuerySources : (ast : QueryAbstractSyntaxTree) -> List TableName
getQuerySources ast =
    let
        querySources'   = map querySourceFromTableJoining (joins ast)
        querySources    = (baseTable ast) ++ querySources'
        maybeNames      = map querySourceName querySources
    in
        onlyJust maybeNames

getQuerySourcesVect : (ast : QueryAbstractSyntaxTree) -> Vect (length (getQuerySources ast)) TableName
getQuerySourcesVect ast = fromList (getQuerySources ast)
