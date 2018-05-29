module LanguageReduced

import Control.Monad.State

%default total
%access public export

data SqlType = BOOLEAN | TEXT | INTEGER | FLOAT | NULLABLE SqlType

namespace ListHasExactlyOneElement
    data ListHasExactlyOneElement : (a : Type) -> List a -> Type where
        Because     : ListHasExactlyOneElement ty (x :: [])

getElementFromProof : (prf : ListHasExactlyOneElement ty xs) -> ty
getElementFromProof (Because {x}) = assert_total x

mutual
    data ColumnExpression : SqlType -> Type where
        BooleanLiteral  : Bool -> ColumnExpression BOOLEAN
        IntegerLiteral  : Int -> ColumnExpression INTEGER

        Column          : {columnType : SqlType} -> (columnName : String) -> ColumnExpression columnType

        SubQueryExpression :
            (query : SqlQueryParts a)
            -> { prf : QueryHasExactlyOneColumn (collapseToAst query) }
            -> ColumnExpression (getSqlTypeFromQueryWithOneColumn (collapseToAst query) {f=prf})

        (+)             : ColumnExpression INTEGER -> ColumnExpression INTEGER -> ColumnExpression INTEGER

    AnyColumnExpression : Type
    AnyColumnExpression = (sqlType ** ColumnExpression sqlType)

    record QueryAbstractSyntaxTree where
        constructor MkQueryAbstractSyntaxTree

        fields          : List AnyColumnExpression

    fieldsAcc : QueryAbstractSyntaxTree -> List AnyColumnExpression
    fieldsAcc = fields


    data SqlQueryParts : (result : Type) -> Type where
        Select          : List AnyColumnExpression -> SqlQueryParts ()
        Pure            : a -> SqlQueryParts a
        (>>=)           : SqlQueryParts a -> (a -> SqlQueryParts b) -> SqlQueryParts b


    collapseToAst : SqlQueryParts a -> QueryAbstractSyntaxTree
    collapseToAst x =
        execState (collapseToAstHelper x) (MkQueryAbstractSyntaxTree [])
        where
            collapseToAstHelper : SqlQueryParts a -> State QueryAbstractSyntaxTree a

            collapseToAstHelper (Select expressions) = do
                modify (record { fields $= (++ expressions) })

            collapseToAstHelper (Pure x) = pure x

            collapseToAstHelper (x >>= f) = do
                res <- collapseToAstHelper x
                collapseToAstHelper (f res)


    namespace QueryHasExactlyOneColumn
        data QueryHasExactlyOneColumn : (ast : QueryAbstractSyntaxTree) -> Type where
            Because     : { ast : QueryAbstractSyntaxTree}
                -> { auto prf : ListHasExactlyOneElement AnyColumnExpression (fields ast) }
                -> QueryHasExactlyOneColumn ast


    getSqlTypeFromQueryWithOneColumn : (query : QueryAbstractSyntaxTree) -> { auto f : QueryHasExactlyOneColumn query } -> SqlType

    getSqlTypeFromQueryWithOneColumn query {f} = assert_total (
        case assert_total f of
            QueryHasExactlyOneColumn.Because {prf} =>
                let
                    (sqlType ** expression) = assert_total $ getElementFromProof prf
                in
                    assert_total sqlType
    )


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


-- EOF mutual


subQuery : SqlQueryParts ()
subQuery = Select [ (INTEGER ** Column "id") ]

one_column : QueryHasExactlyOneColumn (collapseToAst LanguageReduced.subQuery)
one_column = assert_total $ Because

-- subQuery1 : ColumnExpression INTEGER
-- subQuery1 = SubQueryExpression subQuery {prf=one_column}
