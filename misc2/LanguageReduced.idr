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
    data QuerySource : Type where
        Table           : (tableName : String) -> QuerySource
        SubQuery        : (query : PartialQuery a) -> QuerySource
        AliasAs         : (source : QuerySource) -> (aliasName : String) -> QuerySource

    data ColumnExpression : SqlType -> Type where
        BooleanLiteral  : Bool -> ColumnExpression BOOLEAN
        IntegerLiteral  : Int -> ColumnExpression INTEGER

        Column          : {columnType : SqlType} -> (columnName : String) -> ColumnExpression columnType
        ColumnInTable   : {columnType : SqlType} -> (tableName : String) -> (columnName : String) -> ColumnExpression columnType

        AsExpr          : ColumnExpression sqlType -> (aliasName : String) -> ColumnExpression sqlType

        SubQueryExpression :
            (query : PartialQuery a)
            -> { prf : QueryHasExactlyOneColumn (collapseToAst query) }
            -> ColumnExpression (getSqlTypeFromQueryWithOneColumn (collapseToAst query) {f=prf})

        (+)             : ColumnExpression INTEGER -> ColumnExpression INTEGER -> ColumnExpression INTEGER

    AnyColumnExpression : Type
    AnyColumnExpression = (sqlType ** ColumnExpression sqlType)

    record QueryAbstractSyntaxTree where
        constructor MkQueryAbstractSyntaxTree

        fields          : List AnyColumnExpression
        baseTable       : Maybe QuerySource

    fieldsAcc : QueryAbstractSyntaxTree -> List AnyColumnExpression
    fieldsAcc = fields


    data PartialQuery : (result : Type) -> Type where
        Select          : List AnyColumnExpression -> PartialQuery ()
        Pure            : a -> PartialQuery a
        From            : (source : QuerySource) -> PartialQuery ()
        (>>=)           : PartialQuery a -> (a -> PartialQuery b) -> PartialQuery b


    collapseToAst : PartialQuery a -> QueryAbstractSyntaxTree
    collapseToAst x =
        execState (collapseToAstHelper x) (MkQueryAbstractSyntaxTree [] Nothing)
        where
            collapseToAstHelper : PartialQuery a -> State QueryAbstractSyntaxTree a

            collapseToAstHelper (Select expressions) = do
                modify (record { fields $= (++ expressions) })

            collapseToAstHelper (Pure x) = pure x

            collapseToAstHelper (From querySource) = do
                modify (record { baseTable = Just querySource })

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


tableNamesInExpressions : (ast : QueryAbstractSyntaxTree) -> List TableName

data AllColumnTablePrefixesResolvesToValidSource : (ast : QueryAbstractSyntaxTree) -> Type where





data ProofColumnReferences : Type where


record CompleteQuery where
    constructor MkCompleteQuery

    partialQuery            : PartialQuery ()
    ast                     : QueryAbstractSyntaxTree

    proofColumnReferences   : ProofColumnReferences

-- PartialQuery -> PartialQuery -> Either (ErrorPartialCombination) PartialQuery
--
-- PartialQuery -> Either (ErrorPartialToComplete) CompleteQuery
--
-- CompleteQuery -> Either (ErrorPartialToComplete) ValidQuery

data QueryComputation : (result : Type) -> Type where



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
one_column = LanguageReduced.QueryHasExactlyOneColumn.Because {prf = LanguageReduced.ListHasExactlyOneElement.Because}

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
