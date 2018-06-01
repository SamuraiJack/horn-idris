module Language.Property.AllColumnReferencesAreUnambigous

{-

SELECT
    id, name, salary
FROM
    "User" AS u
LEFT JOIN
    "Company" as c on u.company_id = c.id

====
ERROR:  column reference "id" is ambiguous
LINE 2:     id, name, salary
            ^

********** Error **********

ERROR: column reference "id" is ambiguous
SQL state: 42702
Character: 13

-}

import SqlTypes
import Database
import Util
import Language

import Data.Vect

%default total
%access public export

----
data ColumnReferenceIsUnambigous : (ast : QueryAbstractSyntaxTree) -> (sourceName : TableName) -> Type where
    Indeed : {auto prf : Elem sourceName (getQuerySourcesVect ast) } -> ColumnReferenceIsUnambigous ast sourceName


contra' : (contra : Elem sourceName (getQuerySourcesVect ast) -> Void) -> (prf : ColumnReferenceIsUnambigous ast sourceName) -> Void
contra' contra (Indeed {prf = prf'}) = contra prf'

sourceNameResolvesCorrectly : (ast : QueryAbstractSyntaxTree) -> (sourceName : TableName) -> Dec (ColumnReferenceIsUnambigous ast sourceName)
sourceNameResolvesCorrectly ast sourceName = case isElem sourceName (getQuerySourcesVect ast) of
    Yes prf => Yes $ Indeed {prf = prf}
    No contra => No (contra' contra)


----
data AllColumnReferencesAreUnambigous : (ast : QueryAbstractSyntaxTree) -> Type where
    IndeedAll : ForEveryElementVect (getExpressionSourcesVect ast) (ColumnReferenceIsUnambigous ast) -> AllColumnReferencesAreUnambigous ast

contra'' :
    (contra : ForEveryElementVect sourceNames (ColumnReferenceIsUnambigous ast) -> Void)
    -> (decision : Dec (ForEveryElementVect sourceNames (ColumnReferenceIsUnambigous ast)))
    -> (p : sourceNames = getExpressionSourcesVect ast)
    -> AllColumnReferencesAreUnambigous ast -> Void
contra'' contra decision prfNames (IndeedAll prfEvery) = case prfEvery of
    EmptyListOk impossible
    (NextElOk _ _) impossible

allColumnReferencesAreUnambigous : (ast : QueryAbstractSyntaxTree) -> Dec (AllColumnReferencesAreUnambigous ast)
allColumnReferencesAreUnambigous ast with (getExpressionSourcesVect ast) proof p
    allColumnReferencesAreUnambigous ast | (sourceNames) =
        let
            decision    = forEveryElementVect {A = TableName} sourceNames (ColumnReferenceIsUnambigous ast) (sourceNameResolvesCorrectly ast)
        in
            case decision of
                (Yes prf) => Yes $ IndeedAll (rewrite sym p in prf)
                (No contra) => No (contra'' contra decision p)
