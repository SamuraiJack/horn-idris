module Language

import Database
import SqlTypes
import Util
import Language.PartialQuery

import Data.Vect

%default total
%access public export

-- Property 1
-- Query source is either a table name or alias name. All query sources (like "select querySource.columnName")
-- should resolve to actual tables, specified in the "From" + "Joins"

----
data SourceNameResolvesCorrectly : (ast : QueryAbstractSyntaxTree) -> (sourceName : TableName) -> Type where
    Indeed : {auto prf : Elem sourceName (getQuerySourcesVect ast) } -> SourceNameResolvesCorrectly ast sourceName


contra' : (contra : Elem sourceName (getQuerySourcesVect ast) -> Void) -> (prf : SourceNameResolvesCorrectly ast sourceName) -> Void
contra' contra (Indeed {prf = prf'}) = contra prf'

sourceNameResolvesCorrectly : (ast : QueryAbstractSyntaxTree) -> (sourceName : TableName) -> Dec (SourceNameResolvesCorrectly ast sourceName)
sourceNameResolvesCorrectly ast sourceName = case isElem sourceName (getQuerySourcesVect ast) of
    Yes prf => Yes $ Indeed {prf = prf}
    No contra => No (contra' contra)


----
data AllSourceNamesResolvesCorrectly : (ast : QueryAbstractSyntaxTree) -> Type where
    IndeedAll : ForEveryElementVect (getExpressionSourcesVect ast) (SourceNameResolvesCorrectly ast) -> AllSourceNamesResolvesCorrectly ast

contra'' :
    (contra : ForEveryElementVect sourceNames (SourceNameResolvesCorrectly ast) -> Void)
    -> (decision : Dec (ForEveryElementVect sourceNames (SourceNameResolvesCorrectly ast)))
    -> (p : sourceNames = getExpressionSourcesVect ast)
    -> AllSourceNamesResolvesCorrectly ast -> Void
contra'' contra decision prfNames (IndeedAll prfEvery) = case prfEvery of
    EmptyListOk impossible
    (NextElOk _ _) impossible

allSourceNamesResolvesCorrectly : (ast : QueryAbstractSyntaxTree) -> Dec (AllSourceNamesResolvesCorrectly ast)
allSourceNamesResolvesCorrectly ast with (getExpressionSourcesVect ast) proof p
    allSourceNamesResolvesCorrectly ast | (sourceNames) =
        let
            decision    = forEveryElementVect {A = TableName} sourceNames (SourceNameResolvesCorrectly ast) (sourceNameResolvesCorrectly ast)
        in
            case decision of
                (Yes prf) => Yes $ IndeedAll (rewrite sym p in prf)
                (No contra) => No (contra'' contra decision p)
