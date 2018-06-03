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
SourceNameResolvesCorrectly : (ast : QueryAbstractSyntaxTree) -> (sourceName : TableName) -> Type
SourceNameResolvesCorrectly ast sourceName = Elem sourceName (getQuerySourcesVect ast)

sourceNameResolvesCorrectly : (ast : QueryAbstractSyntaxTree) -> (sourceName : TableName) -> Dec (SourceNameResolvesCorrectly ast sourceName)
sourceNameResolvesCorrectly ast sourceName = isElem sourceName (getQuerySourcesVect ast)

----
AllSourceNamesResolvesCorrectly : (ast : QueryAbstractSyntaxTree) -> Type
AllSourceNamesResolvesCorrectly ast = ForEveryElementVect (getExpressionSourcesVect ast) (SourceNameResolvesCorrectly ast)

allSourceNamesResolvesCorrectly : (ast : QueryAbstractSyntaxTree) -> Dec (AllSourceNamesResolvesCorrectly ast)
allSourceNamesResolvesCorrectly ast =
    forEveryElementVect
        {A = TableName}
        (getExpressionSourcesVect ast)
        (SourceNameResolvesCorrectly ast)
        (sourceNameResolvesCorrectly ast)
