module Language.CompleteQuery

import SqlTypes
import Database
import Util
import Language.PartialQuery
import Language.Property.AllSourceNamesResolvesCorrectly
import Language.Property.QueryHasExactlyOneBaseTable

import Control.Monad.State

%default total
%access public export

----
record CompleteQuery where
    constructor MkCompleteQuery

    partialQuery                    : PartialQuery ()

    proofSingleBaseTable            : QueryHasExactlyOneBaseTable (collapseToAst partialQuery)
    proofAllSourceNamesResolves     : AllSourceNamesResolvesCorrectly (collapseToAst partialQuery)

-- PartialQuery -> PartialQuery -> Either (ErrorPartialCombination) PartialQuery
--
-- PartialQuery -> Either (ErrorPartialToComplete) CompleteQuery
--
-- CompleteQuery -> Either (ErrorPartialToComplete) ValidQuery

----
data ErrorPartialToComplete = MkErrorPartialToComplete String

partialToComplete : PartialQuery () -> Either (ErrorPartialToComplete) CompleteQuery

partialToComplete partialQuery with (collapseToAst partialQuery) proof p
    partialToComplete partialQuery | (ast) =
        case allSourceNamesResolvesCorrectly ast of
            (No contra) => Left (MkErrorPartialToComplete "error1")
            (Yes prfResolves) =>
                case queryHasExactlyOneBaseTable ast of
                    (No contra) => Left (MkErrorPartialToComplete "error2")
                    (Yes prfSingleTable) =>
                        Right (MkCompleteQuery partialQuery (rewrite sym p in prfSingleTable) (rewrite sym p in prfResolves))
