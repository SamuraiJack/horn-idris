module Language.CompleteQuery

import SqlTypes
import Database
import Util
import Language.PartialQuery
import Language.Property.AllSourceNamesResolvesCorrectly
import Language.Property.QueryHasExactlyOneBaseTable

import Control.Monad.State
import Data.Vect
import Data.So

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


partialToComplete2 : (partialQuery : PartialQuery ()) -> IsRight (partialToComplete partialQuery)
partialToComplete2 partialQuery with (partialToComplete partialQuery) proof p
    partialToComplete2 partialQuery | eitherPartial =
        case isRight eitherPartial of
            Yes prf     => prf
            No contra   => ?zc1 --contra (partialToComplete partialQuery)
