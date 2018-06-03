module Language.Property.QueryHasExactlyOneBaseTable

import SqlTypes
import Database
import Util
import Language.PartialQuery

%default total
%access public export

----
QueryHasExactlyOneBaseTable : (ast : QueryAbstractSyntaxTree) -> Type
QueryHasExactlyOneBaseTable ast = ListHasExactlyOneElement QuerySource (baseTableAcc ast)

queryHasExactlyOneBaseTable : (ast : QueryAbstractSyntaxTree) -> Dec (QueryHasExactlyOneBaseTable ast)
queryHasExactlyOneBaseTable ast = listHasExactlyOneElement (baseTable ast)


-- ----
-- data QueryHasExactlyOneBaseTable : (ast : QueryAbstractSyntaxTree) -> Type where
--     Because     : { ast : QueryAbstractSyntaxTree }
--         -> { auto prf : ListHasExactlyOneElement QuerySource (baseTableAcc ast) }
--         -> QueryHasExactlyOneBaseTable ast
--
-- noColsProof : (p : [] = baseTableAcc ast) -> (tableProof : QueryHasExactlyOneBaseTable ast) -> Void
-- noColsProof p tableProof = assert_total $ case tableProof of
--     Because {ast} {prf} => ?zxc
--         -- case p of
--         --     Refl => ?zxc
--
-- twoAndMoreProof : (p : (x :: (y :: xs)) = baseTableAcc ast) -> (colProof : QueryHasExactlyOneBaseTable ast) -> Void
-- -- twoAndMoreProof p (Because {ast} {prf=singleColProof}) = assert_total $ case singleColProof of
-- --     Because impossible
--
-- queryHasExactlyOneBaseTable : (ast : QueryAbstractSyntaxTree) -> Dec (QueryHasExactlyOneBaseTable ast)
-- queryHasExactlyOneBaseTable ast with (baseTableAcc ast) proof p
--
--     queryHasExactlyOneBaseTable ast | ([]) = assert_total $
--         No (\colProof => noColsProof p colProof)
--
--     queryHasExactlyOneBaseTable ast | (x :: []) = assert_total $
--         Yes $ Because {ast = ast} {prf = rewrite sym p in (Because {x = x})}
--
--     queryHasExactlyOneBaseTable ast | (x :: y :: xs) = assert_total $
--         No (\colProof => twoAndMoreProof p colProof)
