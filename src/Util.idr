module Util

import Data.So

%default total
%access public export

namespace ListHasExactlyOneElement
    data ListHasExactlyOneElement : (a : Type) -> List a -> Type where
        Because     : ListHasExactlyOneElement ty (x :: [])

getElementFromProof : (prf : ListHasExactlyOneElement ty xs) -> ty
getElementFromProof (Because {x}) = assert_total x


data ForEveryElement : {A : Type} -> (list : List A) -> (predicate : A -> Type) -> Type where
    EmptyListOk : ForEveryElement [] predicate
    NextElOk : {A : Type} -> (prev : ForEveryElement {A} xs predicate) -> (prf : predicate el) -> ForEveryElement {A} (el :: xs) predicate


data SubList : (sub : List a) -> (sup : List a) -> Type where
    MkSubList : Eq a => (sub : List a) -> (sup : List a) -> So (isInfixOf sub sup) -> SubList sub sup

subList : Eq a => (sub : List a) -> (sup : List a) -> Dec (SubList sub sup)
subList sub sup = case isInfixOf sub sup of
    True => Yes ?zz --(MkSubList sub sup Oh)
    False => ?zxc
