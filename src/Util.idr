module Util

import Data.So
import Data.Vect

%default total
%access public export

----
namespace ListHasExactlyOneElement
    data ListHasExactlyOneElement : (a : Type) -> List a -> Type where
        Because     : ListHasExactlyOneElement ty (x :: [])

    Uninhabited (ListHasExactlyOneElement a []) where
        uninhabited Because impossible

    Uninhabited (ListHasExactlyOneElement a (x :: y :: xs)) where
        uninhabited Because impossible

getElementFromProof : (prf : ListHasExactlyOneElement ty xs) -> ty
getElementFromProof (Because {x}) = assert_total x


----
namespace ForEveryElement
    data ForEveryElement : {A : Type} -> (list : List A) -> (predicate : A -> Type) -> Type where
        EmptyListOk : ForEveryElement [] predicate
        NextElOk : {A : Type} -> (prev : ForEveryElement {A} xs predicate) -> (prf : predicate el) -> ForEveryElement {A} (el :: xs) predicate


----
namespace ForEveryElementVect
    data ForEveryElementVect : {A : Type} -> (vect : Vect n A) -> (predicate : A -> Type) -> Type where
        EmptyListOk : ForEveryElementVect [] predicate
        NextElOk : {A : Type} -> (prev : ForEveryElementVect {A} xs predicate) -> (prf : predicate el) -> ForEveryElementVect {A} (el :: xs) predicate


    proofContraHead :
        {A : Type}
        -> (contraHead : predicate x -> Void)
        -> (decisionProc : (a : A) -> Dec (predicate a))
        -> ForEveryElementVect (x :: xs) predicate -> Void
    proofContraHead contraHead decisionProc prfEvery = case prfEvery of
        (NextElOk prev prfX) => contraHead prfX

    proofContraTail :
        {A : Type}
        -> (decisionProc : (a : A) -> Dec (predicate a))
        -> (prfHead : predicate x)
        -> (contraTail : ForEveryElementVect xs predicate -> Void)
        -> ForEveryElementVect (x :: xs) predicate -> Void
    proofContraTail decisionProc prfHead contraTail prfEvery = case prfEvery of
        (NextElOk prev prf) => contraTail prev

    forEveryElementVect :
        {A : Type}
        -> (vect : Vect n A)
        -> (predicate : A -> Type)
        -> (decisionProc : (a : A) -> Dec (predicate a))
        -> Dec (ForEveryElementVect {A} vect predicate)

    forEveryElementVect [] predicate decisionProc = Yes EmptyListOk
    forEveryElementVect (x :: xs) predicate decisionProc = case (decisionProc x) of
        (No contraHead) => No (proofContraHead contraHead decisionProc)
        (Yes prfHead) =>
            case (forEveryElementVect xs predicate decisionProc) of
                (No contraTail) => No (proofContraTail decisionProc prfHead contraTail)
                (Yes prfTail) => Yes $ NextElOk prfTail prfHead


----
namespace OnlyJust
    onlyJust : List (Maybe a) -> List a
    onlyJust [] = []
    onlyJust (Nothing :: xs) = onlyJust xs
    onlyJust ((Just x) :: xs) = x :: onlyJust xs


-- getElFromProof : {A : Type} -> {x : A} -> {y : A} -> (prf : x = y) -> A
-- getElFromProof {A} {x} prf = x


-- data SubList : (sub : List a) -> (sup : List a) -> Type where
--     MkSubList : Eq a => (sub : List a) -> (sup : List a) -> So (isInfixOf sub sup) -> SubList sub sup
--
-- subList : Eq a => (sub : List a) -> (sup : List a) -> Dec (SubList sub sup)
-- subList sub sup = case isInfixOf sub sup of
--     True => Yes ?zz --(MkSubList sub sup Oh)
--     False => ?zxc
