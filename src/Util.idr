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

----
namespace FunctionImage
    data FunctionImage1 : {A, B : Type} -> (f : A -> B) -> A -> B -> Type where
        MkFunctionImage1   : (x : ty) -> FunctionImage1 f x (f x)

    data FunctionImage2 : {A, B, C : Type} -> (f : A -> B -> C) -> A -> B -> C -> Type where
        MkFunctionImage2   : {A, B : Type} -> (a : A) -> (b : B) -> FunctionImage2 f a b (f a b)

    example1 : FunctionImage2 Data.Vect.elem 1 [ 1 ] True
    example1 = MkFunctionImage2 {f=Data.Vect.elem} 1 [ 1 ]

    example2 : FunctionImage2 Data.Vect.elem 1 [ 2 ] False
    example2 = MkFunctionImage2 {f=Data.Vect.elem} 1 [ 2 ]

----
data IsVectElem : {A : Type} -> A -> Vect n A -> Type where
    ItDoes  : {A : Type} -> Eq A => FunctionImage2 (Data.Vect.elem) el vect True -> IsVectElem {A} el vect

----
namespace ListHasExactlyOneElement2
    data ListHasExactlyOneElement2 : {A : Type} -> List A -> Type where
        ItDoes  : {A : Type} -> FunctionImage1 (Prelude.List.length) list 1 -> ListHasExactlyOneElement2 {A} list

    getElementFromProof : (prf : ListHasExactlyOneElement2 {A = ty} xs) -> ty
    getElementFromProof (ItDoes {A = ty} imagePrf) = ?zc_1

-- isVectElem : {A : Type} -> (el : A) -> (vect : Vect n A) -> Dec (IsVectElem el vect)
-- isVectElem x xs with (Data.Vect.elem x xs) proof p
--     isVectElem x xs | (res)    = ?zxc


-- getElFromProof : {A : Type} -> {x : A} -> {y : A} -> (prf : x = y) -> A
-- getElFromProof {A} {x} prf = x


-- data SubList : (sub : List a) -> (sup : List a) -> Type where
--     MkSubList : Eq a => (sub : List a) -> (sup : List a) -> So (isInfixOf sub sup) -> SubList sub sup
--
-- subList : Eq a => (sub : List a) -> (sup : List a) -> Dec (SubList sub sup)
-- subList sub sup = case isInfixOf sub sup of
--     True => Yes ?zz --(MkSubList sub sup Oh)
--     False => ?zxc
