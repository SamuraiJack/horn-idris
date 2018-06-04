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

    listHasExactlyOneElement : (list : List a) -> Dec (ListHasExactlyOneElement a list)
    listHasExactlyOneElement ([]) = No absurd
    listHasExactlyOneElement (x :: []) = Yes Because
    listHasExactlyOneElement (x :: y :: xs) = No absurd

    getElFromExactlyOne : (prf : ListHasExactlyOneElement ty xs) -> ty
    getElFromExactlyOne (Because {x}) = x


----
namespace Both
    data Both : {A : Type} -> (value : A) -> (predicate1 : A -> Type) -> (predicate2 : A -> Type) -> Type where
        MkBoth : {A : Type} -> (prf1 : predicate1 value) -> (prf2 : predicate2 value) -> Both {A} value predicate1 predicate2


----
namespace ForEveryElementList
    data ForEveryElementList : {A : Type} -> (list : List A) -> (predicate : A -> Type) -> Type where
        EmptyListOk : ForEveryElementList [] predicate
        NextElOk : {A : Type} -> (prev : ForEveryElementList {A} xs predicate) -> (prf : predicate el) -> ForEveryElementList {A} (el :: xs) predicate


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
namespace IsRight
    IsRight' : {a, b : Type} -> Either a b -> Type
    -- IsRight' (Left l) = const Void
    -- IsRight' {b} (Right r) = b

    data IsRight : {a, b : Type} -> Either a b -> Type where
        MkIsRight : {B : Type} -> (b : B) -> IsRight (Right b)

    Uninhabited (IsRight (Left a)) where
        uninhabited MkIsRight impossible

    isRight : {a, b : Type} -> (e : Either a b) -> Dec (IsRight e)
    isRight (Left l) = No absurd
    isRight (Right r) = Yes (MkIsRight r)


    verifyNotNull : Nat -> Either String Nat
    verifyNotNull Z = Left "is zero"
    verifyNotNull k = Right k

    safeNotZero : (a : Nat) -> IsRight' (verifyNotNull a) -> Nat

    -- onlyJust : List (Maybe a) -> List a
    -- onlyJust [] = []
    -- onlyJust (Nothing :: xs) = onlyJust xs
    -- onlyJust ((Just x) :: xs) = x :: onlyJust xs


----
namespace FunctionImage
    data FunctionImage1 : {A, B : Type} -> (f : A -> B) -> A -> B -> Type where
        MkFunctionImage1   : {A : Type} -> (x : A) -> FunctionImage1 f x (f x)

    extractArgument1: {A, B : Type} -> {f : A -> B} -> {a : A} -> {b : B} -> (prf : FunctionImage1 f a b) -> A
    extractArgument1 {a} prf = a

    extractImage1: {A, B : Type} -> {f : A -> B} -> {a : A} -> {b : B} -> (prf : FunctionImage1 f a b) -> B
    extractImage1 {b} prf = b

    data FunctionImage2 : {A, B, C : Type} -> (f : A -> B -> C) -> A -> B -> C -> Type where
        MkFunctionImage2   : {A, B : Type} -> (a : A) -> (b : B) -> FunctionImage2 f a b (f a b)

    data FunctionImage3 : {A, B : Type} -> (f : A -> B) -> (a : A) -> (prf : f a = b) -> Type where
        MkFunctionImage3   : {A, B : Type} -> (a : A) -> FunctionImage3 f a Refl

    example1 : FunctionImage2 Data.Vect.elem 1 [ 1 ] True
    example1 = MkFunctionImage2 {f=Data.Vect.elem} 1 [ 1 ]

    example2 : FunctionImage2 Data.Vect.elem 1 [ 2 ] False
    example2 = MkFunctionImage2 {f=Data.Vect.elem} 1 [ 2 ]

    sum : Vect n Nat -> Nat
    sum = foldr (+) 0

    example3 : FunctionImage1 (Util.FunctionImage.sum) [ 1, 2 ] 3
    example3 = MkFunctionImage1 [ 1, 2 ]

    some : Vect 2 Nat
    some = extractArgument1 example3

----
-- data IsVectElem : {A : Type} -> A -> Vect n A -> Type where
--     ItDoes  : {A : Type} -> Eq A => FunctionImage2 (Data.Vect.elem) el vect True -> IsVectElem {A} el vect

----
-- namespace ListHasExactlyOneElement2
--     data ListHasExactlyOneElement2 : {A : Type} -> (list : List A) -> Type where
--         ItDoes  : {A : Type} -> {list : List A} -> FunctionImage1 (Prelude.List.length) list 1 -> ListHasExactlyOneElement2 {A} list
--
--     lemma1 : (p : warg = length list) -> ListHasExactlyOneElement2 list -> Void
--     -- lemma1 prf prfList = case prfList of
--     --     (ItDoes (MkFunctionImage1 list)) => ?zzz
--
--     listHasExactlyOneElement : {A : Type} -> (list : List A) -> Dec (ListHasExactlyOneElement2 {A} list)
--     listHasExactlyOneElement list with (length list) proof p
--         listHasExactlyOneElement {A} list | (S Z) = Yes (ItDoes {A} {list} (rewrite p in MkFunctionImage1 list))
--         listHasExactlyOneElement list | (_) = No (lemma1 p)
--
--
--     getElFromExactlyOne : (prf : ListHasExactlyOneElement2 {A = ty} list) -> ty
--     getElFromExactlyOne (ItDoes {A = ty} {list} imagePrf) with (Prelude.List.length list) proof p
--         getElFromExactlyOne (ItDoes {A = ty} {list} imagePrf) | S Z = ?zz
--
--         getElFromExactlyOne (ItDoes {A = ty} {list} imagePrf) | _ = ?zc_2
--
-- namespace ListHasExactlyOneElement3
--     data ListHasExactlyOneElement3 : {A : Type} -> (list : List A) -> Type where
--         ItDoes  : {A : Type} -> {list : List A} -> FunctionImage3 (Prelude.List.length) list Refl -> ListHasExactlyOneElement3 {A} list
--
--     getElFromExactlyOne : (prf : ListHasExactlyOneElement3 {A = ty} list) -> ty
--     getElFromExactlyOne (ItDoes x) = ?getElFromExactlyOne_rhs_1
--
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
