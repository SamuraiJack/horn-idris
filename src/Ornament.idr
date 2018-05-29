module reornament

import Decidable.Order

-- Idris translation of Agda code:
-- https://gist.github.com/gallais/e507832abc6c91ac7cb9

-- Which follows Conor McBride's Ornaments paper:
-- https://personal.cis.strath.ac.uk/conor.mcbride/pub/OAAO/Ornament.pdf

ListAlgebra : (elem : Type) -> (property : Type) -> Type
ListAlgebra elem property = (property, elem -> property -> property)

data ListSpec : (elem : Type) -> {property : Type} -> ListAlgebra elem property -> property -> Type where
    Nil   : {elem, property : Type} -> {alg : ListAlgebra elem property} -> ListSpec elem alg (fst alg)
    (::)  : {elem, property : Type} -> (a : elem) -> {b : property} -> (as : ListSpec elem alg b) -> ListSpec elem alg (snd alg a b)

AlgLength : {A : Type} -> ListAlgebra A Nat
AlgLength = (0, (\_  => succ))

AlgSum : ListAlgebra Nat Nat
AlgSum = (0, (+))

Algx : 
    {elem, property1, property2 : Type} 
    -> (algB : ListAlgebra elem property1) 
    -> (algC : ListAlgebra elem property2) 
    -> ListAlgebra elem (property1, property2)
Algx (prop1, sucProp1) (prop2, sucProp2) = ((prop1, prop2), (\a => \(prop1, prop2) => (sucProp1 a prop1, sucProp2 a prop2)))


HListAlg : ListAlgebra a (List Type)
HListAlg = (
    [],
    (\elem, prop => ?aa)
)


-- using (max_value : Nat, list : List Nat)
--     data AllElementsOfListAreSmallerThan : Type where
--         NoElementsAreSmaller    : AllElementsOfListAreSmallerThan

--         SomeElementsAreSmaller  : { value : Nat } 
--             -> AllElementsOfListAreSmallerThan max_value list 
--             -> { prf : LTE value max_value }
--             -> AllElementsOfListAreSmallerThan max_value (value :: list)


-- alg : AllElementsOfListAreSmallerThan max_value list ->

-- allElementsAreSmallerThan : (value : Nat) -> (list : List Nat) -> Dec (AllElementsOfListAreSmallerThan value list)
-- allElementsAreSmallerThan value [] = Yes NoElementsAreSmaller
-- allElementsAreSmallerThan value (x :: xs) = case decideLTE x value of
--     Yes headProof   => case allElementsAreSmallerThan value xs of
--         (Yes tailProof) => Yes (SomeElementsAreSmaller {value=x} {max_value=value} tailProof {prf=headProof})
--         (No contra)     => ?aa_4
--     No contra       => ?aa_2


-- using (max_value : Nat, list : List Nat)
--     AllElsSmallerAlg : (elem : Nat) -> (prop : AllElementsOfListAreSmallerThan) -> AllElementsOfListAreSmallerThan

--     AlgIncreasing : ListAlgebra Nat (SomeElementsAreSmaller {max_value=10} {value=1} (NoElementsAreSmaller) (LTE 1 10))

-- AlgIncreasing = (
--     NoElementsAreSmaller, 
--     \el, prop => case prop of
--         a  => ?b
-- )


-- Increasing : (elem : Type) -> Ord elem => (maxEl : Maybe elem) -> Type
-- Increasing elem maxEl = ListSpec elem AlgIncreasing maxEl


-- increasing : Increasing Nat (Just 8)
-- increasing = [ 8, 7, 4, 5, 1 ]


Vec : (A : Type) -> (n : Nat) -> Type
Vec A n = ListSpec A AlgLength n


allFin4 : Vec Nat 4
allFin4 = [0, 1, 2, 3]

Distribution : Type
Distribution = ListSpec Nat AlgSum 100

uniform : Distribution
uniform = [25, 24, 25, 25, 1]

SizedDistribution : Nat -> Type
SizedDistribution n = ListSpec Nat (Algx AlgLength AlgSum) (n, 100)

uniform4 : SizedDistribution 4
uniform4 = [25, 25, 25, 25]