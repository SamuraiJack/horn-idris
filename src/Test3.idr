module Algebra

-- data Expr = Const Int
--           | Add Expr Expr
--           | Mul Expr Expr


data ExprF : (carrier : Type) -> Type where
    Const       : Int -> ExprF carrier
    Add         : (a : carrier) -> (b : carrier) -> ExprF carrier
    Mul         : (a : carrier) -> (b : carrier) -> ExprF carrier


data Fix : (f : Type -> Type) -> Type where
    In : f (Fix f) -> Fix f

unFix : Fix f -> f (Fix f)
unFix (In x) = x

implementation Functor ExprF where
    map func (Const int) = Const int
    map func (Add x y) = Add (func x) (func y)
    map func (Mul x y) = Mul (func x) (func y)

Algebra : (f : Type -> Type) -> Functor f => (carrier : Type) -> Type
Algebra f carrier = f carrier -> carrier

InitialAlgebra : Type
InitialAlgebra = Algebra ExprF (Fix ExprF)

Initial : InitialAlgebra
Initial a = In a

catamorphism : Functor f => Algebra f a -> (Fix f -> a)
catamorphism alg = alg . map ((catamorphism alg)) . (unFix)


-----------------------------------
Expr : Type
Expr = Fix ExprF

val : Expr
val = In $ Add (In $ Const 1) (In $ Const 1)

alg1 : Algebra ExprF Int
alg1 (Const x) = x
alg1 (Add a b) = a + b
alg1 (Mul a b) = a * b


alg2 : Algebra ExprF String
alg2 (Const x) = show x
alg2 (Add a b) = a ++ " + " ++ b
alg2 (Mul a b) = a ++ " * " ++ b

eval1 : Expr -> Int
eval1 = catamorphism alg1




-- data ExprF a = Var String | App a a | Abs String a