module Algebra

data ExprF : (carrier : Type) -> Type where
    Const       : Int -> ExprF carrier
    Add         : (a : carrier) -> (b : carrier) -> ExprF carrier
    Mul         : (a : carrier) -> (b : carrier) -> ExprF carrier


data Fix : (f : Type -> Type) -> Type where
    In : f (Fix f) -> Fix f

implementation Functor ExprF where
    map func (Const int) = Const int
    map func (Add x y) = Add (func x) (func y)
    map func (Mul x y) = Mul (func x) (func y)

Expr : Type
Expr = Fix ExprF

Algebra : (f : Type -> Type) -> (carrier : Type) -> Type
Algebra f carrier = f carrier -> carrier

my : Type
my = Algebra ExprF Int



subList : Eq a => (sub : List a) -> (sup : List a) -> Dec (SubList sub sup)
subList sub sup = case isInfixOf sub sup of
    True => ?zz
    False => ?zxc
