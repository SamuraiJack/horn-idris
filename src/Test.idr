module Language

import SqlTypes
import Database

import Control.ST
import Control.Monad.State
import Data.So


namespace TableJoinExpression
    data TableJoinExpression : Type where
        Empty           : TableJoinExpression
        SingleTable     : (tableName : String) -> TableJoinExpression
        InnerJoin       : (tableName : String) -> TableJoinExpression
        LeftJoin        : (tableName : String) -> TableJoinExpression
        RightJoin       : (tableName : String) -> TableJoinExpression

        Pure            : a -> TableJoinExpression
        (>>=)           : TableJoinExpression -> (a -> TableJoinExpression) -> TableJoinExpression

cons : a -> List a -> List a
cons = Prelude.List.(::)

-- extractTableNames : TableJoinExpression -> List String
-- extractTableNames expr =
--     execState (extractTableNamesHelper expr) []
--     where
--         extractTableNamesHelper : TableJoinExpression -> State (List String) ()
--         extractTableNamesHelper Empty = put Prelude.List.Nil
--         extractTableNamesHelper (SingleTable tableName) = modify (cons tableName)
--         extractTableNamesHelper (InnerJoin tableName) = modify (cons tableName)
--         extractTableNamesHelper (LeftJoin tableName) = modify (cons tableName)
--         extractTableNamesHelper (RightJoin tableName) = modify (cons tableName)
--         extractTableNamesHelper (Pure x) = pure ()
--         extractTableNamesHelper (x >>= f) = do
--             res <- extractTableNamesHelper x
--             extractTableNamesHelper ?aa--(f res)


-- zz : TableJoinExpression
-- zz = do
--     Empty
--     SingleTable "User"

data Toy' b =
    Output' b (Toy' b)
    | Bell' (Toy' b)
    | Done'


data Toy b next =
    Output b next
    | Bell next
    | Done

data Fix : (f : Type -> Type) -> Type where 
    MkFix   : f (Fix f) -> Fix f


Fix' : (f : Type -> Type) -> Type
Fix' f = f (Fix' f)

fix : (f : (a -> a) -> (a -> a)) -> a -> a
fix f x = f (fix f) x

fac_ : (f : Lazy (Int -> Int)) -> (n : Int) -> Int
fac_ f n =
    case n <= 0 of
        True => 1
        False => n * f (n - 1)

-- fac : Int -> Int        
-- fac = fix fac_

{-
fac 5 
fix fac_ 5
fac_ (fix fac_) 5
5 * ((fix fac_) 4)
5 * (fix fac_ 4)
-}

fix'' : (f : Lazy (Lazy a -> a)) -> a
fix'' f = f $ (fix'' f)

fac'' : Int -> Int  
fac'' = fix'' fac_
{-
fac'' 5 
fix'' fac_ 5
(fac_ (fix'' fac_)) 5
5 * ((fix fac_) 4)
5 * (fix fac_ 4)
-}

-- -- Y=λf.(λx.f(xx))(λx.f(xx))

-- -- Y : (f : ) -> ()

-- -- Y f = (\x => f (x x)) (\x => f (x x))


-- fix : ((a -> a) -> a -> a) -> a -> a
-- fix f x = f (fix f) x

-- factInt : (Int -> Int) -> Int -> Int
-- factInt f n with (n <= 0)
--   factInt f n | True = 1
--   factInt f n | False = n * f (n - 1)

-- fixed_factInt : Int -> Int
-- fixed_factInt x = fix factInt x

-- data Foo = MkFoo Foo

-- forever : Foo
-- forever = MkFoo forever