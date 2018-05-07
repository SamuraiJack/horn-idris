module Some

import Data.Vect

data StackCmd : (result : Type) -> (before : Nat) -> (after : Nat) -> Type where
    Push        : Integer -> StackCmd () height (S height)
    Pop         : StackCmd Integer (S height) height
    Top         : StackCmd Integer (S height) (S height)

    GetStr      : StackCmd String height height
    PutStr      : String -> StackCmd () height height

    Pure        : (val : result) -> StackCmd result height height
    (>>=)       : StackCmd a before1 after1 -> (a -> StackCmd b after1 after2) -> StackCmd b before1 after2

-- StackCmdZZ

testAdd : StackCmd Integer 0 0
testAdd = ?testAdd_rhs
-- testAdd = do
--     Push 10
--     Push 20
--     val1 <- Pop
--     val2 <- Pop
--     Pure (val1 + val2)


runStack : (stack : Vect inHeight Integer) -> StackCmd ty inHeight outHeight -> IO (ty, Vect outHeight Integer)
runStack stack (Push x) = pure ((), x :: stack)
runStack (x :: xs) Pop = pure (x, xs)
runStack stack@(x :: xs) Top = pure (x, stack)
runStack stack (Pure val) = pure (val, stack)
runStack stack (x >>= f) = do
    (result, newStack)  <- runStack stack x
    runStack newStack (f result)

namespace StackIOType
    data StackIO : Nat -> Type where
        Do : StackCmd a height1 height2 -> (a -> Inf (StackIO height2)) -> StackIO height1

    (>>=) : StackCmd a height1 height2 -> (a -> Inf (StackIO height2)) -> StackIO height1
    (>>=) = Do

data Fuel = Dry | More (Lazy Fuel)

partial
forever : Fuel
forever = More forever

run : Fuel -> Vect height Integer -> StackIO height -> IO ()
run Dry xs y = pure ()
run (More fuel) stack (Do cmd func) = do
    (res, newStack) <- runStack stack cmd
    run fuel newStack (func res)
