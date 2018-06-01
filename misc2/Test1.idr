module SomeModule

import Data.Vect

%default total

namespace FunctionImage
    data FunctionImage2 : {A, B, C : Type} -> (f : A -> B -> C) -> A -> B -> C -> Type where
        MkFunctionImage2   : {A, B : Type} -> (a : A) -> (b : B) -> FunctionImage2 f a b (f a b)

    example1 : FunctionImage2 Data.Vect.elem 1 [ 1 ] True
    example1 = MkFunctionImage2 {f=Data.Vect.elem} 1 [ 1 ]

    example2 : FunctionImage2 Data.Vect.elem 1 [ 2 ] False
    example2 = MkFunctionImage2 {f=Data.Vect.elem} 1 [ 2 ]


data IsVectElem : {A : Type} -> A -> Vect n A -> Type where
    ItDoes  : {A : Type} -> Eq A => FunctionImage2 (Data.Vect.elem) el vect True -> IsVectElem {A} el vect

{-
at line 19, character 15, file /home/nickolay/workspace/Idris/horn/misc2/Test1.idr
When checking type of SomeModule.ItDoes:
Can't find implementation for Eq Type
-}
