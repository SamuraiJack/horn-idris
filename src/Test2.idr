module Language

%default total

mutual
    data Base : Type where
        MkBase1         : Base
        As              : (source : Base) -> {auto prf : Predicate source} -> Base

    data Predicate : Base -> Type where
        MkPred          : Predicate MkBase1

some : Base

some = As MkBase1

s : Not (Predicate a)
s prf = ?s_rhs



{-

*Playground> :l Test2.i
/home/nickolay/workspace/Idris/horn/src/Test2.idr:18:1-28:
   |
18 | some = MkBase1name" `As` "n"
   | ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Language.some is possibly not total due to: Language.BecauseItIsTable

*Test2>

-}