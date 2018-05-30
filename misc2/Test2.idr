module Language

import Data.So

%default total

record SomeRec where
    constructor MkSomeRec

    WhereCondition  : Bool

some : (rec : SomeRec) -> {auto so : So (Language.WhereCondition rec)} -> Bool
some rec = ?some_rhs

zz : Bool
zz = some (MkSomeRec True)