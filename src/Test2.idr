module Language

-- %default total

mutual
    data QuerySource : (aliased : Bool) -> Type where
        Table           : (tableName : String) -> QuerySource False
        SubQuery        : Bool -> QuerySource False
        As              : (source : QuerySource False) -> (aliasName : String) -> QuerySource True

    -- data QuerySourceIsNotAliased : QuerySource -> Type where
    --     BecauseItIsTable        : QuerySourceIsNotAliased (Table tableName)
    --     BecauseItIsSubquery     : QuerySourceIsNotAliased (SubQuery query)


some : QuerySource True

some = (Table "name" `As` "n") `As` "n"


{-

*Playground> :l Test2.i
/home/nickolay/workspace/Idris/horn/src/Test2.idr:18:1-28:
   |
18 | some = Table "name" `As` "n"
   | ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Language.some is possibly not total due to: Language.BecauseItIsTable

*Test2>

-}