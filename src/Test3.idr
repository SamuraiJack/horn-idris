module Language

import Control.Monad.State

%default total

%access public export

data TableJoiningState = NoTables | HasTables


mutual
    record QueryAbstractSyntaxTree where
        constructor MkQueryAbstractSyntaxTree

        distinct        : Bool



    
    record QueryAstState where
        constructor MkQueryAstState

        joinState               : TableJoiningState


    data SqlQueryParts : (result : Type) -> (before : QueryAstState) -> (after : QueryAstState) -> Type where
        From :
            (source : Bool)
            -> SqlQueryParts
                ()
                (MkQueryAstState
                    NoTables
                )
                (MkQueryAstState
                    HasTables
                )

collapseToAst : SqlQueryParts a before after -> QueryAbstractSyntaxTree
collapseToAst x =
    execState (collapseToAstHelper x) (MkQueryAbstractSyntaxTree False)
    where
        collapseToAstHelper : SqlQueryParts a before after -> State QueryAbstractSyntaxTree a

        collapseToAstHelper (From querySource) = ?aa3

