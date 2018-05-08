module Language

import SqlTypes
import Database

-- import Control.ST
import Control.Monad.State
import Data.So
import Data.Vect

data FixedPoint : (f : Type -> Type) -> Type where
    MkFixedPoint   : f (FixedPoint f) -> FixedPoint f


data ColumnExpression : SqlType -> Type where
    BooleanLiteral  : Bool -> ColumnExpression BOOLEAN
    TextLiteral     : String -> ColumnExpression TEXT
    IntegerLiteral  : Int -> ColumnExpression INTEGER
    FloatLiteral    : Double -> ColumnExpression FLOAT

    Column          : {columnType : SqlType} -> (columnName : String) -> ColumnExpression columnType
    ColumnInTable   : {columnType : SqlType} -> (tableName : String) -> (columnName : String) -> ColumnExpression columnType

    ColumnAs        : {columnType : SqlType} -> (columnName : String) -> (columnAlias : String) -> ColumnExpression columnType
    ColumnInTableAs : {columnType : SqlType} -> (tableName : String) -> (columnName : String) -> (columnAlias : String) -> ColumnExpression columnType

    Alias           : {aliasType : SqlType} -> (columnName : String) -> ColumnExpression aliasType

    -- TODO use (Num t =>) constraint instead
    (+)             : {auto prf : SqlTypeIsNumeric t} -> ColumnExpression t -> ColumnExpression t -> ColumnExpression t
    (-)             : {auto prf : SqlTypeIsNumeric t} -> ColumnExpression t -> ColumnExpression t -> ColumnExpression t

    -- TODO use (Eq t =>) constraint instead
    (==)            : ColumnExpression t -> ColumnExpression t -> ColumnExpression BOOLEAN

    -- TODO use (Ord t =>) constraint instead
    (>)             : {auto prf : SqlTypeIsNumeric t} -> ColumnExpression t -> ColumnExpression t -> ColumnExpression BOOLEAN
    (<)             : {auto prf : SqlTypeIsNumeric t} -> ColumnExpression t -> ColumnExpression t -> ColumnExpression BOOLEAN
    (<=)            : {auto prf : SqlTypeIsNumeric t} -> ColumnExpression t -> ColumnExpression t -> ColumnExpression BOOLEAN
    (>=)            : {auto prf : SqlTypeIsNumeric t} -> ColumnExpression t -> ColumnExpression t -> ColumnExpression BOOLEAN

    And             : ColumnExpression BOOLEAN -> ColumnExpression BOOLEAN -> ColumnExpression BOOLEAN
    Or              : ColumnExpression BOOLEAN -> ColumnExpression BOOLEAN -> ColumnExpression BOOLEAN

data AnyColumnExpression : Type where
    MkAnyColumnExpression : ColumnExpression sqlType -> AnyColumnExpression

AnyColumnExpression' : Type
AnyColumnExpression' = (sqlType ** ColumnExpression sqlType)



-- namespace TableJoinExpression
--     data TableJoiningState = NoTables | HasTables

--     data TableJoinExpression : (result : Type) -> (before : TableJoiningState) -> (after : TableJoiningState) -> Type where
--         Empty           : TableJoinExpression () NoTables NoTables
--         SingleTable     : (tableName : String) -> TableJoinExpression () NoTables HasTables
--         InnerJoin       : (tableName : String) -> (joinExpression : ColumnExpression BOOLEAN) -> TableJoinExpression () HasTables HasTables
--         LeftJoin        : (tableName : String) -> (joinExpression : ColumnExpression BOOLEAN) -> TableJoinExpression () HasTables HasTables
--         RightJoin       : (tableName : String) -> (joinExpression : ColumnExpression BOOLEAN) -> TableJoinExpression () HasTables HasTables

--         Pure            : a -> TableJoinExpression a before after
--         (>>=)           : TableJoinExpression a st1 st2 -> (a -> TableJoinExpression b st2 st3) -> TableJoinExpression b st1 st3


-- cons : a -> List a -> List a
-- cons = Prelude.List.(::)

-- extractTableNames : TableJoinExpression a before after -> List String
-- extractTableNames expr =
--     execState (extractTableNamesHelper expr) []
--     where
--         extractTableNamesHelper : TableJoinExpression a before after -> State (List String) a
--         extractTableNamesHelper Empty = put Prelude.List.Nil
--         extractTableNamesHelper (SingleTable tableName) = modify (cons tableName)
--         extractTableNamesHelper (InnerJoin tableName joinExpression) = modify (cons tableName)
--         extractTableNamesHelper (LeftJoin tableName joinExpression) = modify (cons tableName)
--         extractTableNamesHelper (RightJoin tableName joinExpression) = modify (cons tableName)
--         extractTableNamesHelper (Pure x) = pure x
--         extractTableNamesHelper (x >>= f) = do
--             res <- extractTableNamesHelper x
--             extractTableNamesHelper (f res)

data TableJoiningType = Inner | Outer | Left | Right
data TableJoining = MkTableJoining TableJoiningType (ColumnExpression BOOLEAN)

record QueryAbstractSyntaxTree where
    constructor MkQueryAbstractSyntaxTree

    distinct        : Bool

    fields          : List AnyColumnExpression'
    baseTable       : Maybe String
    joins           : List TableJoining
    -- tables          : TableJoinExpression () before after
    -- default value will be just `TRUE`
    whereCondition  : ColumnExpression BOOLEAN


data TableJoiningState = NoTables | HasTables

record QueryAstState where
    constructor MkQueryAstState

    joinState               : TableJoiningState


data SqlQueryParts : (before : QueryAstState) -> (after : QueryAstState) -> (result : Type) -> Type where
    Select :
        List AnyColumnExpression'
        -> SqlQueryParts
            (MkQueryAstState
                joinState
            )
            (MkQueryAstState
                joinState
            )
            a
    AlsoSelect :
        List AnyColumnExpression'
        -> SqlQueryParts
            (MkQueryAstState
                joinState
            )
            (MkQueryAstState
                joinState
            )
            ()

    From :
        (tableName : String)
        -> SqlQueryParts
            (MkQueryAstState
                NoTables
            )
            (MkQueryAstState
                HasTables
            )
            ()


    Pure            : a -> SqlQueryParts before before a
    -- (>>=)           : SqlQueryParts a st1 st2 -> (a -> SqlQueryParts b st2 st3) -> SqlQueryParts b st1 st3

implementation Functor (SqlQueryParts before after) where
    map func (Select xs) = ?Functor_rhs_2
    map func (AlsoSelect xs) = ?Functor_rhs_3
    map func (From tableName) = ?Functor_rhs_4
    map func (Pure x) = ?Functor_rhs_5

