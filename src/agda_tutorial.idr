module AgdaTutorial


data DepPair : (A : Type) -> (B : A -> Type) -> Type where
    MkDepPair : (A : Type) -> (Prop : A -> Type) -> DepPair A Prop


data SqlType = BOOLEAN | INTEGER


data ColumnExpression : SqlType -> Type where
    BooleanLiteral  : Bool -> ColumnExpression BOOLEAN
    IntegerLiteral  : Int -> ColumnExpression INTEGER


AnyColumnExpression' : Type
AnyColumnExpression' = DepPair SqlType ColumnExpression
