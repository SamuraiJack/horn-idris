module Algebra2

data Lit = 
    StrLit String
    | IntLit Int
    | Ident String

data Expr = 
    Index Expr Expr
    | Call Expr (List Expr)
    | Unary String Expr
    | Binary Expr String Expr
    | Paren Expr
    | Literal Lit

data Stmt = 
    Break 
    | Continue
    | Empty
    | IfElse Expr (List Stmt) (List Stmt)
    | Return (Maybe Expr)
    | While Expr (List Stmt)
    | Expression Expr


applyExpr : (f : Expr -> Expr) -> (exp : Expr) -> Expr  
applyExpr f (Index x y) = Index (f x) (f y)
applyExpr f (Call x xs) = Call (f x) (map f xs)
applyExpr f (Unary op arg) = Unary op (f arg)
applyExpr f (Binary l op r) = Binary (f l) op (f r)
applyExpr f (Paren x) = Paren (f x)
applyExpr f (Literal x) = Literal x


flatten : Expr -> Expr 
flatten (Paren x) = flatten x
flatten exp = applyExpr flatten exp
