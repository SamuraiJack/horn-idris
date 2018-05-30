module ElaboratorTest

import SqlTypes
import Language
import Database

import Data.So

%default total
%language ElabReflection

selectIdAndName : SqlQueryParts () (MkQueryAstState joinState) (MkQueryAstState joinState)
selectIdAndName = do
    Select [
        (INTEGER ** Column "id")
        -- ,
        -- (INTEGER ** Column "id")
        -- ,
        -- (_ ** SubQueryExpression $ Select {joinState = NoTables} [ (INTEGER ** Column "id") ])
    
        -- ,
        -- (_ ** Column {columnType = TEXT} "name")
    ]

subQuery'' : SqlQueryParts () (MkQueryAstState NoTables) (MkQueryAstState NoTables)
subQuery'' = Select {joinState = NoTables} [ (INTEGER ** Column "id") ]

data MyVect : (elem : Type) -> (n : Nat) -> Type where
    Nil     : MyVect elem Z
    (::)    : (a : elem) -> MyVect elem k -> MyVect elem (S k)

-- triv : Elab ()
-- triv = do 
--     compute
--     g <- getGoal
--     case (snd g) of
--         `(MyVect ~elem ~len : Type)    => do 
--             fill `([] : MyVect)
--             solve
--         `(Nat : Type)    => do 
--             fill `(1 : Nat)
--             solve
--         `(() : Type)    => do 
--             fill `(() : ())
--             solve
--         otherGoal       => fail [ TermPart otherGoal, TextPart "is not trivial" ]

-- zxc : ()
-- zxc = %runElab triv

-- zzz : Nat
-- zzz = %runElab triv

-- zz1 : MyVect Nat 5
-- zz1 = %runElab triv

-- triv : Elab ()
-- triv = do 
--     compute
--     g <- getGoal
--     case (snd g) of
--         `(~v : QueryHasExactlyOneColumn)    => do 
--             fill `(Because ~v)
--             solve
--         otherGoal       => fail [ TextPart "Can't solve QueryHasExactlyOneColumn" ]


mkId : Elab ()
mkId = do 
    x <- gensym "x"
    attack
    intro x
    fill (Var x); solve
    solve -- the attack

idNat : Nat -> Nat
idNat = %runElab mkId

buildQueryHasExactlyOneColumn : Elab ()
buildQueryHasExactlyOneColumn = do 
    (name, tt) <- getGoal
    ?aa
    case tt of
        App z x => 
            -- fill (`(Because ~(x)))
            solve
        _       => 
            fail [ TextPart "No app" ]

-- -- (x) <- gensym "x"
-- -- attack
-- -- intro x
-- -- fill (Var x); solve
-- -- solve -- the attack

one_column' : QueryHasExactlyOneColumn (collapseToAst ElaboratorTest.subQuery'')
one_column' = Because


-- subQuery' : AnyColumnExpression'
-- subQuery' = (_ ** SubQueryExpression $ Select {joinState = NoTables} [ (INTEGER ** Column "id") ])

ast : QueryAbstractSyntaxTree
ast = query (selectIdAndName {joinState=NoTables})

-- bb : QueryAbstractSyntaxTree
-- bb = MkQueryAbstractSyntaxTree False
--     [(INTEGER **
--         Column "id")]
--     Nothing
--     []
--     (BooleanLiteral True)

-- cc : QueryHasExactlyOneColumn Playground.bb
-- cc = (assert_total Because) Playground.bb

-- subQuery : ColumnExpression INTEGER
-- subQuery = SubQueryExpression ast

one_column : QueryHasExactlyOneColumn ElaboratorTest.ast
one_column = Because

-- joinWithZZ : SqlQueryParts () (MkQueryAstState HasTables) (MkQueryAstState HasTables)
-- joinWithZZ = do
--     LeftJoin (Table "Company") (BooleanLiteral True)


-- selectFromUser : SqlQueryParts () (MkQueryAstState NoTables) (MkQueryAstState HasTables)
-- selectFromUser = do
--     From (Table "User" `AsSource` "U")

-- aa : QuerySource
-- aa = Table "User" `AsSource` "U"

-- whereCond : SqlQueryParts () (MkQueryAstState joinState) (MkQueryAstState joinState)
-- whereCond = do
--     Where (Column {columnType = TEXT} "name" == TextLiteral "Some")


-- wholeQuery : SqlQueryParts () (MkQueryAstState NoTables) (MkQueryAstState HasTables)
-- wholeQuery = do
--     selectIdAndName
--     selectFromUser
--     whereCond
--     joinWithZZ




-- -- compiled : Query SampleDatabase
-- -- compiled = compileQueryForDatabase wholeQuery
