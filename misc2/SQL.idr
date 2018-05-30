module SQL

%default total
%access public export

data SqlType = BOOLEAN | INTEGER


mutual
    data ColumnExpression : SqlType -> Type where
        BooleanLiteral  : Bool -> ColumnExpression BOOLEAN
        IntegerLiteral  : Int -> ColumnExpression INTEGER

        SubQueryExpression :
            (query : SqlQuery a)
            -> { auto prf : QueryHasExactlyOneColumn query }
            -> ColumnExpression (getSqlTypeFromQueryWithOneColumn query {prf=prf})

        (+)             : ColumnExpression INTEGER -> ColumnExpression INTEGER -> ColumnExpression INTEGER
        (-)             : ColumnExpression INTEGER -> ColumnExpression INTEGER -> ColumnExpression INTEGER


    AnyColumnExpression' : Type
    AnyColumnExpression' = (sqlType ** ColumnExpression sqlType)


    data SqlQuery : (result : Type) -> Type where
        SelectColumn : AnyColumnExpression' -> SqlQuery ()

        Where : ColumnExpression BOOLEAN -> SqlQuery ()

        (>>=) : SqlQuery a -> (a -> SqlQuery b) -> SqlQuery b


    namespace QueryHasExactlyOneColumn

        data QueryHasNoColumns : (query : SqlQuery a) -> Type where
            OkToStartWithWhere : QueryHasNoColumns (Where boolExpression)
            
            OkToAppendWhereNoCols : 
                {a : Type}
                -> {query : SqlQuery a} 
                -> QueryHasNoColumns query 
                -> QueryHasNoColumns (do query; Where boolExpression)

        data QueryHasExactlyOneColumn : (query : SqlQuery a) -> Type where
            Start : { exp : AnyColumnExpression'} -> QueryHasExactlyOneColumn (SelectColumn exp)
            
            OkToAppendWhere : 
                {a : Type}
                -> {query : SqlQuery a} 
                -> QueryHasExactlyOneColumn query 
                -> QueryHasExactlyOneColumn (do query; Where boolExpression)

            OkToAppendSelectToQueryWOColumns : 
                {sqlType : SqlType}
                -> {a : Type}
                -> {query : SqlQuery a} 
                -> QueryHasNoColumns query 
                -> QueryHasExactlyOneColumn (do query; SelectColumn (sqlType ** columnExpression))

    getSqlTypeFromQueryWithOneColumn : (query : SqlQuery a) -> { auto prf : QueryHasExactlyOneColumn query } -> SqlType
    
    getSqlTypeFromQueryWithOneColumn query {prf} = assert_total (
        case prf of
            Start {exp = (sqlType ** columnExp)} => sqlType
            (OkToAppendWhere {query} prf') => getSqlTypeFromQueryWithOneColumn query {prf=prf'}
            (OkToAppendSelectToQueryWOColumns {sqlType} prfNoColumns) => sqlType
    )


queryHasExactlyOneColumn : (query : SqlQuery a) -> Dec (QueryHasExactlyOneColumn query)
queryHasExactlyOneColumn (SelectColumn exp) = Yes Start
queryHasExactlyOneColumn (Where x) = ?startwhere
queryHasExactlyOneColumn (x >>= f) = case queryHasExactlyOneColumn x of 
    (Yes prf) => ?zz_1
    (No contra) => ?zz_2



query : SqlQuery ()
query = do
    SelectColumn (_ ** IntegerLiteral 11)
    Where $ BooleanLiteral True


onlyOne : QueryHasExactlyOneColumn SQL.query
onlyOne = assert_total $ OkToAppendWhere Start

-- queryType : SqlType
-- queryType = assert_total $ getSqlTypeFromQueryWithOneColumn query

-- subQuery : SqlQuery ()
-- subQuery = assert_total $ do
--     SelectColumn (_ ** SubQueryExpression (do SelectColumn (_ ** IntegerLiteral 11);))

-- onlyOne' : QueryHasExactlyOneColumn SQL.subQuery
-- onlyOne' = Start
