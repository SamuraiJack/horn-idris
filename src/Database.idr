module Database

import SqlTypes

%default total
%access public export


TableName : Type
TableName = String

ColumnName : Type
ColumnName = String

DatabaseSchemaName : Type
DatabaseSchemaName = String


record DatabaseColumn where
    constructor MkDatabaseColumn
    name    : ColumnName
    type    : SqlType


record DatabaseTable where
    constructor MkDatabaseTable
    name        : TableName
    columns     : List DatabaseColumn


record DatabaseSchema where
    constructor MkDatabaseSchema
    name        : DatabaseSchemaName
    tables      : List DatabaseTable


tableHasColumn : (table : DatabaseTable) -> (columnName : String) -> Bool
tableHasColumn table columnName = foldl
    (\acc, column => acc || (name column) == columnName)
    False
    (columns table)


databaseHasTable : (dbSchema : DatabaseSchema) -> (tableName : String) -> Bool
databaseHasTable dbSchema tableName = foldl
    (\acc, table => acc || (name table) == tableName)
    False
    (tables dbSchema)



data DatabaseHasTable : (dbSchema : DatabaseSchema) -> (tableName : String) -> Type where
    Here :
        DatabaseHasTable
            (MkDatabaseSchema dbName ((MkDatabaseTable tableName tableColumns) :: xs))
            tableName
    There :
        DatabaseHasTable
            (MkDatabaseSchema dbName tables)
            tableName
        -> DatabaseHasTable
            (MkDatabaseSchema dbName (table :: tables))
            tableName


--  EXAMPLES --

SampleDatabase : DatabaseSchema

SampleDatabase = MkDatabaseSchema
    "SampleDatabase"
    [
        MkDatabaseTable "User" [
            MkDatabaseColumn "id" INTEGER,
            MkDatabaseColumn "name" TEXT,
            MkDatabaseColumn "age" FLOAT
        ],

        MkDatabaseTable "Company" [
            MkDatabaseColumn "id" INTEGER,
            MkDatabaseColumn "name" TEXT,
            MkDatabaseColumn "employeesNum" FLOAT
        ]
    ]
