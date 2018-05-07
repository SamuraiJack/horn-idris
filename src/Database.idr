module Database

import SqlTypes

public export
record DatabaseColumn where
    constructor MkDatabaseColumn
    name    : String
    type    : SqlType


public export
record DatabaseTable where
    constructor MkDatabaseTable
    name        : String
    columns     : List DatabaseColumn


public export
record DatabaseSchema where
    constructor MkDatabaseSchema
    name        : String
    tables      : List DatabaseTable

public export
tableHasColumn : (table : DatabaseTable) -> (columnName : String) -> Bool
tableHasColumn table columnName = foldl
    (\acc, column => acc || (name column) == columnName)
    False
    (columns table)

public export
databaseHasTable : (dbSchema : DatabaseSchema) -> (tableName : String) -> Bool
databaseHasTable dbSchema tableName = foldl
    (\acc, table => acc || (name table) == tableName)
    False
    (tables dbSchema)


public export
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

public export
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
