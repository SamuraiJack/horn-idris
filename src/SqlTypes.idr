module SqlTypes

%default total
%access public export

data SqlType = UNKNOWN | BOOLEAN | TEXT | INTEGER | FLOAT | NULLABLE SqlType

data SqlTypeIsNumeric : (sqlType : SqlType) -> Type where
    BecauseItsInteger   : SqlTypeIsNumeric INTEGER
    BecauseItsFloat     : SqlTypeIsNumeric FLOAT

-- public export
-- makeNullable : SqlType -> SqlType
-- makeNullable x = ?makeNullable_rhs

public export
sqlTypeToIdrisType : SqlType -> Type
sqlTypeToIdrisType BOOLEAN = Bool
sqlTypeToIdrisType TEXT = String
sqlTypeToIdrisType INTEGER = Integer
sqlTypeToIdrisType FLOAT = Double
sqlTypeToIdrisType (NULLABLE x) = Maybe (sqlTypeToIdrisType x)

-- equalSql : (t : SqlType) -> (x, y : sqlTypeToIdrisType t) -> Bool
-- equalSql TEXT x y = x == y
-- equalSql INTEGER x y = x == y
-- equalSql FLOAT x y = x == y
-- equalSql (NULLABLE ty) (Just x) (Just y) = equalSql ty x y
-- equalSql (NULLABLE ty) Nothing Nothing = True
-- equalSql (NULLABLE ty) _ _ = False

-- export showSql : (t : SqlType) -> (x : sqlTypeToIdrisType t) -> String
-- showSql TEXT x = show x
-- showSql INTEGER x = show x
-- showSql FLOAT x = show x
-- showSql (NULLABLE ty) (Just x) = showSql ty x
-- showSql (NULLABLE ty) Nothing = "null"


-- integerNotText : INTEGER = TEXT -> Void
-- integerNotText Refl impossible

-- realNotText : FLOAT = TEXT -> Void
-- realNotText Refl impossible

-- nullableNotText : NULLABLE t = TEXT -> Void
-- nullableNotText Refl impossible

-- realNotInteger : FLOAT = INTEGER -> Void
-- realNotInteger Refl impossible

-- nullableNotInteger : NULLABLE t = INTEGER -> Void
-- nullableNotInteger Refl impossible

-- nullableNotReal : NULLABLE t = FLOAT -> Void
-- nullableNotReal Refl impossible

-- export implementation DecEq SqlType where
--   decEq TEXT TEXT            = Yes Refl
--   decEq INTEGER TEXT         = No integerNotText
--   decEq FLOAT TEXT            = No realNotText
--   decEq (NULLABLE x) TEXT    = No nullableNotText
--   decEq TEXT INTEGER         = No $ integerNotText . sym
--   decEq INTEGER INTEGER      = Yes Refl
--   decEq FLOAT INTEGER         = No realNotInteger
--   decEq (NULLABLE x) INTEGER = No nullableNotInteger
--   decEq TEXT FLOAT            = No $ realNotText . sym
--   decEq INTEGER FLOAT         = No $ realNotInteger . sym
--   decEq FLOAT FLOAT            = Yes Refl
--   decEq (NULLABLE x) FLOAT    = No nullableNotReal
--   decEq TEXT (NULLABLE x)    = No $ nullableNotText . sym
--   decEq INTEGER (NULLABLE x) = No $ nullableNotInteger . sym
--   decEq FLOAT (NULLABLE x)    = No $ nullableNotReal . sym
--   decEq (NULLABLE y) (NULLABLE x) with (decEq y x)
--     decEq (NULLABLE x) (NULLABLE x) | (Yes Refl) = Yes Refl
--     decEq (NULLABLE y) (NULLABLE x) | (No prf) = No $ prf . inside
--       where inside : NULLABLE a = NULLABLE b -> a = b
--             inside Refl = Refl
