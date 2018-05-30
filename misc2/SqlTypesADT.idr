module SqlTypes

%default total
%access public export

data Extension : Type where
    Undecorated     : Extension
    TC              : Extension
    PE              : Extension

Transformation : Type
Transformation = Extension -> Type

S_BooleanTransformations : Transformation
S_BooleanTransformations Undecorated = ()
S_BooleanTransformations TC = ()
S_BooleanTransformations PE = ()

S_TextTransformations : Transformation
S_TextTransformations PE = ?S_TextTransformations_rhs_2
S_TextTransformations TC = ?S_TextTransformations_rhs_1
S_TextTransformations Undecorated = ()

S_IntegerTransformations : Transformation
S_IntegerTransformations PE = ?S_IntegerTransformations_rhs_2
S_IntegerTransformations TC = ?S_IntegerTransformations_rhs_1
S_IntegerTransformations Undecorated = ()

S_FloatTransformations : Transformation
S_FloatTransformations PE = ?S_FloatTransformations_rhs_1
S_FloatTransformations TC = Double
S_FloatTransformations Undecorated = ()

data NewConstructor_PE = MkNewConstructor_PE Int String

S_ExtensionTransformations : Transformation
S_ExtensionTransformations PE = NewConstructor_PE
S_ExtensionTransformations TC = ?S_ExtensionTransformations_rhs_1
S_ExtensionTransformations Undecorated = ()

data SqlTypesAtomic : (extension : Extension) -> Type where
    S_Boolean   : (ext : S_BooleanTransformations extension) -> SqlTypesAtomic extension
    S_Text      : (ext : S_TextTransformations extension) -> SqlTypesAtomic extension
    S_Integer   : (ext : S_IntegerTransformations extension) -> SqlTypesAtomic extension
    S_Float     : (ext : S_FloatTransformations extension) -> SqlTypesAtomic extension
    S_Extension : (ext : S_ExtensionTransformations extension) -> SqlTypesAtomic extension

SqlTypesAtomic_Undecorated : Type
SqlTypesAtomic_Undecorated = SqlTypesAtomic Undecorated

-- S_Boolean_Undecorated : SqlTypesAtomic_Undecorated
-- S_Boolean_Undecorated = S_Boolean ()

pattern syntax "S_Boolean_Undecorated" = S_Boolean ()
term syntax "S_Boolean_Undecorated" = the (SqlTypesAtomic_Undecorated) (S_Boolean ())

interpret : SqlTypesAtomic_Undecorated -> Type
interpret (S_Boolean_Undecorated) = Bool
interpret (S_Text ext) = ?interpret_rhs_2
interpret (S_Integer ext) = ?interpret_rhs_3
interpret (S_Float ext) = ?interpret_rhs_4
interpret S_Extension = ?interpret_rhs_5


SqlTypesAtomic_TC : Type
SqlTypesAtomic_TC = SqlTypesAtomic TC

pattern syntax "S_Float_TC" [ext] = S_Float ext
term syntax "S_Float_TC" [value] = the (SqlTypesAtomic_TC) (S_Float value)

interpretTC : SqlTypesAtomic_TC -> Type
interpretTC (S_Boolean ext) = ?interpretTC_rhs_1
interpretTC (S_Text ext) = ?interpretTC_rhs_2
interpretTC (S_Integer ext) = ?interpretTC_rhs_3
interpretTC (S_Float_TC ext) = ?interpretTC_rhs_4
interpretTC (S_Extension ext) = ?interpretTC_rhs_5


SqlTypesAtomic_PE : Type
SqlTypesAtomic_PE = SqlTypesAtomic PE

pattern syntax "S_NewConstructor_PE" [int] [string] = S_Extension (MkNewConstructor_PE int string)
term syntax "S_NewConstructor_PE" [int] [string] = the (SqlTypesAtomic_PE) (S_Extension (MkNewConstructor_PE int string))

interpretPE : SqlTypesAtomic_PE -> Type
interpretPE (S_Boolean ext) = ?interpretPE_rhs_1
interpretPE (S_Text ext) = ?interpretPE_rhs_2
interpretPE (S_Integer ext) = ?interpretPE_rhs_3
interpretPE (S_Float ext) = ?interpretPE_rhs_4
interpretPE (S_NewConstructor_PE int string) = ?interpretPE_rhs_5

-- sqlTypeToIdrisType : SqlType -> Type
-- sqlTypeToIdrisType BOOLEAN = Bool
-- sqlTypeToIdrisType TEXT = String
-- sqlTypeToIdrisType INTEGER = Integer
-- sqlTypeToIdrisType FLOAT = Double
-- sqlTypeToIdrisType (NULLABLE x) = Maybe (sqlTypeToIdrisType x)

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


-- integerNotText : INTEGER = TEXT -> ()
-- integerNotText Refl impossible

-- realNotText : FLOAT = TEXT -> ()
-- realNotText Refl impossible

-- nullableNotText : NULLABLE t = TEXT -> ()
-- nullableNotText Refl impossible

-- realNotInteger : FLOAT = INTEGER -> ()
-- realNotInteger Refl impossible

-- nullableNotInteger : NULLABLE t = INTEGER -> ()
-- nullableNotInteger Refl impossible

-- nullableNotReal : NULLABLE t = FLOAT -> ()
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
