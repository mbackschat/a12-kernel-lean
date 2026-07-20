import A12Kernel.Elaboration.NumericComputation

/-! # Numeric computation-expression outcome locks -/

namespace A12Kernel.Conformance.NumericComputation

open A12Kernel

private def sourceId : FieldId := 0
private def laterId : FieldId := 1

private def numberInfo : NumField := { scale := 0, signed := true }

private def numberDeclaration (id : FieldId) (name : String) :
    FlatFieldDecl where
  id
  groupPath := ["Root"]
  name
  policy := { kind := .number numberInfo }

private def stringDeclaration (id : FieldId) (name : String) :
    FlatFieldDecl where
  id
  groupPath := ["Root"]
  name
  policy := { kind := .string }

private def source : FlatFieldDecl :=
  numberDeclaration sourceId "Source"

private def later : FlatFieldDecl :=
  numberDeclaration laterId "Later"

private def checkedNumber (raw : RawCell) : CheckedCell :=
  formalCheck { kind := .number numberInfo } raw

private def context (source later : CheckedCell := checkedNumber .empty) :
    ScalarComputationContext where
  read field :=
    if field == sourceId then source
    else if field == laterId then later
    else checkedNumber .empty

private def literal (value : Rat) (authoredScale : Int := 0) :
    AuthoredNumericExpr FlatFieldDecl :=
  .literal { value, authoredScale }

private def field (declaration : FlatFieldDecl) :
    AuthoredNumericExpr FlatFieldDecl :=
  .atom declaration

private def divide (left right : AuthoredNumericExpr FlatFieldDecl) :
    AuthoredNumericExpr FlatFieldDecl :=
  .binary .divide left right

private def binary (op : NumericScaleBinaryOp)
    (left right : AuthoredNumericExpr FlatFieldDecl) :
    AuthoredNumericExpr FlatFieldDecl :=
  .binary op left right

private def rounded (body : AuthoredNumericExpr FlatFieldDecl) :
    AuthoredNumericExpr FlatFieldDecl :=
  .round .halfUp omittedRoundingPlaces body

private def power (base exponent : AuthoredNumericExpr FlatFieldDecl) :
    AuthoredNumericExpr FlatFieldDecl :=
  .power base exponent

private def resultOf (expression : AuthoredNumericExpr FlatFieldDecl)
    (input : ScalarComputationContext := context) :
    Option NumericComputationResult :=
  (expression.evaluateComputation input).toOption

private def faultOf (expression : AuthoredNumericExpr FlatFieldDecl)
    (input : ScalarComputationContext := context) :
    Option NumericComputationFault :=
  match expression.evaluateComputation input with
  | .ok _ => none
  | .error fault => some fault

/- Empty Number is a real computation value, not clean no-selection. -/
example : resultOf (field source) = some (.value 0) := by
  rfl

example : resultOf (binary .add (field source) (literal 2)) =
    some (.value 2) := by
  native_decide

example : resultOf (field source)
    (context ((checkedNumber .empty).withFinding .required)) =
      some (.value 0) := by
  rfl

example : resultOf (divide (literal 6) (literal 3)) = some (.value 2) := by
  native_decide

/- The computation consumer uses the established one-pass lowering rather than folding the authored tree directly. -/
example : resultOf
    (binary .multiply (literal 3)
      (.group (divide (literal 1) (literal 3)))) =
      some (.value 1) := by
  native_decide

/- Arithmetic domain failure survives as its own expression outcome. -/
example : resultOf (divide (literal 1) (literal 0)) = some .domainFailure := by
  native_decide

/- Rounding does not turn a failed arithmetic child into a numeric value. -/
example : resultOf (rounded (divide (literal 1) (literal 0))) =
    some .domainFailure := by
  native_decide

/- Rounding preserves a reached computation poison instead of manufacturing a numeric result. -/
example : resultOf (rounded (field source))
    (context (checkedNumber (.rejected .malformed))) =
      some (.poison .malformed) := by
  rfl

example : resultOf
    (binary .add (divide (literal 1) (literal 0)) (literal 2)) =
      some .domainFailure := by
  native_decide

example : resultOf
    (binary .add (literal 2) (divide (literal 1) (literal 0))) =
      some .domainFailure := by
  native_decide

/- A formally invalid field actually read by the expression remains poison. -/
example : resultOf (field source)
    (context (checkedNumber (.rejected .malformed))) =
      some (.poison .malformed) := by
  rfl

/- The source-generated arithmetic chain still evaluates its right operand after a domain-invalid receiver; a reached invalid field therefore remains poison. Portable mixed-precedence evidence remains pending. -/
example : resultOf
    (binary .add
      (divide (literal 1) (literal 0))
      (field later))
    (context (checkedNumber .empty)
      (checkedNumber (.rejected .declaredConstraint))) =
      some (.poison .declaredConstraint) := by
  rfl

/- A left poison aborts before a differently poisoned right operand can replace its cause. -/
example : resultOf
    (binary .add
      (field source)
      (field later))
    (context
      (checkedNumber (.rejected .malformed))
      (checkedNumber (.rejected .declaredConstraint))) =
      some (.poison .malformed) := by
  rfl

/- Poison order follows the one-pass lowered tree: `(Source / 2) * Later` becomes `(Later * Source) / 2`, so Later is read first. -/
example : resultOf
    (binary .multiply
      (divide (field source) (literal 2))
      (field later))
    (context
      (checkedNumber (.rejected .malformed))
      (checkedNumber (.rejected .declaredConstraint))) =
      some (.poison .declaredConstraint) := by
  rfl

/- A non-Number declaration is a structural fault even when its cell is empty. -/
example : faultOf (field (stringDeclaration sourceId "WrongSource")) =
      some (.fieldKindMismatch sourceId) := by
  native_decide

/- Complete structural checking prevents a left poison from hiding a wrong-kind right declaration. -/
example : faultOf
    (binary .add
      (field source)
      (field (stringDeclaration laterId "WrongLater")))
    (context (checkedNumber (.rejected .malformed))) =
      some (.fieldKindMismatch laterId) := by
  native_decide

/- Power's computation projection remains unaudited and fails closed at this boundary. -/
example : faultOf (power (literal 2) (literal 3)) =
    some .unsupportedPower := by
  native_decide

/- Unsupported structure is rejected before a reached poison can hide it. -/
example : faultOf
    (binary .add (field source) (power (literal 2) (literal 3)))
    (context (checkedNumber (.rejected .malformed))) =
      some .unsupportedPower := by
  native_decide

end A12Kernel.Conformance.NumericComputation
