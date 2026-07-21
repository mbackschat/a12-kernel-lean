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

private def targetId : FieldId := 2
private def wrongId : FieldId := 3
private def repeatedId : FieldId := 4

private def wrong : FlatFieldDecl :=
  stringDeclaration wrongId "Wrong"

private def repeated : FlatFieldDecl :=
  { id := repeatedId
    groupPath := ["Root", "Rows"]
    name := "Repeated"
    policy := { kind := .number numberInfo }
    repeatableScope := [10] }

private def model : FlatModel :=
  { fields := [source, later, numberDeclaration targetId "Target", wrong, repeated]
    repeatableGroups := [{ level := 10, path := ["Root", "Rows"] }] }

private def surfacePath (groups : List String) (name : String) :
    SurfaceFieldPath :=
  { base := .absolute, groups, field := name }

private def surfaceField (groups : List String) (name : String) :
    AuthoredNumericExpr SurfaceFieldPath :=
  .atom (surfacePath groups name)

private def checkedErrorOf (expression : AuthoredNumericExpr SurfaceFieldPath)
    (target : FieldId := targetId) :
    Option NumericComputationElabError :=
  match elaborateNumericComputationOperation model ["Root"] target expression with
  | .ok _ => none
  | .error error => some error

private def checkedNumber (raw : RawCell) : CheckedCell :=
  formalCheck { kind := .number numberInfo } raw

private def context (source later : CheckedCell := checkedNumber .empty) :
    ScalarComputationContext where
  read field :=
    if field == sourceId then source
    else if field == laterId then later
    else checkedNumber .empty

private def checkedResultOf
    (expression : AuthoredNumericExpr SurfaceFieldPath)
    (input : ScalarComputationContext := context) :
    Option NumericComputationResult :=
  match elaborateNumericComputationOperation model ["Root"] targetId expression with
  | .error _ => none
  | .ok checked => checked.evaluate input |>.toOption

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

private def absolute (body : AuthoredNumericExpr FlatFieldDecl) :
    AuthoredNumericExpr FlatFieldDecl :=
  .abs body

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

/- Checked computation-operation authoring resolves the shared numeric tree and rejects a nested direct reference to its own target. -/
example :
    checkedErrorOf
      (.binary .add (surfaceField ["Root"] "Source")
        (.group (.binary .multiply
          (surfaceField ["Root"] "Target")
          (.literal { value := 2, authoredScale := 0 })))) =
      some (.targetSelfReference targetId) := by
  native_decide

/- A checked operation reuses the existing numeric evaluator; unlike a validation comparison, a constant-only computation is legal. -/
example :
    checkedResultOf
        (.binary .add (surfaceField ["Root"] "Source")
          (.literal { value := 2, authoredScale := 0 }))
        (context (checkedNumber (.parsed (.num 3)))) = some (.value 5) ∧
      checkedResultOf (.literal { value := 7, authoredScale := 0 }) =
        some (.value 7) := by
  native_decide

example :
    checkedErrorOf (surfaceField ["Root"] "Wrong") =
        some (.operandNotNumber wrong.path) ∧
      checkedErrorOf (surfaceField ["Root", "Rows"] "Repeated") =
        some (.resolve (.repeatableReference repeated.path)) ∧
      checkedErrorOf (.literal { value := 1, authoredScale := 0 }) wrongId =
        some (.targetNotNumber wrongId) := by
  native_decide

/- Authoring and result-scale checks precede runtime evaluation and retain their distinct rejection classes. -/
example :
    let twoDivisions :=
      AuthoredNumericExpr.binary .multiply
        (.binary .divide (surfaceField ["Root"] "Source")
          (.literal { value := 2, authoredScale := 0 }))
        (.binary .divide (.literal { value := 3, authoredScale := 0 })
          (.literal { value := 4, authoredScale := 0 }))
    checkedErrorOf twoDivisions = some (.authoring .tooManyDivisions) ∧
      checkedErrorOf (.literal { value := 1, authoredScale := 1 }) =
        some (.operationScaleMismatch 0 (NumericScaleSummary.constant 1)) := by
  native_decide

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

/- Absolute value shares the numeric tree but preserves computation-domain failure and poison. -/
example : resultOf (absolute (field source))
    (context (checkedNumber (.parsed (.num (-5))))) = some (.value 5) := by
  native_decide

example : resultOf (absolute (divide (literal 1) (literal 0))) =
    some .domainFailure := by
  native_decide

example : resultOf (absolute (field source))
    (context (checkedNumber (.rejected .malformed))) =
      some (.poison .malformed) := by
  rfl

/- Numeric operand-list extrema keep empty Number as a competing zero. -/
example : resultOf (AuthoredNumericExpr.extremumList .minimum (field source) [literal 4]) =
    some (.value 0) := by
  native_decide

example : resultOf (AuthoredNumericExpr.extremumList .maximum (field source) [literal (-4)]) =
    some (.value 0) := by
  native_decide

/- A domain failure remains value-level and therefore does not hide a later reached poison. -/
example : resultOf
    (AuthoredNumericExpr.extremumList .maximum
      (divide (literal 1) (literal 0)) [literal 3]) =
      some .domainFailure := by
  native_decide

example : resultOf
    (AuthoredNumericExpr.extremumList .minimum
      (divide (literal 1) (literal 0)) [literal 3, field later])
    (context (checkedNumber .empty)
      (checkedNumber (.rejected .declaredConstraint))) =
      some (.poison .declaredConstraint) := by
  native_decide

/- The first poison aborts the remaining ordered operand stream. -/
example : resultOf
    (AuthoredNumericExpr.extremumList .maximum (field source) [field later])
    (context
      (checkedNumber (.rejected .malformed))
      (checkedNumber (.rejected .declaredConstraint))) =
      some (.poison .malformed) := by
  native_decide

/- Structural preflight traverses the complete list before a reached poison could hide a wrong-kind tail. -/
example : faultOf
    (AuthoredNumericExpr.extremumList .minimum (field source)
      [literal 3, field (stringDeclaration laterId "WrongLater")])
    (context (checkedNumber (.rejected .malformed))) =
      some (.fieldKindMismatch laterId) := by
  native_decide

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

/- Power shares the checked computation result boundary: valid values remain values. -/
example : resultOf (power (literal 2) (literal 3)) =
    some (.value 8) := by
  native_decide

/- Both runtime-invalid integral power regions become arithmetic domain failure. -/
example : resultOf (power (literal 0) (literal (-1))) =
    some .domainFailure := by
  native_decide

example : resultOf (power (literal 2) (literal 1001)) =
    some .domainFailure := by
  native_decide

/- Structural preflight still traverses power before a reached poison can hide a wrong-kind exponent. -/
example : faultOf
    (binary .add (field source)
      (power (literal 2) (field (stringDeclaration laterId "WrongLater"))))
    (context (checkedNumber (.rejected .malformed))) =
      some (.fieldKindMismatch laterId) := by
  native_decide

end A12Kernel.Conformance.NumericComputation
