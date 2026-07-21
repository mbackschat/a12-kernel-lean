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
    (target : FieldId := targetId)
    (suppressExactScaleWarning : Bool := false) :
    Option NumericComputationElabError :=
  match elaborateNumericComputationOperation model ["Root"] target expression
      suppressExactScaleWarning with
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

private def targetPolicy : NumericTargetPolicy where
  info := numberInfo
  minFractionalDigits := 0
  minLeMax := by decide

private def checkedTargetResultOf
    (expression : AuthoredNumericExpr SurfaceFieldPath)
    (suppressExactScaleWarning : Bool)
    (policy : NumericTargetPolicy := targetPolicy)
    (input : ScalarComputationContext := context) :
    Option NumericTargetCheckResult :=
  match elaborateNumericComputationOperation model ["Root"] targetId expression
      suppressExactScaleWarning with
  | .error _ => none
  | .ok checked =>
      match checked.attachTargetPolicy policy with
      | .error _ => none
      | .ok targetChecked => targetChecked.evaluate input |>.toOption

private def targetPolicyAttachErrorOf (policy : NumericTargetPolicy) :
    Option NumericComputationElabError :=
  match elaborateNumericComputationOperation model ["Root"] targetId
      (.literal { value := 0, authoredScale := 0 }) with
  | .error error => some error
  | .ok checked =>
      match checked.attachTargetPolicy policy with
      | .error error => some error
      | .ok _ => none

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
        some (.targetSelfReference targetId) ∧
      checkedErrorOf (.abs (surfaceField ["Root"] "Target")) =
        some (.targetSelfReference targetId) := by
  native_decide

/- Target policy is attached once: a different scale/signedness summary is rejected before evaluation. -/
example :
    let wrongPolicy : NumericTargetPolicy :=
      { info := { scale := 1, signed := true }
        minFractionalDigits := 0
        minLeMax := by decide }
    targetPolicyAttachErrorOf wrongPolicy =
      some (.targetPolicyMismatch numberInfo wrongPolicy.info) := by
  native_decide

/- Evaluation consumes the retained complete policy rather than accepting a new caller-selected one. -/
example :
    let zeroForbidden := { targetPolicy with zeroAllowed := false }
    checkedTargetResultOf (.literal { value := 0, authoredScale := 0 })
      false zeroForbidden =
        some (.supported (.rejected
          { unscaled := 0, scale := 0 } .zeroNotAllowed)) := by
  native_decide

/- The one legal warning suppression bypasses only the result-scale gate and selects the no-fit target branch carried by the checked operation. -/
example :
    let scaleOne :=
      AuthoredNumericExpr.literal
        (Atom := SurfaceFieldPath) { value := 11 / 10, authoredScale := 1 }
    checkedErrorOf scaleOne =
        some (.operationScaleMismatch 0 (NumericScaleSummary.constant 1)) ∧
      checkedErrorOf scaleOne (suppressExactScaleWarning := true) = none ∧
      checkedTargetResultOf scaleOne true =
        some (.supported (.rejected
          { unscaled := 11, scale := 1 } .suppressedScaleMismatch)) := by
  native_decide

/- Suppression does not bypass the independent plain-authoring rejection. -/
example :
    let twoDivisions :=
      AuthoredNumericExpr.binary .multiply
        (.binary .divide (surfaceField ["Root"] "Source")
          (.literal { value := 2, authoredScale := 0 }))
        (.binary .divide (.literal { value := 3, authoredScale := 0 })
          (.literal { value := 4, authoredScale := 0 }))
    checkedErrorOf twoDivisions (suppressExactScaleWarning := true) =
      some (.authoring .tooManyDivisions) := by
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

/- The checked boundary admits the source-closed direct root value functions already shared with numeric validation. -/
example :
    let sourceField := surfaceField ["Root"] "Source"
    let input := context (checkedNumber (.parsed (.num (5 / 2))))
    checkedResultOf (.round .halfUp omittedRoundingPlaces sourceField) input =
        some (.value 3) ∧
      checkedResultOf (.abs sourceField)
        (context (checkedNumber (.parsed (.num (-5))))) = some (.value 5) ∧
      checkedResultOf
        (AuthoredNumericExpr.extremumList .maximum sourceField
          [.literal { value := 4, authoredScale := 0 }]) input =
        some (.value 4) := by
  native_decide

/- The narrow checked function fragment still rejects a second Min/Max constant and a wrapper around arithmetic; their wider source traversal remains unclosed. -/
example :
    let sourceField := surfaceField ["Root"] "Source"
    checkedErrorOf
        (AuthoredNumericExpr.extremumList .minimum sourceField
          [.literal { value := 1, authoredScale := 0 },
            .literal { value := 2, authoredScale := 0 }]) =
          some .unsupportedExpression ∧
      checkedErrorOf
        (.round .halfUp omittedRoundingPlaces
          (.binary .add sourceField
            (.literal { value := 1, authoredScale := 0 }))) =
          some .unsupportedExpression := by
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
