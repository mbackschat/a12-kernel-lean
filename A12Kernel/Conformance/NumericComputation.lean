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
private def timeId : FieldId := 5
private def dateTimeId : FieldId := 6
private def dateId : FieldId := 7

private def timeComponents : TemporalComponents :=
  { year := false, month := false, day := false,
    hour := true, minute := true, second := true }

private def dateTimeComponents : TemporalComponents :=
  { TemporalComponents.fullDate with
    hour := true, minute := true, second := true }

private def temporalDeclaration (id : FieldId) (name : String)
    (kind : TemporalKind) (components : TemporalComponents) : FlatFieldDecl where
  id
  groupPath := ["Root"]
  name
  policy := { kind := .temporal kind components }

private def wrong : FlatFieldDecl :=
  stringDeclaration wrongId "Wrong"

private def repeated : FlatFieldDecl :=
  { id := repeatedId
    groupPath := ["Root", "Rows"]
    name := "Repeated"
    policy := { kind := .number numberInfo }
    repeatableScope := [10] }

private def model : FlatModel :=
  { fields := [source, later, numberDeclaration targetId "Target", wrong, repeated,
      temporalDeclaration timeId "Time" .time timeComponents,
      temporalDeclaration dateTimeId "DateTime" .dateTime dateTimeComponents,
      temporalDeclaration dateId "Date" .date TemporalComponents.fullDate]
    repeatableGroups := [{ level := 10, path := ["Root", "Rows"] }]
    baseYear := some 2020 }

private def noBaseYearModel : FlatModel := { model with baseYear := none }

private def surfacePath (groups : List String) (name : String) :
    SurfaceFieldPath :=
  { base := .absolute, groups, field := name }

private def surfaceField (groups : List String) (name : String) :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.field (surfacePath groups name))

private def surfaceAggregate (op : NumericAggregateOp) (first : String)
    (rest : List String) : AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.aggregate op {
    first := surfacePath ["Root"] first
    rest := rest.map (surfacePath ["Root"]) })

private def surfaceBaseYear : AuthoredNumericExpr SurfaceNumericAtom :=
  .atom .baseYear

private def surfaceBaseYearDatePart (source : BaseYearDateSource)
    (part : DateNumericPart) : AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.baseYearDatePart source part)

private def surfaceDateFieldPart (name : String) (part : DateNumericPart) :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.temporalFieldPart (surfacePath ["Root"] name) (.date part))

private def surfaceTimeFieldPart (name : String) (part : TimeNumericPart) :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.temporalFieldPart (surfacePath ["Root"] name) (.time part))

private def surfaceDateDifference (unit : DateDifferenceUnit)
    (left right : SurfaceDateDifferenceOperand) :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.dateDifference unit left right)

private def surfaceDateOperand (name : String) : SurfaceDateDifferenceOperand :=
  .field (surfacePath ["Root"] name)

private def checkedErrorOf (expression : AuthoredNumericExpr SurfaceNumericAtom)
    (target : FieldId := targetId)
    (suppressExactScaleWarning : Bool := false) :
    Option NumericComputationElabError :=
  match elaborateNumericComputationOperation model ["Root"] target expression
      suppressExactScaleWarning with
  | .ok _ => none
  | .error error => some error

private def noBaseYearErrorOf (expression : AuthoredNumericExpr SurfaceNumericAtom) :
    Option NumericComputationElabError :=
  match elaborateNumericComputationOperation noBaseYearModel ["Root"] targetId
      expression with
  | .ok _ => none
  | .error error => some error

private def checkedNumber (raw : RawCell) : CheckedCell :=
  formalCheck { kind := .number numberInfo } raw

private def checkedTemporal (kind : TemporalKind) (components : TemporalComponents)
    (raw : RawCell) : CheckedCell :=
  formalCheck { kind := .temporal kind components } raw

private def context (source later : CheckedCell := checkedNumber .empty)
    (time : CheckedCell := checkedTemporal .time timeComponents .empty)
    (dateTime : CheckedCell :=
      checkedTemporal .dateTime dateTimeComponents .empty)
    (date : CheckedCell :=
      checkedTemporal .date TemporalComponents.fullDate .empty) :
    ScalarComputationContext where
  read field :=
    if field == sourceId then source
    else if field == laterId then later
    else if field == timeId then time
    else if field == dateTimeId then dateTime
    else if field == dateId then date
    else checkedNumber .empty

private def instant : Instant := { epochMillis := 1719292867000 }

private def dateParts : DateParts := { year := 2024, month := 6, day := 25 }

private def clock : TimeOfDay :=
  (TimeOfDay.ofHms? 5 21 7).get (by native_decide)

private def dateTimeValue : Value :=
  .temporal (.dateTime instant dateParts clock .storedGregorian)

private def dateValue (year : Int) (month day : Nat)
    (basis : DateCalendarBasis := .storedGregorian) : Value :=
  .temporal (.date instant { year, month, day } basis)

private def checkedResultOf
    (expression : AuthoredNumericExpr SurfaceNumericAtom)
    (input : ScalarComputationContext := context) :
    Option NumericComputationResult :=
  match elaborateNumericComputationOperation model ["Root"] targetId expression with
  | .error _ => none
  | .ok checked => checked.evaluate input |>.toOption

private def checkedFaultOf
    (expression : AuthoredNumericExpr SurfaceNumericAtom)
    (input : ScalarComputationContext := context) : Option NumericComputationFault :=
  match elaborateNumericComputationOperation model ["Root"] targetId expression with
  | .error _ => none
  | .ok checked =>
      match checked.evaluate input with
      | .ok _ => none
      | .error fault => some fault

private def targetPolicy : NumericTargetPolicy where
  info := numberInfo
  minFractionalDigits := 0
  minLeMax := by decide

private def checkedTargetResultOf
    (expression : AuthoredNumericExpr SurfaceNumericAtom)
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
        (Atom := SurfaceNumericAtom) { value := 11 / 10, authoredScale := 1 }
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

example :
    noBaseYearErrorOf surfaceBaseYear = some .baseYearNotDeclared ∧
    checkedResultOf surfaceBaseYear = some (.value 2020) ∧
    checkedResultOf (.binary .add surfaceBaseYear
      (surfaceField ["Root"] "Source"))
      (context (checkedNumber (.parsed (.num 1)))) = some (.value 2021) ∧
    checkedErrorOf (.binary .add surfaceBaseYear
      (.literal { value := 0, authoredScale := 2 })) =
        some (.operationScaleMismatch 0
          ((NumericScaleSummary.field 0).union
            (NumericScaleSummary.constant 2))) := by
  native_decide

example :
    let directYear := surfaceBaseYearDatePart .direct .year
    let finishDay := surfaceBaseYearDatePart (.range .finish) .day
    let finishQuarter := surfaceBaseYearDatePart (.range .finish) .quarter
    noBaseYearErrorOf finishDay = some .baseYearNotDeclared ∧
      checkedResultOf directYear = some (.value 2020) ∧
      checkedResultOf finishDay = some (.value 31) ∧
      checkedResultOf finishQuarter = some (.value 4) ∧
      checkedResultOf (.binary .add finishDay
        (surfaceField ["Root"] "Source"))
        (context (checkedNumber (.parsed (.num 1)))) = some (.value 32) ∧
      checkedErrorOf (.abs finishDay) = some .unsupportedExpression := by
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

/- Checked computation shares the temporal component source seam: DateTime supplies either half, empty contributes zero, and formal invalidity stays poison. -/
example :
    checkedResultOf (surfaceDateFieldPart "DateTime" .day)
        (context (dateTime := checkedTemporal .dateTime dateTimeComponents
          (.parsed dateTimeValue))) = some (.value 25) ∧
      checkedResultOf (surfaceTimeFieldPart "DateTime" .second)
        (context (dateTime := checkedTemporal .dateTime dateTimeComponents
          (.parsed dateTimeValue))) = some (.value 7) ∧
      checkedResultOf (surfaceTimeFieldPart "Time" .hour) = some (.value 0) ∧
      checkedResultOf (surfaceDateFieldPart "DateTime" .year)
        (context (dateTime := checkedTemporal .dateTime dateTimeComponents
          (.rejected .malformed))) = some (.poison .malformed) := by
  native_decide

/- Checked computation consumes the same mixed date-difference source: filled fields produce scale-0 values, empty is zero, and formal invalidity remains poison. -/
example :
    let mixedMonths := surfaceDateDifference .months
      (.baseYear .direct) (surfaceDateOperand "Date")
    checkedResultOf mixedMonths (context
        (date := checkedTemporal .date TemporalComponents.fullDate
          (.parsed (dateValue 2020 2 29)))) = some (.value 1) ∧
      checkedResultOf mixedMonths = some (.value 0) ∧
      checkedResultOf mixedMonths
        (context (date := checkedTemporal .date TemporalComponents.fullDate
          (.rejected .malformed))) = some (.poison .malformed) := by
  native_decide

/- Month/year differences reject DateTime statically and a legacy-hybrid field payload dynamically instead of applying the proleptic decoded-parts core. -/
example :
    checkedErrorOf (surfaceDateDifference .years
      (surfaceDateOperand "DateTime") (.baseYear .direct)) =
        some (.incompatibleTemporalSource ["Root", "DateTime"]) ∧
      checkedFaultOf
        (surfaceDateDifference .months
          (.baseYear .direct) (surfaceDateOperand "Date"))
        (context (date := checkedTemporal .date TemporalComponents.fullDate
          (.parsed (dateValue 2020 2 29 .legacyHybrid)))) =
          some .unsupportedDateCalendar := by
  native_decide

/- Checked source admission rejects the wrong temporal family and unaudited value-function wrapping. -/
example :
    checkedErrorOf (surfaceDateFieldPart "Time" .day) =
        some (.incompatibleTemporalSource ["Root", "Time"]) ∧
      checkedErrorOf (.abs (surfaceDateFieldPart "DateTime" .day)) =
        some .unsupportedExpression := by
  native_decide

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

/- Computation consumes the same resolved aggregate source and fold: empties are skipped, all-empty is zero, and reached formal invalidity poisons. -/
example :
    checkedResultOf (surfaceAggregate .sum "Source" ["Later"])
        (context (checkedNumber (.parsed (.num 4)))
          (checkedNumber (.parsed (.num 6)))) = some (.value 10) ∧
      checkedResultOf (surfaceAggregate .sum "Source" ["Later"]) =
        some (.value 0) ∧
      checkedResultOf (surfaceAggregate .minimum "Source" ["Later"])
        (context (checkedNumber (.parsed (.num 20)))) = some (.value 20) ∧
      checkedResultOf (surfaceAggregate .maximum "Source" ["Later"])
        (context (checkedNumber (.parsed (.num 20)))
          (checkedNumber (.rejected .declaredConstraint))) =
        some (.poison .declaredConstraint) := by
  native_decide

/- Aggregate atoms compose through plain arithmetic and the kernel-established direct rounding route while retaining their derived scale. -/
example :
    checkedResultOf
      (.binary .add (surfaceAggregate .sum "Source" ["Later"])
        (.literal { value := 1, authoredScale := 0 }))
      (context (checkedNumber (.parsed (.num 4)))
        (checkedNumber (.parsed (.num 6)))) = some (.value 11) ∧
      checkedResultOf
        (.round .halfUp omittedRoundingPlaces
          (surfaceAggregate .sum "Source" ["Later"]))
        (context (checkedNumber (.parsed (.num 4)))
          (checkedNumber (.parsed (.num 6)))) = some (.value 10) := by
  native_decide

/- Direct aggregate rounding does not widen every scalar-only value-function shape to aggregate operands. -/
example :
    let aggregate := surfaceAggregate .sum "Source" ["Later"]
    checkedErrorOf (.abs aggregate) = some .unsupportedExpression ∧
      checkedErrorOf
        (AuthoredNumericExpr.extremumList .minimum aggregate
          [surfaceField ["Root"] "Source"]) = some .unsupportedExpression := by
  native_decide

/- Shared aggregate lowering preserves its diagnostic owner and computation's nested target-reference rejection. -/
example :
    checkedErrorOf (surfaceAggregate .sum "Source" ["Wrong"]) =
        some (.aggregate (.fieldKindMismatch ["Root", "Wrong"] .string)) ∧
      checkedErrorOf (surfaceAggregate .sum "Source" ["Target"]) =
        some (.targetSelfReference targetId) := by
  native_decide

end A12Kernel.Conformance.NumericComputation
