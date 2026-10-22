import A12Kernel.Elaboration.ValidationRule

/-!
# Checked nonrepeatable partial-validation rule locks

This family remains independently buildable with `lake build A12Kernel.Conformance.ValidationRule.Partial`; the validation-rule conformance module is only its import umbrella.
-/

namespace A12Kernel.Conformance.ValidationRule.Partial

open A12Kernel

private def errorField (isGlobal : Bool) : FlatFieldDecl :=
  { id := 200
    groupPath := ["Order"]
    name := "Amount"
    policy := { kind := .number { scale := 0, signed := true } }
    isGlobal }

private def otherField : FlatFieldDecl :=
  { id := 201
    groupPath := ["Order"]
    name := "Confirmed"
    policy := { kind := .boolean } }

private def model (isGlobal : Bool) : FlatModel :=
  { fields := [errorField isGlobal, otherField] }

private def path (field : String) : SurfaceFieldPath :=
  { base := .absolute, groups := ["Order"], field }

private def errorFilled : SurfaceCondition :=
  .fieldFilled (path "Amount")

private def otherFilled : SurfaceCondition :=
  .fieldFilled (path "Confirmed")

private def bothFilled : SurfaceCondition :=
  .and errorFilled otherFilled

private def eitherFilled : SurfaceCondition :=
  .or errorFilled otherFilled

private def emptyAmountIsZero : SurfaceCondition :=
  .compare .equal (path "Amount") (.number 0)

private def world : World :=
  { now := { epochMillis := 0 } }

private def rawBothFilled : RawFlatContext where
  read id :=
    if id == (errorField false).id then .parsed (.num 1)
    else if id == otherField.id then .parsed (.bool true)
    else .empty

private def rawEmpty : RawFlatContext where
  read _ := .empty

private def checkedRule? (isGlobal : Bool) (condition : SurfaceCondition) :
    Option (CheckedResolvedValidationRule (model isGlobal)) := do
  let flat ← (elaborate (model isGlobal) ["Order"] condition).toOption
  let checked ← (CheckedValidationCondition.fromFlat flat).toOption
  (assembleResolvedValidationRule (model isGlobal) checked
    (errorField isGlobal).id "partial" .error { parts := [] }).toOption

private def partialVerdict? (isGlobal : Bool)
    (condition : SurfaceCondition) (raw : RawFlatContext)
    (scope : ValidationRelevanceScope) : Option (Option Verdict) := do
  let prepared ←
    (prepareFlatStringContext world builtinStringPatternCompiler
      (model isGlobal)).toOption
  let rule ← checkedRule? isGlobal condition
  match rule.evalPartial prepared "en_US" raw
      GroupPresenceContext.unavailable scope with
  | .error _ => none
  | .ok .skipped => some none
  | .ok (.evaluated outcome) => some (some outcome.verdict)

private def fullVerdict? (isGlobal : Bool)
    (condition : SurfaceCondition) (raw : RawFlatContext)
    (hasContent : Bool) : Option Verdict := do
  let prepared ←
    (prepareFlatStringContext world builtinStringPatternCompiler
      (model isGlobal)).toOption
  let rule ← checkedRule? isGlobal condition
  let outcome ←
    (rule.evalFull prepared "en_US" raw GroupPresenceContext.unavailable
      hasContent).toOption
  pure outcome.verdict

private def onlyOther : ValidationRelevanceScope :=
  .partialSet [{
    path := otherField.path
    indices := [.all, .all]
  }]

private def nothing : ValidationRelevanceScope :=
  .partialSet []

private def lineValue : FlatFieldDecl :=
  { id := 202
    groupPath := ["Order", "Lines"]
    name := "Value"
    policy := { kind := .string }
    repeatableScope := [10] }

private def lines : RepeatableGroupDecl :=
  { level := 10, path := ["Order", "Lines"], repeatability := some 2 }

private def capacityModel : FlatModel :=
  { fields := [errorField false, lineValue], repeatableGroups := [lines] }

private def capacityRule? (operator : GroupFillQuantifier) :
    Option (CheckedResolvedValidationRule capacityModel) := do
  let guard ←
    (elaborate capacityModel ["Order"] errorFilled).toOption
  let checkedGuard ← (CheckedValidationCondition.fromFlat guard).toOption
  let checkedQuantifier ←
    (CheckedValidationCondition.fromGroupList capacityModel ["Order"] operator [
      .starredGroup {
        base := .absolute
        groups := [
          { name := "Order" },
          { name := "Lines", starred := true }
        ]
      }
    ]).toOption
  let condition ← (checkedGuard.and checkedQuantifier).toOption
  (assembleResolvedValidationRule capacityModel condition
    (errorField false).id "capacity" .error { parts := [] }).toOption

private def capacityDocument : DocumentData :=
  { instantiatedRows := [
      { group := 10, path := [1] },
      { group := 10, path := [2] },
      { group := 10, path := [3] }
    ]
    cells := [{
      address := { field := (errorField false).id, path := [] }
      stored := "1"
      raw := .parsed (.num 1)
    }] }

private def capacityScope (row : Option Nat) : ValidationRelevanceScope :=
  .partialSet ([{
    path := (errorField false).path
    indices := [.all, .all]
  }] ++ row.toList.map fun coordinate => {
    path := lines.path
    indices := [.all, .concrete coordinate]
  })

private def addressedCapacityVerdict? (operator : GroupFillQuantifier)
    (row : Option Nat) : Option Verdict := do
  let rule ← capacityRule? operator
  let prepared ←
    (prepareFlatStringContext world builtinStringPatternCompiler
      capacityModel).toOption
  let checked ← (checkDocument prepared "en_US" capacityDocument).toOption
  let .evaluated outcome ←
    (rule.evalAddressedPartial checked (capacityScope row)).toOption
    | none
  some outcome.verdict

/- A global error field is auto-relevant before the rule gate; the same non-global rule remains skipped. -/
example :
    partialVerdict? true bothFilled rawBothFilled onlyOther =
      some (some (.fired .value)) ∧
    partialVerdict? false bothFilled rawBothFilled onlyOther =
      some none := by
  native_decide

/- Once the global error field admits the rule, an omitted peer remains leaf UNKNOWN: `And` suppresses while the independently true `Or` still fires. -/
example :
    partialVerdict? true bothFilled rawBothFilled nothing =
      some (some .unknown) ∧
    partialVerdict? true eitherFilled rawBothFilled nothing =
      some (some (.fired .value)) := by
  native_decide

/- Partial relevance bypasses the full-validation content gate, so a relevant empty scalar instance can fire through Number-as-zero. Repeatable phantom-row construction is a separate SG2 boundary. -/
example :
    partialVerdict? true emptyAmountIsZero rawEmpty nothing =
      some (some (.fired .omission)) ∧
    fullVerdict? true emptyAmountIsZero rawEmpty false =
      some .notFired := by
  native_decide

/- The complete checked-rule API preserves the measured one-level partial capacity boundary. An
   in-capacity group row enters the threshold extent; an over-limit-only or absent selection remains
   semantic UNKNOWN rather than becoming an empty operand. -/
example :
    addressedCapacityVerdict? .atLeastOneGroupFilled (some 2) =
      some (.fired .value) ∧
    addressedCapacityVerdict? .noGroupFilled (some 2) =
      some .unknown ∧
    addressedCapacityVerdict? .atLeastOneGroupFilled (some 3) =
      some .unknown ∧
    addressedCapacityVerdict? .noGroupFilled (some 3) =
      some .unknown ∧
    addressedCapacityVerdict? .atLeastOneGroupFilled none =
      some .unknown ∧
    addressedCapacityVerdict? .noGroupFilled none =
      some .unknown := by
  native_decide


/-! ## The repetition operand under a caller's coverage

One repeatable group, two rules differing in a single operand, and the coverages the caller declares
([checkpoint](../../../docs/sources/group-and-iteration-probes.md#src-repetition-operand-partial-relevance)).
-/

private def repRows : GroupPath := ["Src", "Rows"]
private def repErr : FlatFieldDecl :=
  { id := 301, groupPath := repRows, name := "Err", policy := { kind := .string },
    repeatableScope := [10] }
private def repBase : FlatFieldDecl :=
  { id := 302, groupPath := repRows, name := "Base",
    policy := { kind := .number { scale := 0, signed := true } }, repeatableScope := [10] }
private def repModel : FlatModel :=
  { fields := [repErr, repBase],
    repeatableGroups := [{ level := 10, path := repRows, repeatability := some 5 }] }
private def repComparison? (left : AuthoredNumericExpr SurfaceNumericAtom) (bound : Rat) :
    Option (CheckedValidationCondition repModel) := do
  let comparison ← (elaborateRepeatableNumericComparison repModel repRows
    { op := .ordinary .greater, left, right := .literal { value := bound, authoredScale := 0 } }).toOption
  (CheckedValidationCondition.fromOrderedNumeric comparison).toOption
/-- `Length(Err) > 0` stands in for the Kernel fixture's `FieldFilled(Err)` guard, conjoined with the
    second operand's `> 1` as there. Both rules carry it identically and it names the error field,
    which the rule assembly requires; because it is the same conjunct in both, any difference below is
    the second operand's. The guard stays a separate conjunct: the Kernel visitor refuses a
    `CurrentRepetition` read anywhere inside one comparison, the nested case by source reading only;
    as its own comparison it is measured unguarded
    ([checkpoint](../../../docs/sources/model-structure-and-declaration-probes.md#src-iteration-guard-k04)
    rows `u17`, `u18`). -/
private def repRule? (second : AuthoredNumericExpr SurfaceNumericAtom) :
    Option (CheckedResolvedValidationRule repModel) := do
  let guard ← repComparison? (.atom (.stringLength { base := .absolute, groups := repRows, field := "Err" })) 0
  let condition ← (guard.and (← repComparison? second 1)).toOption
  (assembleResolvedValidationRule repModel condition repErr.id "R" .error { parts := [] }).toOption
private def repetitionOperand : AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.currentRepetition { base := .absolute, groups := repRows })
private def baseOperand : AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.field { base := .absolute, groups := repRows, field := "Base" })
private def repDocument : DocumentData :=
  { instantiatedRows := [{ group := 10, path := [1] }, { group := 10, path := [2] }]
    cells :=
      [{ address := { field := 301, path := [1] }, stored := "x", raw := .parsed (.str "x") },
       { address := { field := 301, path := [2] }, stored := "x", raw := .parsed (.str "x") },
       { address := { field := 302, path := [1] }, stored := "5", raw := .parsed (.num 5) },
       { address := { field := 302, path := [2] }, stored := "5", raw := .parsed (.num 5) }] }
private def repCoverage (paths : List GroupPath) : ValidationRelevanceScope :=
  .partialSet (paths.map fun path => { path, indices := path.map fun _ => .all })
private def repOutcomes (second : AuthoredNumericExpr SurfaceNumericAtom)
    (scope : ValidationRelevanceScope) : Option (List (Env × PartialRuleOutcome)) := do
  let rule ← repRule? second
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler repModel).toOption
  let checked ← (checkDocument prepared "en_US" repDocument).toOption
  match ← (rule.evalOrdinaryRepeatablePartial checked scope).toOption with
  | .skipped => some []
  | .evaluated rows => some rows
/-- Project one row's partial outcome to `none` for the rule-level relevance skip and `some verdict`
    for every evaluated row. Collapsing a skip onto `notFired` would erase exactly the distinction
    these cases exist to lock. -/
private def repVerdicts (second : AuthoredNumericExpr SurfaceNumericAtom)
    (scope : ValidationRelevanceScope) : Option (List (Option Verdict)) :=
  (repOutcomes second scope).map fun rows => rows.map fun row =>
    match row.2 with
    | .skipped => none
    | .evaluated outcome => some outcome.verdict

/-- **A repetition operand introduces no relevance dependency, so a coverage naming only the error
field leaves it answering exactly as full validation does** — while its field-reading twin, identical
in every other respect, goes UNKNOWN under that same coverage. The twin is what makes these rows a
measurement of the masking layer rather than of a partial validation that ignores coverage. The
error-field gate is separate and stricter, and it is checked per row before any addressed read: a
coverage naming only the *other* field skips both rows even though that rule's own operand reads
nothing at all, and the empty coverage does the same. Every row is the Kernel's
([checkpoint](../../../docs/sources/group-and-iteration-probes.md#src-repetition-operand-partial-relevance)). -/
example :
    let fired := some (Verdict.fired .value)
    repVerdicts repetitionOperand .full = some [some .notFired, fired] ∧
      repVerdicts repetitionOperand (repCoverage [repErr.path]) = some [some .notFired, fired] ∧
      repVerdicts baseOperand .full = some [fired, fired] ∧
      repVerdicts baseOperand (repCoverage [repErr.path]) = some [some .unknown, some .unknown] ∧
      repVerdicts repetitionOperand (repCoverage [repBase.path]) = some [none, none] ∧
      repVerdicts repetitionOperand (repCoverage []) = some [none, none] := by
  native_decide

end A12Kernel.Conformance.ValidationRule.Partial
