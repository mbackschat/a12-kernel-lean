import A12Kernel.Elaboration.GeneratedComputationValidation

/-! # Boolean/Confirm value-count computation locks -/

namespace A12Kernel.Conformance.NumericComputation.BooleanValueCount

open A12Kernel

private def target : FlatFieldDecl :=
  { id := 1
    groupPath := ["Flags"]
    name := "Count"
    policy := { kind := .number { scale := 0, signed := false } } }

private def firstBoolean : FlatFieldDecl :=
  { id := 2
    groupPath := ["Flags"]
    name := "A"
    policy := { kind := .boolean } }

private def secondBoolean : FlatFieldDecl :=
  { id := 3
    groupPath := ["Flags"]
    name := "B"
    policy := { kind := .boolean } }

private def confirmation : FlatFieldDecl :=
  { id := 4
    groupPath := ["Flags"]
    name := "Confirmed"
    policy := { kind := .confirm } }

private def model : FlatModel :=
  { fields := [target, firstBoolean, secondBoolean, confirmation] }

private def outerGate : FlatFieldDecl :=
  { id := 5
    groupPath := ["Flags"]
    name := "Gate"
    policy := { kind := .number { scale := 0, signed := false } } }

private def repeatedGate : FlatFieldDecl :=
  { id := 6
    groupPath := ["Flags", "Rows"]
    name := "Gate"
    policy := { kind := .number { scale := 0, signed := false } }
    repeatableScope := [10] }

private def repeatedBoolean : FlatFieldDecl :=
  { id := 7
    groupPath := ["Flags", "Rows"]
    name := "Selected"
    policy := { kind := .boolean }
    repeatableScope := [10] }

private def repeatableModel : FlatModel :=
  { fields := [target, outerGate, repeatedGate, repeatedBoolean]
    repeatableGroups := [{
      level := 10
      path := ["Flags", "Rows"] }] }

private def path (name : String) : SurfaceFieldPath :=
  { base := .absolute, groups := ["Flags"], field := name }

private def repeatedPath (name : String) : SurfaceFieldPath :=
  { base := .absolute, groups := ["Flags", "Rows"], field := name }

private def repeatedStar (name : String) : SurfaceStarFieldPath :=
  { base := .absolute
    groups := [
      { name := "Flags" },
      { name := "Rows", starred := true }]
    field := name }

private def repeatableHaving : SurfaceCorrelatedHaving :=
  .compareNumbers .equal
    { origin := .inner, field := repeatedPath "Gate" }
    { origin := .outer, field := path "Gate" }

private def source (first second : String) :
    SurfaceBooleanValueCountSource :=
  { first := .field (path first)
    rest := [.field (path second)] }

private def repeatableSource : SurfaceBooleanValueCountSource :=
  { first := .starHaving (repeatedStar "Selected") repeatableHaving
    rest := [] }

private def surface (expected : Bool)
    (authored : SurfaceBooleanValueCountSource) :
    AuthoredNumericExpr SurfaceNumericComputationAtom :=
  .atom (.booleanValueCount expected authored)

private def operation (expected : Bool)
    (authored : SurfaceBooleanValueCountSource) :=
  elaborateCompleteNumericComputationOperation model ["Flags"] target.id
    (surface expected authored)

private def operationError (expected : Bool)
    (authored : SurfaceBooleanValueCountSource) :
    Option NumericComputationElabError :=
  match operation expected authored with
  | .ok _ => none
  | .error error => some error

private def repeatableOperation :
    Except NumericComputationElabError
      (CheckedNumericComputationOperation repeatableModel) :=
  elaborateCompleteNumericComputationOperation
    repeatableModel ["Flags"] target.id
      (surface true repeatableSource)

private def context (a b confirmed : RawCell) :
    ScalarComputationContext where
  read field :=
    if field == firstBoolean.id then firstBoolean.checkRaw a
    else if field == secondBoolean.id then secondBoolean.checkRaw b
    else if field == confirmation.id then confirmation.checkRaw confirmed
    else malformedCheckedCell

private def evaluated (expected : Bool)
    (authored : SurfaceBooleanValueCountSource)
    (a b confirmed : RawCell) : Option NumericComputationResult := do
  let checked ← (operation expected authored).toOption
  (checked.evaluate (context a b confirmed)).toOption

private def checkedNumber (raw : RawCell) : CheckedCell :=
  formalCheck { kind := .number { scale := 0, signed := false } } raw

private def repeatableDocument : Document :=
  { instantiatedRows := [1, 2].map fun row =>
      { group := 10, path := [row] }
    rawCells := fun _ => none }

private def repeatableRead
    (gates booleans : RowIndex → CheckedCell)
    (environment : Env) (field : FieldId) : CheckedCell :=
  if field == outerGate.id then checkedNumber (.parsed (.num 1))
  else
    match environment with
    | [(10, row)] =>
        if field == repeatedGate.id then gates row
        else if field == repeatedBoolean.id then booleans row
        else malformedCheckedCell
    | _ => malformedCheckedCell

private def repeatableContext
    (gates booleans : RowIndex → CheckedCell) :
    NumericComputationEvaluationContext :=
  { scalar := {
      read := fun field =>
        if field == outerGate.id then checkedNumber (.parsed (.num 1))
        else malformedCheckedCell }
    document := repeatableDocument
    outer := []
    filterRead := repeatableRead gates booleans
    starRead := repeatableRead gates booleans }

private def repeatableEvaluated
    (gates booleans : RowIndex → CheckedCell) :
    Option NumericComputationResult := do
  let checked ← repeatableOperation.toOption
  (checked.evaluateIn (repeatableContext gates booleans)).toOption

private def repeatableScalarFault : Option NumericComputationFault := do
  let checked ← repeatableOperation.toOption
  match checked.evaluate {
      read := fun _ => malformedCheckedCell } with
  | .ok _ => none
  | .error error => some error

private def checkedFacts :
    Option (Bool × Bool × Bool × NumericScaleSummary × Bool) := do
  let checked ← (operation true (source "A" "Confirmed")).toOption
  pure (
    checked.core.expression.anyAtom
      (CheckedNumericComputationAtom.references model target.id),
    checked.core.expression.anyAtom
      (CheckedNumericComputationAtom.references model firstBoolean.id),
    checked.core.expression.anyAtom
      (CheckedNumericComputationAtom.references model confirmation.id),
    (checked.core.expression.summary?
      CheckedNumericComputationAtom.numericScaleSummary).getD
        { scale := .unknown, canExpandScale := false },
    checked.core.expression.allAtoms
      CheckedNumericComputationAtom.supportsScalarEvaluation)

private def generatedFacts :
    Option (Bool × Bool × NumericOperandScope) := do
  let checked ← (operation true (source "A" "Confirmed")).toOption
  let comparison ← (checked.generatedMismatchComparison none).toOption
  pure (
    comparison.core.referencesField firstBoolean.id,
    comparison.core.referencesField confirmation.id,
    comparison.operandScope)

private def generatedVerdict
    (count : Rat) (a confirmed : RawCell) : Option Verdict := do
  let checked ← (operation true (source "A" "Confirmed")).toOption
  let comparison ← (checked.generatedMismatchComparison none).toOption
  let raw : RawFlatContext := {
    read field :=
      if field == target.id then .parsed (.num count)
      else if field == firstBoolean.id then a
      else if field == confirmation.id then confirmed
      else .empty }
  pure (comparison.evalFull (model.checkContext raw) true)

private def repeatableGeneratedFacts :
    Option (Bool × Bool × Bool × NumericOperandScope) := do
  let checked ← repeatableOperation.toOption
  let comparison ← (checked.generatedMismatchComparison none).toOption
  pure (
    comparison.core.referencesField target.id,
    comparison.core.referencesField repeatedBoolean.id,
    comparison.core.referencesField repeatedGate.id,
    comparison.operandScope)

private def repeatableGeneratedVerdict
    (targetValue : Rat)
    (gates booleans : RowIndex → CheckedCell) :
    Option Verdict := do
  let checked ← repeatableOperation.toOption
  let comparison ← (checked.generatedMismatchComparison none).toOption
  let scalar : ValidationEvaluationContext := {
    fields := {
      read := fun field =>
        if field == target.id then checkedNumber (.parsed (.num targetValue))
        else if field == outerGate.id then
          checkedNumber (.parsed (.num 1))
        else malformedCheckedCell }
    groups := GroupPresenceContext.unavailable }
  (comparison.evalAddressed {
    scalar
    outer := []
    input := .legacy repeatableDocument (repeatableRead gates booleans)
  }).toOption

/- `True` admits Boolean plus Confirm, while the computation boundary preserves the `False` family rejection for Confirm. -/
example :
    operationError true (source "A" "Confirmed") = none ∧
      operationError false (source "A" "B") = none ∧
      operationError false (source "A" "Confirmed") =
        some (.booleanValueCount
          (.fieldKindMismatch confirmation.path false .confirm)) := by
  native_decide

/- Scalar computation counts canonical checked values, and the first reached formal failure remains poison. -/
example :
    evaluated true (source "A" "Confirmed")
        (.parsed (.bool true)) .empty (.parsed (.conf true)) =
      some (.value 2) ∧
    evaluated false (source "A" "B")
        (.parsed (.bool true)) (.parsed (.bool false)) .empty =
      some (.value 1) ∧
    evaluated true (source "A" "Confirmed")
        (.rejected .booleanToken) .empty (.parsed (.conf true)) =
      some (.poison .booleanToken) := by
  native_decide

/- The checked atom has integral scale, references exactly its source fields, and remains scalar-executable. A Number target cannot inhabit the statically Boolean/Confirm source family. -/
example :
    checkedFacts =
      some (false, true, true, NumericScaleSummary.field 0, true) := by
  native_decide

/- Generated validation retains the same checked source and direct model-wide scope; equality suppresses the generated mismatch and a different target fires it. -/
example :
    generatedFacts =
        some (true, true, .modelWideNonrepeatable) ∧
      generatedVerdict 2 (.parsed (.bool true)) (.parsed (.conf true)) =
        some .notFired ∧
      generatedVerdict 1 (.parsed (.bool true)) (.parsed (.conf true)) =
        some (.fired .value) := by
  native_decide

/- A filtered Boolean star is addressed end to end: scalar execution rejects the missing topology, selected rows count through the full computation evaluator, and a reached filter failure becomes poison before any target value is produced. -/
example :
    let selected : RowIndex → CheckedCell
      | 1 => formalCheck { kind := .boolean } (.parsed (.bool true))
      | 2 => formalCheck { kind := .boolean } (.parsed (.bool false))
      | _ => formalCheck { kind := .boolean } .empty
    let matching : RowIndex → CheckedCell
      | 1 | 2 => checkedNumber (.parsed (.num 1))
      | _ => checkedNumber .empty
    let poisoned : RowIndex → CheckedCell
      | 1 => checkedNumber (.rejected .malformed)
      | _ => checkedNumber .empty
    repeatableScalarFault = some .repeatableContextRequired ∧
      repeatableEvaluated matching selected = some (.value 1) ∧
      repeatableEvaluated poisoned selected = some (.poison .malformed) := by
  native_decide

/- Generated validation retains the repeatable source and `Having` dependency in its checked model-wide scope, then compares the addressed count rather than silently falling back to scalar reads. -/
example :
    let selected : RowIndex → CheckedCell
      | 1 => formalCheck { kind := .boolean } (.parsed (.bool true))
      | 2 => formalCheck { kind := .boolean } (.parsed (.bool false))
      | _ => formalCheck { kind := .boolean } .empty
    let matching : RowIndex → CheckedCell
      | 1 | 2 => checkedNumber (.parsed (.num 1))
      | _ => checkedNumber .empty
    repeatableGeneratedFacts =
        some (true, true, true, .modelWideCheckedComputation) ∧
      repeatableGeneratedVerdict 1 matching selected =
        some .notFired ∧
      repeatableGeneratedVerdict 2 matching selected =
        some (.fired .omission) := by
  native_decide

end A12Kernel.Conformance.NumericComputation.BooleanValueCount
