import A12Kernel.Elaboration.AddressedStringFirstFilledFormalInput

/-! # Exact-address repeatable ordinary String `FirstFilledValue` locks -/

namespace A12Kernel.Conformance.AddressedStringFirstFilledComputation

open A12Kernel

private def stringField (id : FieldId) (name : String)
    (groupPath : GroupPath) (scope : List RepeatableLevel := [])
    (policy : StringFieldPolicy := {}) : FlatFieldDecl := {
  id, name, groupPath, repeatableScope := scope
  policy := { kind := .string }
  stringPolicy := policy
}

private def source := stringField 1 "Code"
  ["Projects", "Choices"] [10, 20]
private def target : FlatFieldDecl := {
  stringField 2 "Selected" ["Projects", "Tasks"] [10, 30]
    { maxLength := some 3 } with
  stringPatternSource := some "A+"
}
private def fixedTarget := stringField 4 "Fixed" ["Summary"]
private def rawSource : FlatFieldDecl := {
  stringField 5 "RawCode" ["Projects", "Choices"] [10, 20]
    { lineBreaksPermitted := true } with
  stringValueMode := .raw
}
private def rawTarget : FlatFieldDecl := {
  stringField 6 "RawSelected" ["Projects", "Tasks"] [10, 30]
    { lineBreaksPermitted := true } with
  stringValueMode := .raw
}
private def numberSource : FlatFieldDecl := {
  id := 7
  name := "Amount"
  groupPath := ["Projects", "Choices"]
  repeatableScope := [10, 20]
  policy := { kind := .number { scale := 0, signed := true } }
}
private def numberTarget : FlatFieldDecl := {
  numberSource with
  id := 8
  name := "SelectedAmount"
  groupPath := ["Projects", "Tasks"]
  repeatableScope := [10, 30]
}
private def nestedSource := stringField 9 "NestedCode"
  ["Projects", "Choices", "Details"] [10, 20, 40]
private def unboundTarget := stringField 10 "UnboundSelected"
  ["OtherTasks"] [50]
private def rootSource := stringField 11 "GlobalCode"
  ["GlobalChoices"] [60]
private def targetDescendantSource := stringField 12 "TaskDetailCode"
  ["Projects", "Tasks", "TaskDetails"] [10, 30, 70]

private def model : FlatModel := {
  fields := [source, target, fixedTarget, rawSource, rawTarget,
    numberSource, numberTarget, nestedSource, unboundTarget, rootSource,
    targetDescendantSource]
  repeatableGroups := [
    { level := 10, path := ["Projects"], repeatability := some 6 },
    { level := 20, path := ["Projects", "Choices"], repeatability := some 2,
      indexField := some source.id },
    { level := 30, path := ["Projects", "Tasks"], repeatability := some 2 },
    { level := 40, path := ["Projects", "Choices", "Details"],
      repeatability := some 2 },
    { level := 50, path := ["OtherTasks"], repeatability := some 2 },
    { level := 60, path := ["GlobalChoices"], repeatability := some 2 },
    { level := 70, path := ["Projects", "Tasks", "TaskDetails"],
      repeatability := some 2 }]
}

private def siblingStar (field : String) : SurfaceStarFieldPath := {
  base := .relative 1
  groups := [{ name := "Choices", starred := true }]
  field
}

private def nestedSiblingStar : SurfaceStarFieldPath := {
  base := .relative 1
  groups := [
    { name := "Choices", starred := true },
    { name := "Details", starred := true }]
  field := nestedSource.name
}

private def partialBindingStar : SurfaceStarFieldPath := {
  base := .relative 1
  groups := [
    { name := "Choices" },
    { name := "Details", starred := true }]
  field := nestedSource.name
}

private def absoluteSiblingStar : SurfaceStarFieldPath := {
  base := .absolute
  groups := [
    { name := "Projects" },
    { name := "Choices", starred := true }]
  field := source.name
}

private def rootStar : SurfaceStarFieldPath := {
  base := .absolute
  groups := [{ name := "GlobalChoices", starred := true }]
  field := rootSource.name
}

private def selfStar : SurfaceStarFieldPath := {
  base := .relative 1
  groups := [{ name := "Tasks", starred := true }]
  field := target.name
}

private def targetDescendantStar : SurfaceStarFieldPath := {
  base := .relative 0
  groups := [{ name := "TaskDetails", starred := true }]
  field := targetDescendantSource.name
}

private def operation? :
    Option (CheckedAddressedStringFirstFilledComputation model) :=
  (checkAddressedStringFirstFilledComputation model
    ["Projects", "Tasks"] target.id (siblingStar source.name)).toOption

private def elabError? (checked : Except
    AddressedStringFirstFilledComputationElabError
    (CheckedAddressedStringFirstFilledComputation model)) :=
  match checked with
  | .error cause => some cause
  | .ok _ => none

/- The checked boundary separates repeatable target placement, ordinary String carrier admission, sibling-star scope, and self-reference. Placement is containment: the ancestor `["Projects"]` is admitted with an operand spelled for that base, while `["Projects", "Choices"]` — which shares the target's enclosing prefix without containing it — is refused, so an account keyed on a common ancestor still admits what only containment rejects. -/
example : operation?.isSome = true ∧
    elabError? (checkAddressedStringFirstFilledComputation model
      ["Projects", "Tasks"] 99 (siblingStar source.name)) =
        some (.target (.unknownFieldId 99)) ∧
    elabError? (checkAddressedStringFirstFilledComputation model
      ["Summary"] target.id (siblingStar source.name)) =
        some (.targetOutsideDeclaringGroup target.path ["Summary"]) ∧
    (checkAddressedStringFirstFilledComputation model
      ["Projects"] target.id absoluteSiblingStar).toOption.isSome = true ∧
    elabError? (checkAddressedStringFirstFilledComputation model
      ["Projects", "Choices"] target.id absoluteSiblingStar) =
        some (.targetOutsideDeclaringGroup target.path ["Projects", "Choices"]) ∧
    elabError? (checkAddressedStringFirstFilledComputation model
      ["Summary"] fixedTarget.id (siblingStar source.name)) =
        some (.targetNotRepeatable fixedTarget.path) ∧
    elabError? (checkAddressedStringFirstFilledComputation model
      ["Projects", "Tasks"] numberTarget.id (siblingStar source.name)) =
        some (.targetNotOrdinaryString numberTarget.path) ∧
    elabError? (checkAddressedStringFirstFilledComputation model
      ["Projects", "Tasks"] rawTarget.id (siblingStar source.name)) =
        some (.targetNotOrdinaryString rawTarget.path) ∧
    elabError? (checkAddressedStringFirstFilledComputation model
      ["Projects", "Tasks"] target.id (siblingStar numberSource.name)) =
        some (.sourceNotOrdinaryString numberSource.path) ∧
    elabError? (checkAddressedStringFirstFilledComputation model
      ["Projects", "Tasks"] target.id (siblingStar rawSource.name)) =
        some (.sourceNotOrdinaryString rawSource.path) ∧
    elabError? (checkAddressedStringFirstFilledComputation model
      ["Projects", "Tasks"] target.id nestedSiblingStar) =
        some (.sourceShape nestedSource.path) ∧
    elabError? (checkAddressedStringFirstFilledComputation model
      ["Projects", "Tasks"] target.id partialBindingStar) =
        some (.sourceScope nestedSource.path) ∧
    elabError? (checkAddressedStringFirstFilledComputation model
      ["OtherTasks"] unboundTarget.id absoluteSiblingStar) =
        some (.sourceScope source.path) ∧
    elabError? (checkAddressedStringFirstFilledComputation model
      ["Projects", "Tasks"] target.id rootStar) =
        some (.sourceScope rootSource.path) ∧
    elabError? (checkAddressedStringFirstFilledComputation model
      ["Projects", "Tasks"] target.id targetDescendantStar) =
        some (.sourceScope targetDescendantSource.path) ∧
    elabError? (checkAddressedStringFirstFilledComputation model
      ["Projects", "Tasks"] target.id selfStar) =
        some (.targetSelfReference target.id) := by
  native_decide

private def patternCompiler : StringPatternCompiler := fun pattern =>
  if pattern == "A+" then
    some fun value =>
      !value.isEmpty && value.toList.all fun character => character == 'A'
  else
    none

private def prepared : PreparedFlatStringContext model patternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    patternCompiler model).toOption.get (by native_decide)

private def rows : List RowAddr := [
  { group := 10, path := [1] }, { group := 10, path := [2] },
  { group := 10, path := [3] }, { group := 10, path := [4] },
  { group := 10, path := [5] }, { group := 10, path := [6] },
  { group := 20, path := [1, 1] }, { group := 20, path := [1, 2] },
  { group := 20, path := [2, 1] },
  { group := 20, path := [4, 1] }, { group := 20, path := [5, 1] },
  { group := 20, path := [6, 1] },
  { group := 30, path := [2, 1] }, { group := 30, path := [1, 1] },
  { group := 30, path := [4, 1] }, { group := 30, path := [3, 1] },
  { group := 30, path := [6, 1] }, { group := 30, path := [5, 1] }]

private def cell (field : FieldId) (path : List Nat)
    (stored : String) (raw : RawCell := .parsed (.str stored)) :
    ClassifiedCellInput := {
  address := { field, path }
  stored
  raw
}

private def address (field : FieldId) (path : List Nat) : CellAddr :=
  { field, path }

private def documentWithRows? (selectedRows : List RowAddr)
    (cells : List ClassifiedCellInput) :
    Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := selectedRows, cells }).toOption

private def document? (cells : List ClassifiedCellInput) :
    Option (CheckedDocument model) :=
  documentWithRows? rows cells

private def inputCells : List ClassifiedCellInput := [
  cell source.id [1, 1] "" .presentEmpty,
  cell source.id [1, 2] "AA",
  cell source.id [2, 1] "AB",
  cell source.id [4, 1] "AAAA",
  cell source.id [5, 1] "7" (.parsed (.num 7)),
  cell source.id [6, 1] "AAA",
  cell target.id [1, 1] "AA",
  cell target.id [2, 1] "A",
  cell target.id [3, 1] "A",
  cell target.id [5, 1] "A",
  cell target.id [6, 1] "A"]

private def input? : Option (CheckedDocument model) := document? inputCells

private def missingTargetMatcher :
    PreparedFlatStringPatterns model patternCompiler := {
  fields := []
  modelWellFormed := prepared.patterns.modelWellFormed
}

/- An incomplete prepared-pattern input fails at the exact target before any row outcome can silently bypass its declared pattern. -/
example : (do
    let operation ← operation?
    let input ← input?
    match operation.execute missingTargetMatcher input with
    | .error cause => some cause
    | .ok _ => none) =
      some (.targetPatternUnavailable target.id) := by
  native_decide

/- Each physical target row scans only its enclosing sibling extent before the exact target policy and prepared matcher classify the selected String. -/
example : (do
    let operation ← operation?
    let input ← input?
    let outcomes ← operation.execute prepared.patterns input |>.toOption
    pure (outcomes.map fun entry => (entry.targetField, entry.outcome))) = some [
      (address target.id [2, 1],
        .errored ⟨"AB", by decide⟩ .pattern),
      (address target.id [1, 1], .accepted ⟨"AA", by decide⟩),
      (address target.id [4, 1],
        .errored ⟨"AAAA", by decide⟩ .tooLong),
      (address target.id [3, 1], .noValue),
      (address target.id [6, 1], .accepted ⟨"AAA", by decide⟩),
      (address target.id [5, 1], .poison .malformed)] := by
  native_decide

private structure ResultApplicationSummary where
  values : List (CellAddr × String)
  changes : List (CellAddr × String)
  errors : List (CellAddr × String × StringTargetError)
  cleared : List CellAddr
  residual : List FormalCause
  applied : List StringTargetState
  unrelatedState : StringTargetState
  deriving Repr, DecidableEq

private def resultApplicationSummary? : Option ResultApplicationSummary := do
  let operation ← operation?
  let input ← input?
  let destination ← document? [
    cell target.id [1, 1] "A", cell target.id [2, 1] "A",
    cell target.id [3, 1] "A", cell target.id [4, 1] "A",
    cell target.id [5, 1] "A", cell target.id [6, 1] "A",
    cell fixedTarget.id [] "KEEP"]
  let result ← operation.executeResult prepared.patterns input
    ([.malformed] : List FormalCause) |>.toOption
  let applied ← result.applyToChecked destination |>.toOption
  let targetAt := fun row => address target.id [row, 1]
  pure {
    values := result.string.withoutErrors.map fun item =>
      (item.targetField, item.value.text)
    changes := result.string.withChanges.map fun item =>
      (item.targetField, item.value.text)
    errors := result.string.withErrors.map fun item =>
      (item.targetField, item.attempted.text, item.cause)
    cleared := result.string.cleared
    residual := result.string.formalErrorsInOperands
    applied := [1, 2, 3, 4, 5, 6].map fun row => applied (targetAt row)
    unrelatedState := applied (address fixedTarget.id [])
  }

/- Result classification stays relative to the immutable source, while application changes only retained exact-address actions in a separate destination. -/
example : resultApplicationSummary? = some {
    values := [
      (address target.id [1, 1], "AA"),
      (address target.id [6, 1], "AAA")]
    changes := [(address target.id [6, 1], "AAA")]
    errors := [
      (address target.id [2, 1], "AB", .pattern),
      (address target.id [4, 1], "AAAA", .tooLong)]
    cleared := [address target.id [3, 1], address target.id [5, 1]]
    residual := [.malformed]
    applied := [
      .presentValue ⟨"A", by decide⟩,
      .presentEmpty,
      .presentEmpty,
      .presentEmpty,
      .presentEmpty,
      .presentValue ⟨"AAA", by decide⟩]
    unrelatedState := .presentValue ⟨"KEEP", by decide⟩
  } := by
  native_decide

private def formalFinding (path : List Nat)
    (cause : FormalCause) : ComputationFormalInputFinding := {
  address := address source.id path
  cause
}

private structure FormalInputSummary where
  planOperands : List FieldId
  planTargets : List FieldId
  findingsExact : Bool
  values : List (CellAddr × String)
  changes : List (CellAddr × String)
  errorsEmpty : Bool
  cleared : List CellAddr
  deriving Repr, DecidableEq

private def formalInputSummary? : Option FormalInputSummary := do
  let operation ← operation?
  let plan ← operation.formalInputPlan.toOption
  let input ← documentWithRows? [
      { group := 10, path := [1] }, { group := 10, path := [2] },
      { group := 20, path := [1, 1] },
      { group := 20, path := [2, 1] },
      { group := 20, path := [2, 2] },
      { group := 30, path := [1, 1] },
      { group := 30, path := [2, 1] }] [
    cell source.id [1, 1] "AA",
    cell source.id [2, 1] "AB",
    cell source.id [2, 2] "AB",
    cell target.id [1, 1] "A",
    cell target.id [2, 1] "A"]
  let result ← operation.executeResultWithFormalInputs prepared.patterns input
    |>.toOption
  let findings := result.string.formalErrorsInOperands
  pure {
    planOperands := plan.operandFields
    planTargets := plan.computedFields
    findingsExact := findings.length == 2 &&
      findings.contains (formalFinding [2, 1] .duplicateIndex) &&
      findings.contains (formalFinding [2, 2] .duplicateIndex)
    values := result.string.withoutErrors.map fun item =>
      (item.targetField, item.value.text)
    changes := result.string.withChanges.map fun item =>
      (item.targetField, item.value.text)
    errorsEmpty := result.string.withErrors.isEmpty
    cleared := result.string.cleared
  }

/- The selected String preliminary stays eager, but duplicate poison wins only when its parent-local scan reaches the annotated cell and therefore bypasses target-pattern rejection. -/
example : formalInputSummary? = some {
    planOperands := [source.id]
    planTargets := [target.id]
    findingsExact := true
    values := [(address target.id [1, 1], "AA")]
    changes := [(address target.id [1, 1], "AA")]
    errorsEmpty := true
    cleared := [address target.id [2, 1]]
  } := by
  native_decide

end A12Kernel.Conformance.AddressedStringFirstFilledComputation
