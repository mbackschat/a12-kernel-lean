import A12Kernel.Elaboration.AddressedBooleanFirstFilledFormalInput

/-! # Exact-address repeatable Boolean `FirstFilledValue` locks -/

namespace A12Kernel.Conformance.AddressedBooleanFirstFilledComputation

open A12Kernel

private def booleanField (id : FieldId) (name : String)
    (groupPath : GroupPath) (scope : List RepeatableLevel) : FlatFieldDecl := {
  id, name, groupPath, repeatableScope := scope
  policy := { kind := .boolean }
}

private def source := booleanField 1 "Decision"
  ["Projects", "Choices"] [10, 20]

private def target := booleanField 2 "Selected"
  ["Projects", "Tasks"] [10, 30]

private def unrelated := booleanField 3 "Unrelated" ["Summary"] []

private def fixedTarget := booleanField 4 "Fixed" ["Summary"] []

private def confirmSource : FlatFieldDecl := {
  source with id := 5, name := "Confirmed", policy := { kind := .confirm }
}

private def nestedSource := booleanField 6 "NestedDecision"
  ["Projects", "Choices", "Details"] [10, 20, 40]

private def unboundTarget := booleanField 7 "UnboundSelected"
  ["OtherTasks"] [50]

private def rootSource := booleanField 8 "GlobalDecision"
  ["GlobalChoices"] [60]

private def peerSource := booleanField 9 "PeerDecision"
  ["Projects", "Tasks"] [10, 30]

private def model : FlatModel := {
  fields := [source, target, unrelated, fixedTarget, confirmSource, nestedSource,
    unboundTarget, rootSource, peerSource]
  repeatableGroups := [
    { level := 10, path := ["Projects"], repeatability := some 4 },
    { level := 20, path := ["Projects", "Choices"], repeatability := some 3,
      indexField := some source.id },
    { level := 30, path := ["Projects", "Tasks"], repeatability := some 3 },
    { level := 40, path := ["Projects", "Choices", "Details"],
      repeatability := some 3 },
    { level := 50, path := ["OtherTasks"], repeatability := some 3 },
    { level := 60, path := ["GlobalChoices"], repeatability := some 3 }]
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

private def selfStar : SurfaceStarFieldPath := {
  base := .relative 1
  groups := [{ name := "Tasks", starred := true }]
  field := target.name
}

private def peerStar : SurfaceStarFieldPath := {
  base := .relative 1
  groups := [{ name := "Tasks", starred := true }]
  field := peerSource.name
}

private def absoluteSiblingStar : SurfaceStarFieldPath := {
  base := .absolute
  groups := [
    { name := "Projects" },
    { name := "Choices", starred := true }]
  field := source.name
}

/-- The sibling star as it must be spelled from the ancestor `["Projects"]` rather than from the
target's own group: same operand, one fewer level of parent walk. -/
private def respelledSiblingStar : SurfaceStarFieldPath := {
  base := .relative 0
  groups := [{ name := "Choices", starred := true }]
  field := source.name
}

private def rootStar : SurfaceStarFieldPath := {
  base := .absolute
  groups := [{ name := "GlobalChoices", starred := true }]
  field := rootSource.name
}

private def operation? :
    Option (CheckedAddressedBooleanFirstFilledComputation model) :=
  (checkAddressedBooleanFirstFilledComputation model
    ["Projects", "Tasks"] target.id (siblingStar source.name)).toOption

private def elabError? (checked :
    Except AddressedBooleanFirstFilledComputationElabError
      (CheckedAddressedBooleanFirstFilledComputation model)) :
    Option AddressedBooleanFirstFilledComputationElabError :=
  match checked with
  | .error cause => some cause
  | .ok _ => none

/- Placement is containment, not parenthood, and it is separate from operand resolution. The ancestor
`["Projects"]` admits the target with an absolute operand and with the operand re-spelled for that base; both
admissions are Kernel-measured at the
[declaring-group gate checkpoint](../../docs/SOURCES.md#src-computation-declaring-group-gate).
`["Projects", "Choices"]` is the discriminating refusal: it is a declared group that shares the target's
enclosing `["Projects"]` prefix without containing the target, so an account keyed on a shared first segment
or on any common-ancestor test still admits it, and only containment refuses it. That is the shape the
checkpoint's operand-bearing row measured. The complementary direction — a declared group strictly *below*
the target — is separated by the other families named in
[SG4](../../docs/SEMANTICS-GAPS.md#sg4--computation-scheduling-and-state-transition). -/
example :
    (checkAddressedBooleanFirstFilledComputation model
      ["Projects"] target.id absoluteSiblingStar).toOption.isSome = true ∧
    (checkAddressedBooleanFirstFilledComputation model
      ["Projects"] target.id respelledSiblingStar).toOption.isSome = true ∧
    elabError? (checkAddressedBooleanFirstFilledComputation model
      ["Projects", "Choices"] target.id absoluteSiblingStar) =
        some (.targetOutsideDeclaringGroup target.path ["Projects", "Choices"]) ∧
    elabError? (checkAddressedBooleanFirstFilledComputation model
      ["Summary"] target.id absoluteSiblingStar) =
        some (.targetOutsideDeclaringGroup target.path ["Summary"]) := by
  native_decide

/- Keeping the target-relative spelling while moving to the ancestor fails in the *source*, not the placement,
so the two causes stay separable. The encoding differs from the Kernel here and the case records only the local
outcome: this fragment refuses the walk itself, because one parent exceeds a one-segment declaring group, while
the Kernel's measured `..` reached its root and then failed the lookup under it. Same separation of causes,
different cause on this cell. -/
example :
    elabError? (checkAddressedBooleanFirstFilledComputation model
      ["Projects"] target.id (siblingStar source.name)) =
        some (.source (.resolve (.aboveRoot 1))) := by
  native_decide

/- Containment is checked against a representable declaring group, never on its own: `[]` is a prefix of every
path, so containment alone would treat it as containing everything. An empty segment is refused here too,
though that cell is about the reported cause rather than admission, since no declaration path can contain one. -/
example :
    elabError? (checkAddressedBooleanFirstFilledComputation model
      [] target.id absoluteSiblingStar) =
        some (.target (.invalidRuleGroup [])) ∧
    elabError? (checkAddressedBooleanFirstFilledComputation model
      ["Projects", ""] target.id absoluteSiblingStar) =
        some (.target (.invalidRuleGroup ["Projects", ""])) := by
  native_decide

/- The addressed boundary requires a repeatable Boolean target, one Boolean star axis, and no target self-read. -/
example :
    operation?.isSome = true ∧
    elabError? (checkAddressedBooleanFirstFilledComputation model
      ["Summary"] fixedTarget.id (siblingStar source.name)) =
        some (.targetNotRepeatable fixedTarget.path) ∧
    elabError? (checkAddressedBooleanFirstFilledComputation model
      ["Projects", "Choices"] confirmSource.id (siblingStar source.name)) =
        some (.targetKind confirmSource.path .confirm) ∧
    elabError? (checkAddressedBooleanFirstFilledComputation model
      ["Projects", "Tasks"] target.id (siblingStar confirmSource.name)) =
        some (.sourceKind confirmSource.path .confirm) ∧
    elabError? (checkAddressedBooleanFirstFilledComputation model
      ["Projects", "Tasks"] target.id nestedSiblingStar) =
        some (.sourceShape nestedSource.path) ∧
    elabError? (checkAddressedBooleanFirstFilledComputation model
      ["OtherTasks"] unboundTarget.id absoluteSiblingStar) =
        some (.sourceScope source.path) ∧
    elabError? (checkAddressedBooleanFirstFilledComputation model
      ["Projects", "Tasks"] target.id rootStar) =
        some (.sourceScope rootSource.path) ∧
    elabError? (checkAddressedBooleanFirstFilledComputation model
      ["Projects", "Tasks"] target.id peerStar) =
        some (.sourceScope peerSource.path) ∧
    elabError? (checkAddressedBooleanFirstFilledComputation model
      ["Projects", "Tasks"] target.id selfStar) =
        some (.targetSelfReference target.id) := by
  native_decide

private def prepared :
    PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def rows : List RowAddr :=
  [{ group := 10, path := [1] }, { group := 10, path := [2] },
    { group := 10, path := [3] }, { group := 10, path := [4] },
    { group := 20, path := [1, 1] }, { group := 20, path := [2, 1] },
    { group := 20, path := [4, 1] },
    { group := 30, path := [2, 1] }, { group := 30, path := [1, 2] },
    { group := 30, path := [4, 2] }, { group := 30, path := [1, 1] },
    { group := 30, path := [3, 1] }, { group := 30, path := [4, 1] },
    { group := 30, path := [3, 2] }]

private def cell (field : FieldId) (path : List Nat)
    (stored : String) : ClassifiedCellInput := {
  address := { field, path }
  stored
  raw := classifyStoredBooleanText stored
}

private def documentWithRows? (selectedRows : List RowAddr)
    (cells : List ClassifiedCellInput) :
    Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := selectedRows, cells }).toOption

private def document? (cells : List ClassifiedCellInput) :
    Option (CheckedDocument model) :=
  documentWithRows? rows cells

private def address (field : FieldId) (path : List Nat) : CellAddr :=
  { field, path }

private def input? : Option (CheckedDocument model) :=
  document? [
    cell source.id [1, 1] "false",
    cell source.id [2, 1] "true",
    cell source.id [4, 1] "TRUE",
    cell target.id [1, 1] "false",
    cell target.id [1, 2] "true",
    cell target.id [3, 1] "true",
    cell target.id [4, 1] "false",
    cell unrelated.id [] "true"]

/- Moving the declaration to an ancestor changes admission, never correlation: the ancestor-declared
operations produce the same rows, in the same order, with the same values as the declaration at the target's
own group. The [declaring-group gate checkpoint](../../docs/SOURCES.md#src-computation-declaring-group-gate)
measures that invariance against the Kernel across the containment range on both codegen strategies; this
locks it for the executable account, which is what makes widening admission safe for the correlation clause. -/
example : (do
    let own ← operation?
    let ancestorAbsolute ← (checkAddressedBooleanFirstFilledComputation model
      ["Projects"] target.id absoluteSiblingStar).toOption
    let ancestorRespelled ← (checkAddressedBooleanFirstFilledComputation model
      ["Projects"] target.id respelledSiblingStar).toOption
    let input ← input?
    let ownOutcomes ← own.execute input |>.toOption
    let absoluteOutcomes ← ancestorAbsolute.execute input |>.toOption
    let respelledOutcomes ← ancestorRespelled.execute input |>.toOption
    let view := fun (entries : List _) =>
      entries.map fun entry => (entry.targetField, entry.result)
    pure ((view absoluteOutcomes == view ownOutcomes)
      && (view respelledOutcomes == view ownOutcomes))) = some true := by
  native_decide

/- Each target row scans only its enclosing parent's sibling source rows. False remains a value, an empty sibling extent yields no value, and malformed content poisons only that parent. -/
example : (do
    let operation ← operation?
    let input ← input?
    let outcomes ← operation.execute input |>.toOption
    pure (outcomes.map fun entry => (entry.targetField, entry.result))) = some [
      (address target.id [2, 1], .value true),
      (address target.id [1, 2], .value false),
      (address target.id [4, 2], .poison .booleanToken),
      (address target.id [1, 1], .value false),
      (address target.id [3, 1], .noValue),
      (address target.id [4, 1], .poison .booleanToken),
      (address target.id [3, 2], .noValue)] := by
  native_decide

private structure ResultApplicationSummary where
  values : List (CellAddr × Bool)
  changes : List (CellAddr × Bool)
  cleared : List CellAddr
  row11 : BooleanTargetState
  row12 : BooleanTargetState
  row21 : BooleanTargetState
  row31 : BooleanTargetState
  row32 : BooleanTargetState
  row41 : BooleanTargetState
  row42 : BooleanTargetState
  unrelatedState : BooleanTargetState
  deriving Repr, DecidableEq

private def resultApplicationSummary? : Option ResultApplicationSummary := do
  let operation ← operation?
  let input ← input?
  let destination ← document? [
    cell target.id [1, 1] "true",
    cell target.id [2, 1] "false",
    cell target.id [4, 1] "true",
    cell unrelated.id [] "false"]
  let result ← operation.executeResult input
    ([.booleanToken] : List FormalCause) |>.toOption
  let applied := result.applyToChecked destination
  pure {
    values := result.boolean.withoutErrors.map fun item =>
      (item.targetField, item.value)
    changes := result.boolean.withChanges.map fun item =>
      (item.targetField, item.value)
    cleared := result.boolean.cleared
    row11 := applied (address target.id [1, 1])
    row12 := applied (address target.id [1, 2])
    row21 := applied (address target.id [2, 1])
    row31 := applied (address target.id [3, 1])
    row32 := applied (address target.id [3, 2])
    row41 := applied (address target.id [4, 1])
    row42 := applied (address target.id [4, 2])
    unrelatedState := applied (address unrelated.id [])
  }

/- Result classification uses immutable exact target state, then changed values and retained clears apply to a separate destination without disturbing unchanged or unrelated cells. -/
example : resultApplicationSummary? = some {
    values := [
      (address target.id [2, 1], true),
      (address target.id [1, 2], false),
      (address target.id [1, 1], false)]
    changes := [
      (address target.id [2, 1], true),
      (address target.id [1, 2], false)]
    cleared := [address target.id [3, 1], address target.id [4, 1]]
    row11 := .presentValue true
    row12 := .presentValue false
    row21 := .presentValue true
    row31 := .presentEmpty
    row32 := .absent
    row41 := .presentEmpty
    row42 := .absent
    unrelatedState := .presentValue false
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
  values : List (CellAddr × Bool)
  changes : List (CellAddr × Bool)
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
    cell source.id [1, 1] "false",
    cell source.id [2, 1] "true",
    cell source.id [2, 2] "true",
    cell target.id [1, 1] "true",
    cell target.id [2, 1] "false"]
  let result ← operation.executeResultWithFormalInputs input |>.toOption
  let findings := result.boolean.formalErrorsInOperands
  pure {
    planOperands := plan.operandFields
    planTargets := plan.computedFields
    findingsExact := findings.length == 2 &&
      findings.contains (formalFinding [2, 1] .duplicateIndex) &&
      findings.contains (formalFinding [2, 2] .duplicateIndex)
    values := result.boolean.withoutErrors.map fun item =>
      (item.targetField, item.value)
    changes := result.boolean.withChanges.map fun item =>
      (item.targetField, item.value)
    cleared := result.boolean.cleared
  }

/- Selected Boolean-index preparation stays eager while runtime poison remains parent-local: a unique `false` is a value and a reached duplicate clears only its source-filled target. -/
example : formalInputSummary? = some {
    planOperands := [source.id]
    planTargets := [target.id]
    findingsExact := true
    values := [(address target.id [1, 1], false)]
    changes := [(address target.id [1, 1], false)]
    cleared := [address target.id [2, 1]]
  } := by
  native_decide

end A12Kernel.Conformance.AddressedBooleanFirstFilledComputation
