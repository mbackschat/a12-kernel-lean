import A12Kernel.Elaboration.AddressedEnumerationComputation

/-! # Repeatable Enumeration computation locks -/

namespace A12Kernel.Conformance.AddressedEnumerationComputation

open A12Kernel

private def enumeration : EnumerationDeclaration := {
  storedTokens := ["A", "B"]
  categories := [{ name := "Choice", tokens := ["A", "B"] }]
}

private def projectedEnumeration : EnumerationDeclaration := {
  storedTokens := ["X", "Y"]
  categories := [{ name := "Target", tokens := ["A", "B"] }]
}

private def incompatibleEnumeration : EnumerationDeclaration := {
  storedTokens := ["A", "C"]
}

private def displayedEnumeration : EnumerationDeclaration := {
  storedTokens := ["A", "B"]
  displayFacts := [
    { locale := "en", stored := "A", display := "Alpha" },
    { locale := "en", stored := "B", display := "Beta" }
  ]
}

private def enumerationField (id : FieldId) (name : String)
    (groupPath : GroupPath) (repeatableScope : List RepeatableLevel)
    (domain : EnumerationDeclaration := enumeration) : FlatFieldDecl := {
  id, name, groupPath, repeatableScope
  policy := { kind := .enumeration }
  enumeration := some domain
}

private def target := enumerationField 1 "Target" ["Form", "Rows"] [10]
private def source := enumerationField 2 "Source" ["Form", "Rows"] [10]
private def projected := enumerationField 3 "Projected" ["Form", "Rows"] [10]
  projectedEnumeration
private def incompatible := enumerationField 4 "Incompatible" ["Form", "Rows"] [10]
  incompatibleEnumeration
private def rootSource := enumerationField 5 "RootSource" ["Form"] []
private def rootTarget := enumerationField 6 "RootTarget" ["Form"] []
private def other := enumerationField 7 "Other" ["Form"] []
private def displayed := enumerationField 8 "Displayed" ["Form", "Rows"] [10]
  displayedEnumeration
private def deepSource := enumerationField 9 "DeepSource"
  ["Form", "Rows", "Details"] [10, 20]

private def model : FlatModel := {
  fields := [target, source, projected, incompatible, rootSource, rootTarget, other,
    displayed, deepSource]
  repeatableGroups := [{
    level := 10, path := ["Form", "Rows"], repeatability := some 4
  }, {
    level := 20, path := ["Form", "Rows", "Details"], repeatability := some 3
  }]
}

private def bare (name : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field := name }

private def parent (name : String) : SurfaceFieldPath :=
  { base := .relative 1, groups := [], field := name }

private def child (name : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := ["Details"], field := name }

private def operation? : Option (CheckedAddressedEnumerationComputation model) :=
  (checkAddressedEnumerationComputation model ["Form", "Rows"] target.id
    (.field (.direct (bare "Source")))).toOption

private def projectedOperation? :
    Option (CheckedAddressedEnumerationComputation model) :=
  (checkAddressedEnumerationComputation model ["Form", "Rows"] target.id
    (.field (.category (bare "Projected") "Target"))).toOption

private def rootSourceOperation? :
    Option (CheckedAddressedEnumerationComputation model) :=
  (checkAddressedEnumerationComputation model ["Form", "Rows"] target.id
    (.field (.direct (parent "RootSource")))).toOption

private def literalOperation? :
    Option (CheckedAddressedEnumerationComputation model) :=
  (checkAddressedEnumerationComputation model ["Form", "Rows"] target.id
    (.literal "B")).toOption

private def errorOf (targetField : FieldId)
    (declaringGroup : GroupPath) (source : SurfaceEnumerationComputationSource) :
    Option AddressedEnumerationComputationElabError :=
  match checkAddressedEnumerationComputation model declaringGroup targetField source with
  | .ok _ => none
  | .error cause => some cause

private def targetDiagnosticOf (source : SurfaceEnumerationComputationSource) :
    Option KernelStaticDiagnostic :=
  (errorOf target.id ["Form", "Rows"] source).bind
    AddressedEnumerationComputationElabError.targetDiagnostic?

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def address (field : FieldId) (row : Nat) : CellAddr :=
  { field, path := [row] }

private def rowCell (field : FlatFieldDecl) (row : Nat)
    (stored : String) (raw : RawCell) : ClassifiedCellInput :=
  { address := address field.id row, stored, raw }

private def rootCell (field : FlatFieldDecl) (stored : String)
    (raw : RawCell) : ClassifiedCellInput :=
  { address := { field := field.id, path := [] }, stored, raw }

private def document? (rowCount : Nat) (cells : List ClassifiedCellInput) :
    Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := (List.range rowCount).map fun index =>
      { group := 10, path := [index + 1] }
    cells
  }).toOption

private def outcomes? (operation : CheckedAddressedEnumerationComputation model)
    (rowCount : Nat) (cells : List ClassifiedCellInput) :
    Option (List (CellAddr × StringTargetOutcome)) := do
  let input ← document? rowCount cells
  let outcomes ← operation.execute input |>.toOption
  pure (outcomes.map fun entry =>
    (entry.targetField, entry.result.asExactStringTargetOutcome))

private def rawOutcomes? (operation : CheckedAddressedEnumerationComputation model)
    (rowCount : Nat) (cells : List ClassifiedCellInput) :
    Option (List (CellAddr × TokenComputationResult)) := do
  let input ← document? rowCount cells
  let outcomes ← operation.execute input |>.toOption
  pure (outcomes.map fun entry => (entry.targetField, entry.result))

private structure ResultApplicationSummary where
  values : List (CellAddr × String)
  changes : List (CellAddr × String)
  errors : List CellAddr
  cleared : List CellAddr
  residual : List FormalCause
  row1 : StringTargetState
  row2 : StringTargetState
  unrelated : StringTargetState
  deriving Repr, DecidableEq

private def resultApplicationSummary? (input destination : CheckedDocument model)
    (residual : List FormalCause := []) : Option ResultApplicationSummary := do
  let operation ← operation?
  let result ← operation.executeResult input residual |>.toOption
  let applied ← result.applyToChecked destination |>.toOption
  pure {
    values := result.string.withoutErrors.map fun item =>
      (item.targetField, item.value.text)
    changes := result.string.withChanges.map fun item =>
      (item.targetField, item.value.text)
    errors := result.string.withErrors.map (·.targetField)
    cleared := result.string.cleared
    residual := result.string.formalErrorsInOperands
    row1 := applied (address target.id 1)
    row2 := applied (address target.id 2)
    unrelated := applied { field := other.id, path := [] }
  }

/- The complete ordinary literal, stored, category, and enclosing-scope source forms are admitted, while a root target remains outside this addressed capsule. -/
example : operation?.isSome = true ∧ projectedOperation?.isSome = true ∧
    rootSourceOperation?.isSome = true ∧ literalOperation?.isSome = true ∧
    errorOf rootTarget.id ["Form"] (.literal "A") =
      some (.targetNotRepeatable rootTarget.path) := by
  native_decide

/- This family carries its own placement gate rather than the shared repeatable-target certificate, so it
needs its own rows. It encodes the same rule — containment against a representable declaring group — with the
ancestor `["Form"]` admitted and the deeper `["Form", "Rows", "Details"]` refused even though it lies inside
the target's own subtree. The invalid-group cause travels on the `ordinary` channel here, because this error
type has no `target` constructor; that is a channel difference, not a different rule. The
[declaring-group gate checkpoint](../../docs/SOURCES.md#src-computation-declaring-group-gate) owns the
Kernel measurement. -/
example :
    errorOf target.id ["Form"] (.literal "B") = none ∧
    errorOf target.id ["Form", "Rows", "Details"] (.literal "B") =
        some (.targetOutsideDeclaringGroup target.path ["Form", "Rows", "Details"]) ∧
    errorOf target.id [] (.literal "B") =
        some (.ordinary (.resolve (.invalidRuleGroup []))) ∧
    errorOf target.id ["Form", ""] (.literal "B") =
        some (.ordinary (.resolve (.invalidRuleGroup ["Form", ""]))) := by
  native_decide

/- Static target-domain compatibility and reading-mode self-reference stay ahead of execution. -/
example :
    errorOf target.id ["Form", "Rows"] (.literal "C") =
        some (.ordinary (.literalOutsideTarget target.path "C")) ∧
      errorOf target.id ["Form", "Rows"]
        (.field (.direct (bare "Incompatible"))) =
          some (.ordinary (.sourceIncompatible incompatible.path target.path)) ∧
      errorOf target.id ["Form", "Rows"]
        (.field (.direct (bare "Displayed"))) =
          some (.ordinary (.sourceIncompatible displayed.path target.path)) ∧
      errorOf target.id ["Form", "Rows"]
        (.field (.direct (child "DeepSource"))) =
          some (.scopeMismatch target.path deepSource.path) ∧
      errorOf target.id ["Form", "Rows"]
        (.field (.direct (bare "Target"))) =
          some (.ordinary (.targetSelfReferenceAtDirectField target.id)) ∧
      errorOf target.id ["Form", "Rows"]
        (.field (.category (bare "Target") "Choice")) =
          some (.ordinary
            (.targetSelfReferenceAtCompatibleCategory target.id)) ∧
      targetDiagnosticOf (.field (.direct (bare "Target"))) =
        some .errorReferenceToCalculatedField ∧
      targetDiagnosticOf (.field (.category (bare "Target") "Choice")) =
        some .errorSemanticIndexOrCategoryForErrorField := by
  native_decide

/- Two physical rows retain exact target addresses and their row-local stored tokens. -/
example : (do
    let operation ← operation?
    outcomes? operation 2 [
      rowCell source 1 "A" (.parsed (.enum "A")),
      rowCell source 2 "B" (.parsed (.enum "B"))]) = some [
        (address target.id 1, .accepted ⟨"A", by decide⟩),
        (address target.id 2, .accepted ⟨"B", by decide⟩)] := by
  native_decide

/- Category projection remains row-local, while a root source and literal each fan out to every physical target row. -/
example : (do
    let operation ← projectedOperation?
    outcomes? operation 2 [
      rowCell projected 1 "X" (.parsed (.enum "X")),
      rowCell projected 2 "Y" (.parsed (.enum "Y"))]) = some [
        (address target.id 1, .accepted ⟨"A", by decide⟩),
        (address target.id 2, .accepted ⟨"B", by decide⟩)] ∧
    (do
      let operation ← rootSourceOperation?
      outcomes? operation 2 [rootCell rootSource "A" (.parsed (.enum "A"))]) =
        some [
          (address target.id 1, .accepted ⟨"A", by decide⟩),
          (address target.id 2, .accepted ⟨"A", by decide⟩)] ∧
    (do
      let operation ← literalOperation?
      outcomes? operation 2 []) = some [
        (address target.id 1, .accepted ⟨"B", by decide⟩),
        (address target.id 2, .accepted ⟨"B", by decide⟩)] := by
  native_decide

/- Source-relative unchanged classification is inert against a different destination, while the changed row applies at its own key and unrelated state survives. -/
example : (do
    let input ← document? 2 [
      rowCell target 1 "B" (.parsed (.enum "B")),
      rowCell target 2 "A" (.parsed (.enum "A")),
      rowCell source 1 "B" (.parsed (.enum "B")),
      rowCell source 2 "B" (.parsed (.enum "B"))]
    let destination ← document? 2 [
      rowCell target 1 "A" (.parsed (.enum "A")),
      rootCell other "A" (.parsed (.enum "A"))]
    resultApplicationSummary? input destination [.malformed]) = some {
      values := [
        (address target.id 1, "B"),
        (address target.id 2, "B")]
      changes := [(address target.id 2, "B")]
      errors := []
      cleared := []
      residual := [.malformed]
      row1 := .presentValue ⟨"A", by decide⟩
      row2 := .presentValue ⟨"B", by decide⟩
      unrelated := .presentValue ⟨"A", by decide⟩
    } := by
  native_decide

/- Clean absence and a formally invalid reached token both become exact retained clears, materializing absent destination cell states without claiming row topology. -/
example : (do
    let operation ← operation?
    rawOutcomes? operation 2 [
      rowCell source 2 "C" (.parsed (.enum "C"))]) = some [
        (address target.id 1, .noValue),
        (address target.id 2, .poison .declaredConstraint)] := by
  native_decide

example : (do
    let input ← document? 2 [
      rowCell target 1 "A" (.parsed (.enum "A")),
      rowCell target 2 "A" (.parsed (.enum "A")),
      rowCell source 2 "C" (.parsed (.enum "C"))]
    let destination ← document? 2 [
      rootCell other "B" (.parsed (.enum "B"))]
    resultApplicationSummary? input destination) = some {
      values := []
      changes := []
      errors := []
      cleared := [address target.id 1, address target.id 2]
      residual := []
      row1 := .presentEmpty
      row2 := .presentEmpty
      unrelated := .presentValue ⟨"B", by decide⟩
    } := by
  native_decide

example : (do
    let operation ← operation?
    outcomes? operation 0 []) = some [] := by
  native_decide

end A12Kernel.Conformance.AddressedEnumerationComputation
