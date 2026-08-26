import A12Kernel.Elaboration.AddressedEnumerationCascade

namespace A12Kernel.Conformance.AddressedEnumerationCascade

open A12Kernel

private def domain : EnumerationDeclaration := {
  storedTokens := ["A", "B"]
  categories := [{ name := "Choice", tokens := ["B", "A"] }]
}

private def enumerationField (id : FieldId) (name : String) : FlatFieldDecl := {
  id, name
  groupPath := ["Form", "Rows"]
  repeatableScope := [10]
  policy := { kind := .enumeration }
  enumeration := some domain
}

private def source := enumerationField 1 "Source"
private def produced := enumerationField 2 "Produced"
private def final := enumerationField 3 "Final"
private def deepFinal : FlatFieldDecl := {
  final with
  id := 4
  name := "DeepFinal"
  groupPath := ["Form", "Rows", "Details"]
  repeatableScope := [10, 20]
}

private def model : FlatModel := {
  fields := [source, produced, final, deepFinal]
  repeatableGroups := [
    { level := 10, path := ["Form", "Rows"], repeatability := some 3 },
    { level := 20, path := ["Form", "Rows", "Details"], repeatability := some 2 }]
}

private def bare (name : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field := name }

private def operation? (target : FlatFieldDecl) (source : FlatFieldDecl) :
    Option (CheckedAddressedEnumerationComputation model) :=
  (checkAddressedEnumerationComputation model ["Form", "Rows"] target.id
    (.field (.direct (bare source.name)))).toOption

private def categoryOperation? (target : FlatFieldDecl) (source : FlatFieldDecl) :
    Option (CheckedAddressedEnumerationComputation model) :=
  (checkAddressedEnumerationComputation model ["Form", "Rows"] target.id
    (.field (.category (bare source.name) "Choice"))).toOption

private def deepConsumer? :
    Option (CheckedAddressedEnumerationComputation model) :=
  (checkAddressedEnumerationComputation model ["Form", "Rows", "Details"]
    deepFinal.id (.field (.direct
      { base := .relative 1, groups := [], field := produced.name }))).toOption

private def deepCategoryConsumer? :
    Option (CheckedAddressedEnumerationComputation model) :=
  (checkAddressedEnumerationComputation model ["Form", "Rows", "Details"]
    deepFinal.id (.field (.category
      { base := .relative 1, groups := [], field := produced.name }
      "Choice"))).toOption

private def cascade? : Option (CheckedAddressedEnumerationCascade model) := do
  let producer ← operation? produced source
  let consumer ← operation? final produced
  (certifyAddressedEnumerationCascade producer consumer).toOption

private def deepCascade? : Option (CheckedAddressedEnumerationCascade model) := do
  let producer ← operation? produced source
  let consumer ← deepConsumer?
  (certifyAddressedEnumerationCascade producer consumer).toOption

private def categoryCascade? : Option (CheckedAddressedEnumerationCascade model) := do
  let producer ← operation? produced source
  let consumer ← categoryOperation? final produced
  (certifyAddressedEnumerationCascade producer consumer).toOption

private def deepCategoryCascade? :
    Option (CheckedAddressedEnumerationCascade model) := do
  let producer ← operation? produced source
  let consumer ← deepCategoryConsumer?
  (certifyAddressedEnumerationCascade producer consumer).toOption

private def planError? (producer? consumer? :
    Option (CheckedAddressedEnumerationComputation model)) :
    Option AddressedEnumerationCascadePlanError := do
  let producer ← producer?
  let consumer ← consumer?
  match certifyAddressedEnumerationCascade producer consumer with
  | .ok _ => none
  | .error cause => some cause

private def prepared :
    PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def address (field : FieldId) (row : Nat) : CellAddr :=
  { field, path := [row] }

private def deepAddress (field : FieldId) (outer inner : Nat) : CellAddr :=
  { field, path := [outer, inner] }

private def cell (field : FlatFieldDecl) (row : Nat)
    (stored : String) (raw : RawCell) : ClassifiedCellInput := {
  address := address field.id row, stored, raw
}

private def input? : Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := [
      { group := 10, path := [1] },
      { group := 10, path := [2] },
      { group := 10, path := [3] }]
    cells := [
      cell source 1 "A" (.parsed (.enum "A")),
      cell source 3 "C" (.parsed (.enum "C")),
      cell produced 1 "B" (.parsed (.enum "B")),
      cell produced 2 "B" (.parsed (.enum "B")),
      cell produced 3 "B" (.parsed (.enum "B"))]
  }).toOption

private def deepInput? : Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := [
      { group := 10, path := [1] },
      { group := 10, path := [2] },
      { group := 10, path := [3] },
      { group := 20, path := [1, 1] },
      { group := 20, path := [1, 2] },
      { group := 20, path := [2, 1] },
      { group := 20, path := [3, 1] }]
    cells := [
      cell source 1 "A" (.parsed (.enum "A")),
      cell source 2 "C" (.parsed (.enum "C")),
      cell produced 1 "B" (.parsed (.enum "B")),
      cell produced 2 "B" (.parsed (.enum "B")),
      cell produced 3 "B" (.parsed (.enum "B"))]
  }).toOption

private abbrev CascadeSummary :=
  List (CellAddr × TokenComputationResult) ×
    List (CellAddr × TokenComputationResult)

private def summarize? (cascade? : Option (CheckedAddressedEnumerationCascade model))
    (input? : Option (CheckedDocument model)) : Option CascadeSummary := do
  let cascade ← cascade?
  let input ← input?
  let outcomes ← cascade.execute input |>.toOption
  pure (
    outcomes.producer.map fun entry => (entry.targetField, entry.result),
    outcomes.consumer.map fun entry => (entry.targetField, entry.result))

private def summary? := summarize? cascade? input?
private def categorySummary? := summarize? categoryCascade? input?
private def deepSummary? := summarize? deepCascade? deepInput?
private def deepCategorySummary? := summarize? deepCategoryCascade? deepInput?

example : cascade?.isSome = true ∧ deepCascade?.isSome = true ∧
    categoryCascade?.isSome = true ∧ deepCategoryCascade?.isSome = true ∧
    planError? (operation? produced final) (operation? final produced) =
      some .producerReadsConsumer ∧
    planError? (operation? produced source) (operation? final source) =
      some .consumerDoesNotReadProducer := by
  native_decide

/- Validation-scoped required poison remains a structural dependency-conversion fault rather than being mislabeled as a reached computed dependency. -/
example : EnumerationDependencyCell.ofResult (.poison .required) = .error .validationScopedRequired := by
  rfl

/- Every producer row completes before the consumer reads the exact-address overlay. Stale source-document values cannot leak through; invalidity becomes cause-blind dependency poison. -/
example : summary? = some ([
    (address produced.id 1, .value "A"),
    (address produced.id 2, .noValue),
    (address produced.id 3, .poison .declaredConstraint)
  ], [
    (address final.id 1, .value "A"),
    (address final.id 2, .noValue),
    (address final.id 3, .poison .computedDependency)
  ]) := by
  native_decide

/- A non-identity category mapping is applied to the completed producer token rather than to the stale stored producer cell. -/
example : categorySummary? = some ([
    (address produced.id 1, .value "A"),
    (address produced.id 2, .noValue),
    (address produced.id 3, .poison .declaredConstraint)
  ], [
    (address final.id 1, .value "B"),
    (address final.id 2, .noValue),
    (address final.id 3, .poison .computedDependency)
  ]) := by
  native_decide

/- One completed enclosing producer row fans out only to its own descendant targets; stale parent cells cannot leak through clean absence or dependency poison. -/
example : deepSummary? = some ([
    (address produced.id 1, .value "A"),
    (address produced.id 2, .poison .declaredConstraint),
    (address produced.id 3, .noValue)
  ], [
    (deepAddress deepFinal.id 1 1, .value "A"),
    (deepAddress deepFinal.id 1 2, .value "A"),
    (deepAddress deepFinal.id 2 1, .poison .computedDependency),
    (deepAddress deepFinal.id 3 1, .noValue)
  ]) ∧ deepCategorySummary? = some ([
    (address produced.id 1, .value "A"),
    (address produced.id 2, .poison .declaredConstraint),
    (address produced.id 3, .noValue)
  ], [
    (deepAddress deepFinal.id 1 1, .value "B"),
    (deepAddress deepFinal.id 1 2, .value "B"),
    (deepAddress deepFinal.id 2 1, .poison .computedDependency),
    (deepAddress deepFinal.id 3 1, .noValue)
  ]) := by
  native_decide

end A12Kernel.Conformance.AddressedEnumerationCascade
