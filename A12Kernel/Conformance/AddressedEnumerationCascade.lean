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
private def terminal := enumerationField 5 "Terminal"
private def deepFinal : FlatFieldDecl := {
  final with
  id := 4
  name := "DeepFinal"
  groupPath := ["Form", "Rows", "Details"]
  repeatableScope := [10, 20]
}

private def model : FlatModel := {
  fields := [source, produced, final, deepFinal, terminal]
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

private def threeStageCascade? :
    Option (CheckedAddressedEnumerationThreeStageCascade model) := do
  let first ← operation? produced source
  let second ← categoryOperation? final produced
  let third ← operation? terminal final
  (certifyAddressedEnumerationThreeStageCascade first second third).toOption

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

private structure PhaseResultSummary where
  producerValues : List (CellAddr × String)
  producerChanges : List (CellAddr × String)
  producerErrors : List CellAddr
  producerCleared : List CellAddr
  producerResidual : List FormalCause
  consumerValues : List (CellAddr × String)
  consumerChanges : List (CellAddr × String)
  consumerErrors : List CellAddr
  consumerCleared : List CellAddr
  consumerResidual : List FormalCause
  deriving Repr, DecidableEq

private def categoryResultSummary? : Option PhaseResultSummary := do
  let cascade ← categoryCascade?
  let input ← input?
  let view ← cascade.executeResult input [.malformed] [.required] |>.toOption
  pure {
    producerValues := view.producer.withoutErrors.map fun entry =>
      (entry.targetField, entry.value.text)
    producerChanges := view.producer.withChanges.map fun entry =>
      (entry.targetField, entry.value.text)
    producerErrors := view.producer.withErrors.map (·.targetField)
    producerCleared := view.producer.cleared
    producerResidual := view.producer.formalErrorsInOperands
    consumerValues := view.consumer.withoutErrors.map fun entry =>
      (entry.targetField, entry.value.text)
    consumerChanges := view.consumer.withChanges.map fun entry =>
      (entry.targetField, entry.value.text)
    consumerErrors := view.consumer.withErrors.map (·.targetField)
    consumerCleared := view.consumer.cleared
    consumerResidual := view.consumer.formalErrorsInOperands
  }

private structure CascadeApplicationSummary where
  produced1 : StringTargetState
  produced2 : StringTargetState
  produced3 : StringTargetState
  final1 : StringTargetState
  final2 : StringTargetState
  source1 : StringTargetState
  deriving Repr, DecidableEq

private def applicationSummary? : Option CascadeApplicationSummary := do
  let cascade ← categoryCascade?
  let input ← input?
  let view ← cascade.executeResult input
    ([] : List FormalCause) ([] : List FormalCause) |>.toOption
  let destination ← (checkDocument prepared "en_US" {
    instantiatedRows := [
      { group := 10, path := [1] },
      { group := 10, path := [2] },
      { group := 10, path := [3] }]
    cells := [
      cell produced 1 "B" (.parsed (.enum "B")),
      cell produced 2 "A" (.parsed (.enum "A")),
      cell final 1 "A" (.parsed (.enum "A")),
      cell final 2 "A" (.parsed (.enum "A")),
      cell source 1 "B" (.parsed (.enum "B"))]
  }).toOption
  let applied ← view.applyToChecked destination |>.toOption
  pure {
    produced1 := applied (address produced.id 1)
    produced2 := applied (address produced.id 2)
    produced3 := applied (address produced.id 3)
    final1 := applied (address final.id 1)
    final2 := applied (address final.id 2)
    source1 := applied (address source.id 1)
  }

private def threeStageError?
    (first? second? third? :
      Option (CheckedAddressedEnumerationComputation model)) :
    Option AddressedEnumerationThreeStageCascadePlanError := do
  let first ← first?
  let second ← second?
  let third ← third?
  match certifyAddressedEnumerationThreeStageCascade first second third with
  | .ok _ => none
  | .error cause => some cause

private def threeStageInput? : Option (CheckedDocument model) :=
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
      cell produced 3 "B" (.parsed (.enum "B")),
      cell final 1 "A" (.parsed (.enum "A")),
      cell final 2 "A" (.parsed (.enum "A")),
      cell final 3 "A" (.parsed (.enum "A")),
      cell terminal 1 "B" (.parsed (.enum "B")),
      cell terminal 2 "A" (.parsed (.enum "A")),
      cell terminal 3 "A" (.parsed (.enum "A"))]
  }).toOption

private structure ThreeStageExecutionSummary where
  analysis : AddressedEnumerationThreeStageCascadeAnalysis
  first : List (CellAddr × TokenComputationResult)
  second : List (CellAddr × TokenComputationResult)
  third : List (CellAddr × TokenComputationResult)
  deriving Repr, DecidableEq

private def threeStageExecutionSummary? : Option ThreeStageExecutionSummary := do
  let plan ← threeStageCascade?
  let input ← threeStageInput?
  let outcomes ← plan.execute input |>.toOption
  pure {
    analysis := plan.analyze
    first := outcomes.first.map fun item => (item.targetField, item.result)
    second := outcomes.second.map fun item => (item.targetField, item.result)
    third := outcomes.third.map fun item => (item.targetField, item.result)
  }

private structure ThreeStageResultApplicationSummary where
  firstValues : List (CellAddr × String)
  firstChanges : List (CellAddr × String)
  firstCleared : List CellAddr
  firstResidual : List Nat
  secondValues : List (CellAddr × String)
  secondChanges : List (CellAddr × String)
  secondCleared : List CellAddr
  secondResidual : List Nat
  thirdValues : List (CellAddr × String)
  thirdChanges : List (CellAddr × String)
  thirdCleared : List CellAddr
  thirdResidual : List Nat
  applied : List (CellAddr × StringTargetState)
  deriving Repr, DecidableEq

private def threeStageDestination? : Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := [
      { group := 10, path := [1] },
      { group := 10, path := [2] },
      { group := 10, path := [3] }]
    cells := [
      cell produced 1 "B" (.parsed (.enum "B")),
      cell final 1 "A" (.parsed (.enum "A")),
      cell terminal 1 "A" (.parsed (.enum "A")),
      cell source 1 "B" (.parsed (.enum "B"))]
  }).toOption

private def threeStageResultApplicationSummary? :
    Option ThreeStageResultApplicationSummary := do
  let plan ← threeStageCascade?
  let input ← threeStageInput?
  let destination ← threeStageDestination?
  let view ← plan.executeResult input [11] [22] [33] |>.toOption
  let applied ← view.applyToChecked destination |>.toOption
  let addresses := [
    address produced.id 1, address final.id 1, address terminal.id 1,
    address produced.id 2, address final.id 2, address terminal.id 2,
    address source.id 1]
  pure {
    firstValues := view.first.withoutErrors.map fun item =>
      (item.targetField, item.value.text)
    firstChanges := view.first.withChanges.map fun item =>
      (item.targetField, item.value.text)
    firstCleared := view.first.cleared
    firstResidual := view.first.formalErrorsInOperands
    secondValues := view.second.withoutErrors.map fun item =>
      (item.targetField, item.value.text)
    secondChanges := view.second.withChanges.map fun item =>
      (item.targetField, item.value.text)
    secondCleared := view.second.cleared
    secondResidual := view.second.formalErrorsInOperands
    thirdValues := view.third.withoutErrors.map fun item =>
      (item.targetField, item.value.text)
    thirdChanges := view.third.withChanges.map fun item =>
      (item.targetField, item.value.text)
    thirdCleared := view.third.cleared
    thirdResidual := view.third.formalErrorsInOperands
    applied := addresses.map fun item => (item, applied item)
  }

example : cascade?.isSome = true ∧ deepCascade?.isSome = true ∧
    categoryCascade?.isSome = true ∧ deepCategoryCascade?.isSome = true ∧
    planError? (operation? produced final) (operation? final produced) =
      some .producerReadsConsumer ∧
    planError? (operation? produced source) (operation? final source) =
      some .consumerDoesNotReadProducer := by
  native_decide

example : threeStageCascade?.isSome = true ∧
    threeStageError? (operation? produced final) (operation? final produced)
      (operation? terminal final) =
        some (.firstToSecond .producerReadsConsumer) ∧
    threeStageError? (operation? produced source) (operation? final source)
      (operation? terminal final) =
        some (.firstToSecond .consumerDoesNotReadProducer) ∧
    threeStageError? (operation? produced source) (operation? final produced)
      (operation? produced final) = some .firstAndThirdTargetsSame ∧
    threeStageError? (operation? produced terminal) (operation? final produced)
      (operation? terminal final) = some .firstReadsThird ∧
    threeStageError? (operation? produced source) (operation? final produced)
      (operation? terminal source) =
        some .thirdDoesNotReadSecond := by
  native_decide

/- Fresh phase overlays beat contradictory stored target cells at both edges; clean absence stays clean, while poison becomes cause-blind and remains poison across the second edge. -/
example : threeStageExecutionSummary? = some {
  analysis := {
    targetFields := [produced.id, final.id, terminal.id]
    fieldDependencies := [
      (produced.id, [source.id]),
      (final.id, [produced.id]),
      (terminal.id, [final.id])]
  }
  first := [
    (address produced.id 1, .value "A"),
    (address produced.id 2, .noValue),
    (address produced.id 3, .poison .declaredConstraint)]
  second := [
    (address final.id 1, .value "B"),
    (address final.id 2, .noValue),
    (address final.id 3, .poison .computedDependency)]
  third := [
    (address terminal.id 1, .value "B"),
    (address terminal.id 2, .noValue),
    (address terminal.id 3, .poison .computedDependency)]
} := by
  native_decide

/- Result phases retain their own messages and source-relative actions; the third source-identical value remains inert against a differing destination. -/
example : threeStageResultApplicationSummary? = some {
  firstValues := [(address produced.id 1, "A")]
  firstChanges := [(address produced.id 1, "A")]
  firstCleared := [address produced.id 2, address produced.id 3]
  firstResidual := [11]
  secondValues := [(address final.id 1, "B")]
  secondChanges := [(address final.id 1, "B")]
  secondCleared := [address final.id 2, address final.id 3]
  secondResidual := [22]
  thirdValues := [(address terminal.id 1, "B")]
  thirdChanges := []
  thirdCleared := [address terminal.id 2, address terminal.id 3]
  thirdResidual := [33]
  applied := [
    (address produced.id 1, .presentValue ⟨"A", by decide⟩),
    (address final.id 1, .presentValue ⟨"B", by decide⟩),
    (address terminal.id 1, .presentValue ⟨"A", by decide⟩),
    (address produced.id 2, .presentEmpty),
    (address final.id 2, .presentEmpty),
    (address terminal.id 2, .presentEmpty),
    (address source.id 1, .presentValue ⟨"B", by decide⟩)]
} := by
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

/- The two completed phases project separately against immutable source-target state without re-executing the consumer from stale input. -/
example : categoryResultSummary? = some {
    producerValues := [(address produced.id 1, "A")]
    producerChanges := [(address produced.id 1, "A")]
    producerErrors := []
    producerCleared := [address produced.id 2, address produced.id 3]
    producerResidual := [.malformed]
    consumerValues := [(address final.id 1, "B")]
    consumerChanges := [(address final.id 1, "B")]
    consumerErrors := []
    consumerCleared := []
    consumerResidual := [.required]
  } := by
  native_decide

/- Producer and consumer actions fold onto one separate destination while inert and unrelated cells survive and a retained clear can materialize absent state. -/
example : applicationSummary? = some {
    produced1 := .presentValue ⟨"A", by decide⟩
    produced2 := .presentEmpty
    produced3 := .presentEmpty
    final1 := .presentValue ⟨"B", by decide⟩
    final2 := .presentValue ⟨"A", by decide⟩
    source1 := .presentValue ⟨"B", by decide⟩
  } := by
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
