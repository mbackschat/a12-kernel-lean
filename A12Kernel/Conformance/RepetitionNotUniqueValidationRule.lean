import A12Kernel.Elaboration.ValidationRule

/-!
# Checked repetition-not-unique whole-rule conformance locks

This family remains independently buildable with `lake build A12Kernel.Conformance.RepetitionNotUniqueValidationRule`; the conformance root is only its full-suite umbrella.
-/

namespace A12Kernel.Conformance.RepetitionNotUniqueValidationRule

open A12Kernel

private def count : FlatFieldDecl :=
  { id := 100
    groupPath := ["Order", "Items"]
    name := "Count"
    policy := { kind := .number { scale := 0, signed := false } }
    repeatableScope := [10] }

private def weight : FlatFieldDecl :=
  { count with id := 101, name := "Weight" }

private def insideNote : FlatFieldDecl :=
  { count with
    id := 102
    name := "InsideNote"
    policy := { kind := .string } }

private def descendantNote : FlatFieldDecl :=
  { insideNote with
    id := 103
    groupPath := ["Order", "Items", "Details"]
    name := "DescendantNote" }

private def parentNote : FlatFieldDecl :=
  { insideNote with
    id := 104
    groupPath := ["Order"]
    name := "ParentNote"
    repeatableScope := [] }

private def model : FlatModel :=
  { fields := [count, weight, insideNote, descendantNote, parentNote]
    repeatableGroups := [{
      level := 10
      path := ["Order", "Items"]
      repeatability := some 3 }] }

private def world : World :=
  { now := { epochMillis := 0 } }

private def field (name : String) : SurfaceFieldPath :=
  { base := .absolute, groups := ["Order", "Items"], field := name }

private def source (restKeys : List SurfaceFieldPath := []) :
    SurfaceRepetitionNotUniqueSource :=
  { firstKey := field "Count", restKeys }

private def authoredFromSource : SurfaceRepetitionNotUniqueSource :=
  { source with
    scope := .from (.path {
      base := .absolute
      groups := ["Order", "Items"] }) }

private def checkedConditionFrom?
    (authored : SurfaceRepetitionNotUniqueSource)
    (restKeys : List SurfaceFieldPath := []) :
    Option (CheckedValidationCondition model) :=
  (CheckedValidationCondition.fromRepetitionNotUnique
    model ["Order"] { authored with restKeys }).toOption

private def checkedCondition? (restKeys : List SurfaceFieldPath := []) :
    Option (CheckedValidationCondition model) :=
  checkedConditionFrom? source restKeys

private def filledWeightCondition? :
    Option (CheckedValidationCondition model) :=
  (CheckedValidationCondition.fromRepeatableFieldPresence
    model ["Order"] .filled (field "Weight")).toOption

private def assembleRule?
    (combine : CheckedValidationCondition model →
      CheckedValidationCondition model →
        Except ValidationConditionAssemblyError
          (CheckedValidationCondition model))
    (restKeys : List SurfaceFieldPath := []) :
    Option (CheckedResolvedValidationRule model) := do
  let rnu ← checkedCondition? restKeys
  let filledWeight ← filledWeightCondition?
  let condition ← (combine rnu filledWeight).toOption
  (assembleResolvedValidationRule model condition count.id
    "rnu" .error { parts := [] }).toOption

private def rnuOrWeightRule? :
    Option (CheckedResolvedValidationRule model) :=
  assembleRule? CheckedValidationCondition.or

private def weightAndRnuRule? :
    Option (CheckedResolvedValidationRule model) :=
  assembleRule? (fun rnu filledWeight => filledWeight.and rnu)

private def compositeRnuRule? :
    Option (CheckedResolvedValidationRule model) := do
  let condition ← checkedCondition? [field "Weight"]
  (assembleResolvedValidationRule model condition count.id
    "rnu" .error { parts := [] }).toOption

private def compositeRnuOrCountRule? :
    Option (CheckedResolvedValidationRule model) := do
  let rnu ← checkedCondition? [field "Weight"]
  let filledCount ←
    (CheckedValidationCondition.fromRepeatableFieldPresence
      model ["Order"] .filled (field "Count")).toOption
  let condition ← (rnu.or filledCount).toOption
  (assembleResolvedValidationRule model condition count.id
    "rnu" .error { parts := [] }).toOption

private def referenceRuleAdmitted?
    (authored : SurfaceRepetitionNotUniqueSource)
    (errorField : FieldId) : Bool :=
  match checkedConditionFrom? authored with
  | none => false
  | some condition =>
      (assembleResolvedValidationRule model condition errorField
        "rnu" .error { parts := [] }).isOk

private def referenceBoundary? :
    Option (Bool × Bool × Bool × Bool × Bool × Bool) := do
  let explicit ← checkedConditionFrom? authoredFromSource
  let inferred ← checkedConditionFrom? source
  pure (
    explicit.core.referencesField insideNote.id,
    explicit.core.referencesField descendantNote.id,
    explicit.core.referencesField parentNote.id,
    inferred.core.referencesField insideNote.id,
    inferred.core.referencesField descendantNote.id,
    inferred.core.referencesField parentNote.id)

private def cell (fieldId : FieldId) (row : Nat)
    (stored : String) (value : Nat) : ClassifiedCellInput :=
  { address := { field := fieldId, path := [row] }
    stored
    raw := .parsed (.num value) }

private def rnuOrWeightData : DocumentData :=
  { instantiatedRows := [
      { group := 10, path := [1] },
      { group := 10, path := [2] },
      { group := 10, path := [3] }]
    cells := [
      cell count.id 1 "5" 5,
      cell count.id 2 "5" 5,
      cell count.id 3 "9" 9,
      cell weight.id 3 "200" 200] }

private def guardedRnuData : DocumentData :=
  { instantiatedRows := [
      { group := 10, path := [1] },
      { group := 10, path := [2] }]
    cells := [
      cell count.id 1 "5" 5,
      cell count.id 2 "5" 5,
      cell weight.id 1 "1" 1] }

private def compositeRnuData : DocumentData :=
  { instantiatedRows := [
      { group := 10, path := [1] },
      { group := 10, path := [2] }]
    cells := [
      cell count.id 1 "5" 5,
      cell count.id 2 "5" 5] }

private def checkedDocument? (data : DocumentData) :
    Option (CheckedDocument model) := do
  let prepared ←
    (prepareFlatStringContext world builtinStringPatternCompiler
      model).toOption
  (checkDocument prepared "en_US" data).toOption

private def evalRule?
    (rule : CheckedResolvedValidationRule model)
    (data : DocumentData) :
    Option (List (Env × FlatRuleOutcome)) := do
  let document ← checkedDocument? data
  (rule.evalOrdinaryRepeatableFull document).toOption

private def verdicts?
    (rule : Option (CheckedResolvedValidationRule model))
    (data : DocumentData) : Option (List (Env × Verdict)) := do
  let checked ← rule
  let outcomes ← evalRule? checked data
  pure (outcomes.map fun entry => (entry.1, entry.2.verdict))

private def partialVerdicts?
    (rule : Option (CheckedResolvedValidationRule model))
    (data : DocumentData) (scope : ValidationRelevanceScope) :
    Option (List (Env × Option Verdict)) := do
  let checkedRule ← rule
  let document ← checkedDocument? data
  let outcome ←
    (checkedRule.evalOrdinaryRepeatablePartial document scope).toOption
  match outcome with
  | .skipped => none
  | .evaluated rows =>
      pure (rows.map fun row =>
        (row.1, match row.2 with
          | .skipped => none
          | .evaluated result => some result.verdict))

private def allCompositeKeysRelevant : ValidationRelevanceScope :=
  .partialSet [
    RelevantEntityPattern.allInstances count.path,
    RelevantEntityPattern.allInstances weight.path
  ]

private def countOnlyRelevant : ValidationRelevanceScope :=
  .partialSet [RelevantEntityPattern.allInstances count.path]

private def firstCompositeKeyRelevant : ValidationRelevanceScope :=
  .partialSet [
    { path := count.path, indices := [.all, .concrete 1, .all] },
    { path := weight.path, indices := [.all, .concrete 1, .all] }
  ]

private def multipleRnuError? : Option ValidationConditionAssemblyError := do
  let first ← checkedCondition?
  let second ← checkedCondition?
  match first.and second with
  | .ok _ => none
  | .error error => some error

private def missingPreparedResultError? :
    Option CheckedAddressingError := do
  let condition ← checkedCondition?
  let document ← checkedDocument? rnuOrWeightData
  let context : AddressedValidationEvaluationContext model := {
    scalar := {
      fields := document.flatContext
      groups := GroupPresenceContext.unavailable
    }
    outer := [(10, 1)]
    input := .checked document
  }
  match condition.core.evalAddressed context with
  | .ok _ => none
  | .error error => some error

private def consumerKeyIds? : Option (List FieldId) := do
  let condition ← checkedCondition?
  let source ← condition.core.repetitionNotUniqueSource?
  pure (source.keys.map (·.fieldId))

private def consumerResults? :
    Option (List RepetitionNotUniqueResult) := do
  let condition ← checkedCondition?
  let source ← condition.core.repetitionNotUniqueSource?
  let document ← checkedDocument? guardedRnuData
  (source.evaluateChecked document [] .full).toOption

private def phase : FlatFieldDecl :=
  { id := 200
    groupPath := ["Project", "Milestones"]
    name := "Phase"
    policy := { kind := .number { scale := 0, signed := false } }
    repeatableScope := [20] }

private def effort : FlatFieldDecl :=
  { id := 201
    groupPath := ["Project", "Milestones", "Tasks"]
    name := "Effort"
    policy := { kind := .number { scale := 0, signed := false } }
    repeatableScope := [20, 30] }

private def nestedModel : FlatModel :=
  { fields := [phase, effort]
    repeatableGroups := [
      { level := 20
        path := ["Project", "Milestones"]
        repeatability := some 2 },
      { level := 30
        path := ["Project", "Milestones", "Tasks"]
        repeatability := some 2 }
    ] }

private def nestedPath (groups : GroupPath) (field : String) :
    SurfaceFieldPath :=
  { base := .absolute, groups, field }

private def nestedEffortPath : SurfaceFieldPath :=
  nestedPath ["Project", "Milestones", "Tasks"] "Effort"

private def nestedPhasePath : SurfaceFieldPath :=
  nestedPath ["Project", "Milestones"] "Phase"

private def nestedSource
    (scope : SurfaceRepetitionNotUniqueScope := .default)
    (withPhase : Bool := false) : SurfaceRepetitionNotUniqueSource :=
  if withPhase then
    { firstKey := nestedPhasePath
      restKeys := [nestedEffortPath]
      scope }
  else
    { firstKey := nestedEffortPath, restKeys := [], scope }

private def nestedFrom (groups : GroupPath) :
    SurfaceRepetitionNotUniqueScope :=
  .from (.path { base := .absolute, groups })

private def nestedRule?
    (scope : SurfaceRepetitionNotUniqueScope := .default)
    (withPhase : Bool := false) :
    Option (CheckedResolvedValidationRule nestedModel) := do
  let condition ←
    (CheckedValidationCondition.fromRepetitionNotUnique
      nestedModel ["Project"] (nestedSource scope withPhase)).toOption
  (assembleResolvedValidationRule nestedModel condition effort.id
    "nestedRnu" .error { parts := [] }).toOption

private def nestedCell (field : FieldId) (path : List Nat)
    (stored : String) (value : Nat) : ClassifiedCellInput :=
  { address := { field, path }, stored, raw := .parsed (.num value) }

private def nestedData (withinFirstMilestone : Bool := false) :
    DocumentData :=
  { instantiatedRows := [
      { group := 20, path := [2] },
      { group := 20, path := [1] },
      { group := 30, path := [2, 2] },
      { group := 30, path := [1, 2] },
      { group := 30, path := [2, 1] },
      { group := 30, path := [1, 1] }
    ]
    cells := [
      nestedCell phase.id [1] "1" 1,
      nestedCell phase.id [2] "2" 2,
      nestedCell effort.id [2, 2] "9" 9,
      nestedCell effort.id [1, 2] (if withinFirstMilestone then "5" else "7")
        (if withinFirstMilestone then 5 else 7),
      nestedCell effort.id [2, 1] (if withinFirstMilestone then "7" else "5")
        (if withinFirstMilestone then 7 else 5),
      nestedCell effort.id [1, 1] "5" 5
    ] }

private def nestedCheckedDocument? (data : DocumentData) :
    Option (CheckedDocument nestedModel) := do
  let prepared ←
    (prepareFlatStringContext world builtinStringPatternCompiler
      nestedModel).toOption
  (checkDocument prepared "en_US" data).toOption

private def nestedVerdicts?
    (rule : Option (CheckedResolvedValidationRule nestedModel))
    (data : DocumentData) : Option (List (Env × Verdict)) := do
  let checkedRule ← rule
  let document ← nestedCheckedDocument? data
  let outcomes ← (checkedRule.evalOrdinaryRepeatableFull document).toOption
  pure (outcomes.map fun outcome => (outcome.1, outcome.2.verdict))

private def nestedPartialVerdicts?
    (rule : Option (CheckedResolvedValidationRule nestedModel))
    (data : DocumentData) (scope : ValidationRelevanceScope) :
    Option (List (Env × Option Verdict)) := do
  let checkedRule ← rule
  let document ← nestedCheckedDocument? data
  let outcome ←
    (checkedRule.evalOrdinaryRepeatablePartial document scope).toOption
  match outcome with
  | .skipped => none
  | .evaluated rows =>
      pure (rows.map fun row =>
        (row.1, match row.2 with
          | .skipped => none
          | .evaluated result => some result.verdict))

private def nestedMissingOuterError? :
    Option CheckedAddressingError := do
  let condition ←
    (CheckedValidationCondition.fromRepetitionNotUnique
      nestedModel ["Project"]
      (nestedSource
        (nestedFrom ["Project", "Milestones", "Tasks"]))).toOption
  let source ← condition.core.repetitionNotUniqueSource?
  let document ← nestedCheckedDocument? (nestedData)
  match source.evaluateChecked document [] .full with
  | .ok _ => none
  | .error error => some error

private def allNestedEffortRelevant : ValidationRelevanceScope :=
  .partialSet [RelevantEntityPattern.allInstances effort.path]

private def firstNestedEffortRelevant : ValidationRelevanceScope :=
  .partialSet [{
    path := effort.path
    indices := [.all, .concrete 1, .concrete 1, .all]
  }]

/- RNU remains one ordinary row leaf: duplicate rows fire through it, while an independent positive branch can fire the unique row. -/
example :
    verdicts? rnuOrWeightRule? rnuOrWeightData =
      some [
        ([(10, 1)], .fired .value),
        ([(10, 2)], .fired .value),
        ([(10, 3)], .fired .value)] := by
  native_decide

/- Duplicate construction is branch-independent: the guard-false peer still makes the guard-true row a duplicate. -/
example :
    verdicts? weightAndRnuRule? guardedRnuData =
      some [
        ([(10, 1)], .fired .value),
        ([(10, 2)], .notFired)] := by
  native_decide

/- Optional empty composite components participate in equality and retain OMISSION through whole-rule emission. -/
example :
    verdicts? compositeRnuRule? compositeRnuData =
      some [
        ([(10, 1)], .fired .omission),
        ([(10, 2)], .fired .omission)] := by
  native_decide

/- Every composite-key component must be relevant before a row joins the duplicate relation. Complete relevance fires both omission-valued duplicates; count-only relevance admits both error instances but leaves the RNU leaf UNKNOWN. -/
example :
    partialVerdicts? compositeRnuRule? compositeRnuData
        allCompositeKeysRelevant =
      some [
        ([(10, 1)], some (.fired .omission)),
        ([(10, 2)], some (.fired .omission))] ∧
    partialVerdicts? compositeRnuRule? compositeRnuData
        countOnlyRelevant =
      some [
        ([(10, 1)], some .unknown),
        ([(10, 2)], some .unknown)] := by
  native_decide

/- A sole relevant composite row cannot duplicate an excluded peer. The same count-only split still permits an independent relevant positive branch to decide `Or`. -/
example :
    partialVerdicts? compositeRnuRule? compositeRnuData
        firstCompositeKeyRelevant =
      some [
        ([(10, 1)], some .notFired),
        ([(10, 2)], none)] ∧
    partialVerdicts? compositeRnuOrCountRule? compositeRnuData
        countOnlyRelevant =
      some [
        ([(10, 1)], some (.fired .value)),
        ([(10, 2)], some (.fired .value))] := by
  native_decide

/- The checked condition rejects a second RNU leaf before runtime composition. -/
example :
    multipleRnuError? =
      some .multipleRepetitionNotUnique := by
  native_decide

/- Calling the generic addressed evaluator without the rule-owned RNU result is a structural execution failure, never semantic UNKNOWN. -/
example :
    missingPreparedResultError? =
      some (.repetitionNotUniqueResult [(10, 1)]) := by
  native_decide

/- Execute/Transform/Explain consumers recover the checked key identity and branch-independent peer cluster from the same source used by the row evaluator. -/
example :
    consumerKeyIds? = some [count.id] := by
  native_decide

example :
    consumerResults?.map (List.map fun result => result.verdict) =
      some [.fired .value, .fired .value] := by
  native_decide

example :
    consumerResults?.map (List.map fun result => result.cluster) =
      some [
        [[(10, 1)], [(10, 2)]],
        [[(10, 1)], [(10, 2)]]] := by
  native_decide

/- An authored `@From` contributes its resolved group subtree to the whole-rule error-field gate; selecting the same group by default does not manufacture that authored reference. -/
example :
    referenceRuleAdmitted? authoredFromSource insideNote.id = true ∧
      referenceRuleAdmitted? authoredFromSource descendantNote.id = true ∧
      referenceRuleAdmitted? authoredFromSource parentNote.id = false ∧
      referenceRuleAdmitted? source insideNote.id = false ∧
      referenceRuleAdmitted? source descendantNote.id = false ∧
      referenceRuleAdmitted? source parentNote.id = false := by
  native_decide

/- The checked reference query itself excludes the parent; the parent rule also has an independent row-scope mismatch. -/
example :
    referenceBoundary? =
      some (true, true, false, false, false, false) := by
  native_decide

/- Default scope and explicit `@From Milestones` compare equal task keys across parents. Rule outcomes retain the deepest-row encounter order even though duplicate construction uses canonical topology order. -/
example :
    nestedVerdicts? (nestedRule?) (nestedData) =
      some [
        ([(20, 2), (30, 2)], .notFired),
        ([(20, 1), (30, 2)], .notFired),
        ([(20, 2), (30, 1)], .fired .value),
        ([(20, 1), (30, 1)], .fired .value)
      ] ∧
    nestedVerdicts?
        (nestedRule? (nestedFrom ["Project", "Milestones"]))
        (nestedData) =
      some [
        ([(20, 2), (30, 2)], .notFired),
        ([(20, 1), (30, 2)], .notFired),
        ([(20, 2), (30, 1)], .fired .value),
        ([(20, 1), (30, 1)], .fired .value)
      ] := by
  native_decide

/- Explicit `@From Tasks` partitions the same relation by the bound milestone: cross-parent equals stay unique, while an equal pair under one milestone fires. -/
example :
    nestedVerdicts?
        (nestedRule? (nestedFrom ["Project", "Milestones", "Tasks"]))
        (nestedData) =
      some [
        ([(20, 2), (30, 2)], .notFired),
        ([(20, 1), (30, 2)], .notFired),
        ([(20, 2), (30, 1)], .notFired),
        ([(20, 1), (30, 1)], .notFired)
      ] ∧
    nestedVerdicts?
        (nestedRule? (nestedFrom ["Project", "Milestones", "Tasks"]))
        (nestedData true) =
      some [
        ([(20, 2), (30, 2)], .notFired),
        ([(20, 1), (30, 2)], .fired .value),
        ([(20, 2), (30, 1)], .notFired),
        ([(20, 1), (30, 1)], .fired .value)
      ] := by
  native_decide

/- An ancestor component is projected through its own one-level address before joining the deepest composite key. Distinct milestone phases therefore separate equal efforts. -/
example :
    nestedVerdicts? (nestedRule? (withPhase := true)) (nestedData) =
      some [
        ([(20, 2), (30, 2)], .notFired),
        ([(20, 1), (30, 2)], .notFired),
        ([(20, 2), (30, 1)], .notFired),
        ([(20, 1), (30, 1)], .notFired)
      ] := by
  native_decide

/- A narrow reference scope cannot be evaluated without its exact parent binding; the failure remains structural. -/
example :
    nestedMissingOuterError? =
      some (.addressing (.missingBinding 20)) := by
  native_decide

/- Nested partial execution keeps topology separate from relevance. Complete key relevance preserves cross-parent duplicates; one concrete relevant error/key row is evaluated as unique while every other actual row skips. -/
example :
    nestedPartialVerdicts? (nestedRule?) (nestedData)
        allNestedEffortRelevant =
      some [
        ([(20, 2), (30, 2)], some .notFired),
        ([(20, 1), (30, 2)], some .notFired),
        ([(20, 2), (30, 1)], some (.fired .value)),
        ([(20, 1), (30, 1)], some (.fired .value))
      ] ∧
    nestedPartialVerdicts? (nestedRule?) (nestedData)
        firstNestedEffortRelevant =
      some [
        ([(20, 2), (30, 2)], none),
        ([(20, 1), (30, 2)], none),
        ([(20, 2), (30, 1)], none),
        ([(20, 1), (30, 1)], some .notFired)
      ] := by
  native_decide

/- Partial `@From Tasks` retains the authored parent partition when every task key is relevant; relevance changes row admission, not relation scope. -/
example :
    nestedPartialVerdicts?
        (nestedRule? (nestedFrom ["Project", "Milestones", "Tasks"]))
        (nestedData) allNestedEffortRelevant =
      some [
        ([(20, 2), (30, 2)], some .notFired),
        ([(20, 1), (30, 2)], some .notFired),
        ([(20, 2), (30, 1)], some .notFired),
        ([(20, 1), (30, 1)], some .notFired)
      ] := by
  native_decide

/- Relevance is component-wise at each key's own depth: relevant task error instances with a nonrelevant ancestor component evaluate RNU as UNKNOWN. -/
example :
    nestedPartialVerdicts? (nestedRule? (withPhase := true)) (nestedData)
        allNestedEffortRelevant =
      some [
        ([(20, 2), (30, 2)], some .unknown),
        ([(20, 1), (30, 2)], some .unknown),
        ([(20, 2), (30, 1)], some .unknown),
        ([(20, 1), (30, 1)], some .unknown)
      ] := by
  native_decide

end A12Kernel.Conformance.RepetitionNotUniqueValidationRule
