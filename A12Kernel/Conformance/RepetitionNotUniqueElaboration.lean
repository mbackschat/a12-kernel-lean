import A12Kernel.Elaboration.RepetitionNotUnique

/-! # Checked nested Number `RepetitionNotUnique` locks -/

namespace A12Kernel.Conformance.RepetitionNotUniqueElaboration

open A12Kernel

private def effort : FlatFieldDecl :=
  { id := 1
    groupPath := ["Project", "Milestones", "Tasks"]
    name := "Effort"
    policy := { kind := .number { scale := 0, signed := false } }
    repeatableScope := [10, 20] }

private def estimate : FlatFieldDecl :=
  { effort with id := 2, name := "Estimate" }

private def text : FlatFieldDecl :=
  { effort with id := 3, name := "Text", policy := { kind := .string } }

private def phase : FlatFieldDecl :=
  { id := 4
    groupPath := ["Project", "Milestones"]
    name := "Phase"
    policy := { kind := .number { scale := 0, signed := false } }
    repeatableScope := [10] }

private def model : FlatModel :=
  { fields := [effort, estimate, text, phase]
    repeatableGroups := [
      { level := 20, path := ["Project", "Milestones", "Tasks"], repeatability := some 2 },
      { level := 10, path := ["Project", "Milestones"], repeatability := some 2 },
      { level := 30, path := ["Project", "Reviews"], repeatability := some 2 }] }

private def keyPath (field : String := "Effort") : SurfaceFieldPath :=
  { base := .absolute, groups := ["Project", "Milestones", "Tasks"], field }

private def phasePath : SurfaceFieldPath :=
  { base := .absolute, groups := ["Project", "Milestones"], field := "Phase" }

private def fromGroup (groups : List String) : SurfaceNumberRepetitionNotUniqueScope :=
  .from { base := .absolute, groups }

private def authored (scope : SurfaceNumberRepetitionNotUniqueScope := .default)
    (firstKey : SurfaceFieldPath := keyPath)
    (restKeys : List SurfaceFieldPath := []) :
    SurfaceNumberRepetitionNotUniqueSource :=
  { firstKey, restKeys, scope }

private def rows : List RowAddr := [
  { group := 10, path := [1] }, { group := 20, path := [1, 1] },
  { group := 20, path := [1, 2] }, { group := 10, path := [2] },
  { group := 20, path := [2, 1] }, { group := 20, path := [2, 2] }]

private def document : Document :=
  { instantiatedRows := rows, rawCells := fun _ => none }

private def rawNumber (value : Nat) : RawCell :=
  .parsed (.num value)

private def crossMilestoneRead (environment : Env) (field : FieldId) : RawCell :=
  if field == estimate.id then .empty
  else
    match environment with
    | [(10, 1), (20, 1)] => rawNumber 5
    | [(10, 1), (20, 2)] => rawNumber 7
    | [(10, 2), (20, 1)] => rawNumber 5
    | [(10, 2), (20, 2)] => rawNumber 9
    | _ => .empty

private def withinFirstMilestoneRead (environment : Env)
    (field : FieldId) : RawCell :=
  if field == estimate.id then .empty
  else
    match environment with
    | [(10, 1), (20, _)] => rawNumber 5
    | _ => rawNumber 9

private def errorOf (surface : SurfaceNumberRepetitionNotUniqueSource)
    (declaringGroup : GroupPath := ["Project"]) :
    Option NumberRepetitionNotUniqueElabError :=
  match elaborateNumberRepetitionNotUniqueSource model declaringGroup surface with
  | .ok _ => none
  | .error error => some error

private def verdictsOf (surface : SurfaceNumberRepetitionNotUniqueSource)
    (outer : Env) (relevance : ValidationRelevanceScope)
    (read : Env → FieldId → RawCell) : Option (List (Env × Verdict)) :=
  match elaborateNumberRepetitionNotUniqueSource model ["Project"] surface with
  | .error _ => none
  | .ok checked =>
      match checked.evaluate document outer relevance read with
      | .error _ => none
      | .ok results => some (results.map fun result => (result.row, result.verdict))

/- The default first-repeatable scope compares all nested task rows across milestones. -/
example :
    verdictsOf (authored) [] .full crossMilestoneRead = some [
      ([(10, 1), (20, 1)], .fired .value),
      ([(10, 1), (20, 2)], .notFired),
      ([(10, 2), (20, 1)], .fired .value),
      ([(10, 2), (20, 2)], .notFired)] := by
  native_decide

/- Explicit `@From Tasks` makes each bound milestone one independent scope. -/
example :
    verdictsOf (authored (fromGroup ["Project", "Milestones", "Tasks"]))
      [(10, 1)] .full crossMilestoneRead = some [
        ([(10, 1), (20, 1)], .notFired),
        ([(10, 1), (20, 2)], .notFired)] ∧
    verdictsOf (authored (fromGroup ["Project", "Milestones", "Tasks"]))
      [(10, 1)] .full withinFirstMilestoneRead = some [
        ([(10, 1), (20, 1)], .fired .value),
        ([(10, 1), (20, 2)], .fired .value)] := by
  native_decide

private def firstTaskOnly : ValidationRelevanceScope :=
  .partialSet [{
    path := effort.path
    indices := [.concrete 1, .concrete 1, .concrete 1, .concrete 1] }]

/- A partially relevant duplicate partner is removed before duplicate construction. -/
example :
    verdictsOf (authored) [] firstTaskOnly crossMilestoneRead = some [
      ([(10, 1), (20, 1)], .notFired)] := by
  native_decide

/- Composite optional empties participate and make a duplicate OMISSION-typed. -/
example :
    verdictsOf (authored (restKeys := [keyPath "Estimate"])) [] .full
      crossMilestoneRead = some [
        ([(10, 1), (20, 1)], .fired .omission),
        ([(10, 1), (20, 2)], .notFired),
        ([(10, 2), (20, 1)], .fired .omission),
        ([(10, 2), (20, 2)], .notFired)] := by
  native_decide

private def malformedDuplicate (environment : Env) (field : FieldId) : RawCell :=
  if field == estimate.id then .empty
  else if environment == [(10, 2), (20, 1)] then .rejected .malformed
  else crossMilestoneRead environment field

/- A formally invalid key row is retained as the resolved UNKNOWN refinement but cannot make its peer duplicate. -/
example :
    verdictsOf (authored) [] .full malformedDuplicate = some [
      ([(10, 1), (20, 1)], .notFired),
      ([(10, 1), (20, 2)], .notFired),
      ([(10, 2), (20, 1)], .unknown),
      ([(10, 2), (20, 2)], .notFired)] := by
  native_decide

/- Static lowering fixes direct-key uniqueness, one exact key path and Number kind, a containing reference group, and a repeatable level below the rule group. -/
example :
    errorOf (authored (restKeys := [keyPath])) =
        some (.duplicateKeyField effort.id) ∧
    errorOf (authored (restKeys := [phasePath])) =
        some (.keyPathMismatch effort.groupPath phase.groupPath) ∧
    errorOf (authored (firstKey := keyPath "Text")) =
        some (.keyNotNumber text.path .string) ∧
    errorOf (authored (fromGroup ["Project", "Reviews"])) =
        some (.referenceGroupDoesNotContainKey
          ["Project", "Reviews"] effort.groupPath) ∧
    errorOf (authored) effort.groupPath =
        some (.missingReferenceGroup effort.path) := by
  native_decide

end A12Kernel.Conformance.RepetitionNotUniqueElaboration
