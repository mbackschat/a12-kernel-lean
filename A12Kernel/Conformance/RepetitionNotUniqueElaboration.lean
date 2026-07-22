import A12Kernel.Elaboration.RepetitionNotUnique

/-! # Checked nested heterogeneous `RepetitionNotUnique` locks -/

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

private def reviewScore : FlatFieldDecl :=
  { id := 5
    groupPath := ["Project", "Reviews"]
    name := "Score"
    policy := { kind := .number { scale := 0, signed := false } }
    repeatableScope := [30] }

private def status : FlatFieldDecl :=
  { id := 8
    groupPath := ["Project", "Milestones", "Tasks"]
    name := "Status"
    policy := { kind := .enumeration }
    enumeration := some {
      storedTokens := ["OPEN", "CLOSED", "WAITING", "DONE"]
      categories := [{
        name := "Bucket"
        tokens := ["ACTIVE", "ACTIVE", "ACTIVE", "ACTIVE"] }] }
    repeatableScope := [10, 20] }

private def model : FlatModel :=
  { fields := [effort, estimate, text, phase, reviewScore, status]
    repeatableGroups := [
      { level := 20, path := ["Project", "Milestones", "Tasks"], repeatability := some 2 },
      { level := 10, path := ["Project", "Milestones"], repeatability := some 2 },
      { level := 30, path := ["Project", "Reviews"], repeatability := some 2 }] }

private def keyPath (field : String := "Effort") : SurfaceFieldPath :=
  { base := .absolute, groups := ["Project", "Milestones", "Tasks"], field }

private def phasePath : SurfaceFieldPath :=
  { base := .absolute, groups := ["Project", "Milestones"], field := "Phase" }

private def reviewPath : SurfaceFieldPath :=
  { base := .absolute, groups := ["Project", "Reviews"], field := "Score" }

private def fromGroup (groups : List String) : SurfaceRepetitionNotUniqueScope :=
  .from { base := .absolute, groups }

private def authored (scope : SurfaceRepetitionNotUniqueScope := .default)
    (firstKey : SurfaceFieldPath := keyPath)
    (restKeys : List SurfaceFieldPath := []) :
    SurfaceRepetitionNotUniqueSource :=
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
  if field == phase.id then
    match environment with
    | [(10, repetition)] => rawNumber repetition
    | _ => .rejected .malformed
  else if field == text.id then
    match environment with
    | [(10, 1), (20, 1)] | [(10, 2), (20, 1)] => .parsed (.str "A")
    | _ => .parsed (.str "B")
  else if field == estimate.id then .empty
  else
    match environment with
    | [(10, 1), (20, 1)] => rawNumber 5
    | [(10, 1), (20, 2)] => rawNumber 7
    | [(10, 2), (20, 1)] => rawNumber 5
    | [(10, 2), (20, 2)] => rawNumber 9
    | _ => .empty

private def samePhaseRead (environment : Env) (field : FieldId) : RawCell :=
  if field == phase.id then rawNumber 1 else crossMilestoneRead environment field

private def enumerationDuplicateRead (environment : Env)
    (field : FieldId) : RawCell :=
  if field == status.id then
    match environment with
    | [(10, 1), (20, 1)] | [(10, 2), (20, 1)] => .parsed (.enum "OPEN")
    | _ => .parsed (.enum "CLOSED")
  else
    crossMilestoneRead environment field

private def enumerationDistinctRead (environment : Env)
    (field : FieldId) : RawCell :=
  if field == status.id then
    match environment with
    | [(10, 1), (20, 1)] => .parsed (.enum "OPEN")
    | [(10, 1), (20, 2)] => .parsed (.enum "CLOSED")
    | [(10, 2), (20, 1)] => .parsed (.enum "WAITING")
    | _ => .parsed (.enum "DONE")
  else
    crossMilestoneRead environment field

private def enumerationInvalidRead (environment : Env)
    (field : FieldId) : RawCell :=
  if field == status.id then
    match environment with
    | [(10, 1), (20, 1)] => .parsed (.enum "OPEN")
    | [(10, 2), (20, 1)] => .parsed (.enum "OUTSIDE")
    | _ => .parsed (.enum "CLOSED")
  else
    crossMilestoneRead environment field

private def withinFirstMilestoneRead (environment : Env)
    (field : FieldId) : RawCell :=
  if field == estimate.id then .empty
  else
    match environment with
    | [(10, 1), (20, _)] => rawNumber 5
    | _ => rawNumber 9

private def errorOf (surface : SurfaceRepetitionNotUniqueSource)
    (declaringGroup : GroupPath := ["Project"]) :
    Option RepetitionNotUniqueElabError :=
  match elaborateRepetitionNotUniqueSource model declaringGroup surface with
  | .ok _ => none
  | .error error => some error

private def verdictsOf (surface : SurfaceRepetitionNotUniqueSource)
    (outer : Env) (relevance : ValidationRelevanceScope)
    (read : Env → FieldId → RawCell) : Option (List (Env × Verdict)) :=
  match elaborateRepetitionNotUniqueSource model ["Project"] surface with
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

/- String keys preserve exact normalized token identity instead of acquiring Number equality. -/
example :
    verdictsOf (authored (firstKey := keyPath "Text")) [] .full
      crossMilestoneRead = some [
        ([(10, 1), (20, 1)], .fired .value),
        ([(10, 1), (20, 2)], .fired .value),
        ([(10, 2), (20, 1)], .fired .value),
        ([(10, 2), (20, 2)], .fired .value)] := by
  native_decide

private def numericLookingStringRead (environment : Env) (field : FieldId) : RawCell :=
  if field == text.id then
    match environment with
    | [(10, 1), (20, 1)] => .parsed (.str "5")
    | [(10, 1), (20, 2)] => .parsed (.str "X")
    | [(10, 2), (20, 1)] => .parsed (.str "5.00")
    | _ => .parsed (.str "Y")
  else
    crossMilestoneRead environment field

/- Numeric-looking String spellings remain distinct, unlike Number components. -/
example :
    verdictsOf (authored (firstKey := keyPath "Text")) [] .full
      numericLookingStringRead = some [
        ([(10, 1), (20, 1)], .notFired),
        ([(10, 1), (20, 2)], .notFired),
        ([(10, 2), (20, 1)], .notFired),
        ([(10, 2), (20, 2)], .notFired)] := by
  native_decide

/- Mixed Number/String composite keys retain authored component order and typed equality. -/
example :
    verdictsOf (authored (restKeys := [keyPath "Text"])) [] .full
      crossMilestoneRead = some [
        ([(10, 1), (20, 1)], .fired .value),
        ([(10, 1), (20, 2)], .notFired),
        ([(10, 2), (20, 1)], .fired .value),
        ([(10, 2), (20, 2)], .notFired)] := by
  native_decide

/- An ancestor key is read at its own repetition prefix for every deepest-row instance. -/
example :
    verdictsOf (authored (firstKey := phasePath) (restKeys := [keyPath])) [] .full
      crossMilestoneRead = some [
        ([(10, 1), (20, 1)], .notFired),
        ([(10, 1), (20, 2)], .notFired),
        ([(10, 2), (20, 1)], .notFired),
        ([(10, 2), (20, 2)], .notFired)] ∧
    verdictsOf (authored (firstKey := phasePath) (restKeys := [keyPath])) [] .full
      samePhaseRead = some [
        ([(10, 1), (20, 1)], .fired .value),
        ([(10, 1), (20, 2)], .notFired),
        ([(10, 2), (20, 1)], .fired .value),
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

/- Direct Enumeration keys retain exact checked stored tokens rather than applying a category projection. -/
example :
    verdictsOf (authored (firstKey := keyPath "Status")) [] .full
      enumerationDuplicateRead = some [
        ([(10, 1), (20, 1)], .fired .value),
        ([(10, 1), (20, 2)], .fired .value),
        ([(10, 2), (20, 1)], .fired .value),
        ([(10, 2), (20, 2)], .fired .value)] ∧
    verdictsOf (authored (firstKey := keyPath "Status")) [] .full
      enumerationDistinctRead = some [
        ([(10, 1), (20, 1)], .notFired),
        ([(10, 1), (20, 2)], .notFired),
        ([(10, 2), (20, 1)], .notFired),
        ([(10, 2), (20, 2)], .notFired)] := by
  native_decide

/- Enumeration domain checking happens before the established duplicate relation. -/
example :
    verdictsOf (authored (firstKey := keyPath "Status")) [] .full
      enumerationInvalidRead = some [
        ([(10, 1), (20, 1)], .notFired),
        ([(10, 1), (20, 2)], .fired .value),
        ([(10, 2), (20, 1)], .unknown),
        ([(10, 2), (20, 2)], .fired .value)] := by
  native_decide

/- Enumeration components compose with Number components through the same typed key list. -/
example :
    verdictsOf (authored (firstKey := keyPath "Status")
        (restKeys := [keyPath])) [] .full enumerationDuplicateRead = some [
      ([(10, 1), (20, 1)], .fired .value),
      ([(10, 1), (20, 2)], .notFired),
      ([(10, 2), (20, 1)], .fired .value),
      ([(10, 2), (20, 2)], .notFired)] := by
  native_decide

private def flag : FlatFieldDecl :=
  { effort with id := 6, name := "Flag", policy := { kind := .boolean } }

private def modelWithFlag : FlatModel :=
  { model with fields := flag :: model.fields }

private def customText : FlatFieldDecl :=
  { id := 7
    groupPath := text.groupPath
    name := "CustomText"
    policy := text.policy
    customType := some { name := "ProjectCode" }
    repeatableScope := text.repeatableScope }

private def modelWithCustomText : FlatModel :=
  { model with fields := customText :: model.fields }

private def unsupportedError : Option RepetitionNotUniqueElabError :=
  match elaborateRepetitionNotUniqueSource modelWithFlag ["Project"]
      (authored (firstKey := keyPath "Flag")) with
  | .ok _ => none
  | .error error => some error

private def customTextError : Option RepetitionNotUniqueElabError :=
  match elaborateRepetitionNotUniqueSource modelWithCustomText ["Project"]
      (authored (firstKey := keyPath "CustomText")) with
  | .ok _ => none
  | .error error => some error

/- Static lowering fixes direct-key uniqueness, one exact key path and a supported typed component, a containing reference group, and a repeatable level below the rule group. -/
example :
    errorOf (authored (restKeys := [keyPath])) =
        some (.duplicateKeyField effort.id) ∧
    errorOf (authored (restKeys := [reviewPath])) =
        some (.keyPathMismatch effort.groupPath reviewScore.groupPath) ∧
    unsupportedError =
        some (.unsupportedKeyKind flag.path .boolean) ∧
    customTextError =
        some (.customStringRequiresPreparedChecking customText.path) ∧
    errorOf (authored (fromGroup ["Project", "Milestones", "Tasks"])
        phasePath [keyPath]) =
        some (.referenceGroupDoesNotContainKey
          ["Project", "Milestones", "Tasks"] phase.groupPath) ∧
    errorOf (authored (fromGroup ["Project", "Reviews"])) =
        some (.referenceGroupDoesNotContainKey
          ["Project", "Reviews"] effort.groupPath) ∧
    errorOf (authored) effort.groupPath =
        some (.missingReferenceGroup effort.path) := by
  native_decide

end A12Kernel.Conformance.RepetitionNotUniqueElaboration
