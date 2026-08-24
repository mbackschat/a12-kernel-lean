import A12Kernel.Elaboration.TemporalValuesNotUnique

/-! # Checked temporal group-scope entity-list carrier

The temporal uniqueness carrier certifies one authored group slot as a complete recursive temporal
expansion with one declared format. Translate and Analyze retain the authored slot plus that
expansion. Execute reads the same recursive `(row × field)` extent as the explicit-field control and
compares each reached cell by its exact stored text.
-/

namespace A12Kernel.Conformance.TemporalEntityGroupOperand

open A12Kernel

private def dateField (id : FieldId) (groups : GroupPath) (name : String)
    (scope : List RepeatableLevel := []) : FlatFieldDecl :=
  { id
    groupPath := groups
    name
    policy := { kind := .temporal .date TemporalComponents.fullDate }
    temporalTargetPolicy := some { format := "yyyy-MM-dd" }
    repeatableScope := scope }

private def model : FlatModel :=
  { fields := [
      dateField 1 ["Form", "Dates"] "Direct",
      dateField 2 ["Form", "Dates", "Rows"] "Left" [10],
      dateField 3 ["Form", "Dates", "Rows"] "Right" [10]]
    repeatableGroups := [
      { level := 10, path := ["Form", "Dates", "Rows"] }] }

private def groupOperand : SurfaceFieldEntityOperand :=
  .group (.path {
    base := .absolute, groups := ["Form", "Dates"] })

private def directOperand : SurfaceFieldEntityOperand :=
  .field {
    base := .absolute, groups := ["Form", "Dates"], field := "Direct" }

private def starOperand (field : String) : SurfaceFieldEntityOperand :=
  .star {
    base := .absolute
    groups := [
      { name := "Form" },
      { name := "Dates" },
      { name := "Rows", starred := true }]
    field }

private def groupSource? : Option (CheckedTemporalValuesNotUniqueSource model) :=
  (elaborateTemporalValuesNotUniqueSource model ["Form"] {
    first := groupOperand
    rest := [] }).toOption

private def explicitSource? : Option (CheckedTemporalValuesNotUniqueSource model) :=
  (elaborateTemporalValuesNotUniqueSource model ["Form"] {
    first := directOperand
    rest := [starOperand "Left", starOperand "Right"] }).toOption

/- Measured beside its explicit-field control with structured `rule check` at clean a12-dmkits
   `57ddd442`, dmtool 0.13.0, against kernel 30.8.1. -/
example : groupSource?.isSome = true := by native_decide

example : explicitSource?.isSome = true := by native_decide

/- The certificate retains one authored group slot and its recursive declaration expansion; it
   does not lower the group to three authored field operands. -/
private def retainedGroup? : Option (GroupPath × Bool × List FieldId) := do
  let source ← groupSource?
  let slot ← source.first.groupSlot?
  pure (slot.groupPath, slot.isStarred,
    slot.fields.map (·.declaration.id))

example :
    retainedGroup? = some (["Form", "Dates"], false, [1, 2, 3]) := by
  native_decide

private def prepared :
    PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def rows : List RowAddr :=
  [{ group := 10, path := [1] }, { group := 10, path := [2] }]

private def dateValue (day : Nat) : TemporalValue :=
  .date {
    instant := { epochMillis := 0 }
    parts := { year := 2024, month := 1, day }
    basis := .storedGregorian }

private def cell (field : FieldId) (path : List Nat) (stored : String)
    (day : Nat) : ClassifiedCellInput :=
  { address := { field, path }
    stored
    raw := .parsed (.temporal (dateValue day)) }

private def runtimeVerdicts?
    (cells : List ClassifiedCellInput) : Option (Verdict × Verdict) := do
  let groupSource ← groupSource?
  let explicitSource ← explicitSource?
  let document ←
    (checkDocument prepared "en_US" { instantiatedRows := rows, cells }).toOption
  let groupVerdict ←
    (groupSource.evaluateCheckedDocumentValuesNotUnique document []).toOption
  let explicitVerdict ←
    (explicitSource.evaluateCheckedDocumentValuesNotUnique document []).toOption
  pure (groupVerdict, explicitVerdict)

private def distinctCells : List ClassifiedCellInput :=
  [cell 1 [] "2024-01-01" 1,
    cell 2 [1] "2024-01-02" 2,
    cell 2 [2] "2024-01-03" 3,
    cell 3 [1] "2024-01-04" 4,
    cell 3 [2] "2024-01-05" 5]

/- The group and the explicit expansion both stay quiet when every reached stored text is distinct. -/
example :
    runtimeVerdicts? distinctCells = some (.notFired, .notFired) := by
  native_decide

/- A duplicate between the direct declaration and row 2 separates recursive group extent from a
   direct-child-only or first-row-only scan. -/
example :
    runtimeVerdicts? [
      cell 1 [] "2024-01-01" 1,
      cell 2 [1] "2024-01-02" 2,
      cell 2 [2] "2024-01-01" 1,
      cell 3 [1] "2024-01-04" 4,
      cell 3 [2] "2024-01-05" 5] =
        some (.fired .value, .fired .value) := by
  native_decide

/- A duplicate wholly inside row 2 proves that the group combines distinct descendant
   declarations into one compared set instead of scanning each declaration separately. -/
example :
    runtimeVerdicts? [
      cell 1 [] "2024-01-01" 1,
      cell 2 [1] "2024-01-02" 2,
      cell 2 [2] "2024-01-03" 3,
      cell 3 [1] "2024-01-04" 4,
      cell 3 [2] "2024-01-03" 3] =
        some (.fired .value, .fired .value) := by
  native_decide

/- Instantiated rows containing only empty cells contribute no comparable value. -/
example : runtimeVerdicts? [] = some (.notFired, .notFired) := by
  native_decide

end A12Kernel.Conformance.TemporalEntityGroupOperand
