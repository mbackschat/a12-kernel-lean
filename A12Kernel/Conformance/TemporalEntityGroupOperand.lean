import A12Kernel.Elaboration.TemporalValuesNotUnique

/-! # Checked temporal group-scope entity-list carrier

The temporal uniqueness carrier certifies one authored group slot as a complete recursive temporal
expansion with one declared format. Translate and Analyze retain the authored slot plus that
expansion. Execute remains explicitly refused because this capsule measures static admission only
and does not transfer a runtime account from neighbouring carriers.
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

private def source? : Option (CheckedTemporalValuesNotUniqueSource model) :=
  (elaborateTemporalValuesNotUniqueSource model ["Form"] {
    first := .group (.path {
      base := .absolute, groups := ["Form", "Dates"] })
    rest := [] }).toOption

/- Measured beside its explicit-field control with structured `rule check` at clean a12-dmkits
   `57ddd442`, dmtool 0.13.0, against kernel 30.8.1. -/
example : source?.isSome = true := by native_decide

/- The certificate retains one authored group slot and its recursive declaration expansion; it
   does not lower the group to three authored field operands. -/
private def retainedGroup? : Option (GroupPath × Bool × List FieldId) := do
  let source ← source?
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

private def emptyCheckedDocument : CheckedDocument model :=
  (checkDocument prepared "en_US" { instantiatedRows := [], cells := [] })
    |>.toOption.get (by native_decide)

private def runtimeError? : Option CheckedAddressingError := do
  let source ← source?
  match source.evaluateCheckedDocumentValuesNotUnique emptyCheckedDocument [] with
  | .error error => some error
  | .ok _ => none

example :
    runtimeError? =
      some (.addressing (.unsupportedGroupOperand ["Form", "Dates"])) := by
  native_decide

end A12Kernel.Conformance.TemporalEntityGroupOperand
