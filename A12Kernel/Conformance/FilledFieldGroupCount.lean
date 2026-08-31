import A12Kernel.Elaboration.FilledFieldGroupCount

/-! # Checked group-scope `NumberOfFilledFields` conformance

The fixed-group rows distinguish filled, present-empty, and absent descendants. The starred rows distinguish whole-extent expansion from a per-row or row-1 read and lock the empty-group zero.
-/

namespace A12Kernel

private def fixedModel : FlatModel :=
  { fields := [
      { id := 1, groupPath := ["Order", "Contact"], name := "Street",
        policy := { kind := .string } },
      { id := 2, groupPath := ["Order", "Contact"], name := "City",
        policy := { kind := .string } }] }

private def fixedPrepared :
    PreparedFlatStringContext fixedModel builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler fixedModel).toOption.get (by native_decide)

private def fixedSource : SurfaceFilledFieldCountFixedGroupValidationSource :=
  { group := { base := .absolute, groups := ["Order", "Contact"] } }

private def fixedChecked? : Option (CheckedFilledFieldCountGroupSource fixedModel) :=
  (elaborateFilledFieldCountFixedGroupValidationSource
    fixedModel ["Order"] fixedSource).toOption

private def fixedRootError? : Option FilledFieldCountGroupElabError :=
  match elaborateFilledFieldCountFixedGroupValidationSource fixedModel ["Order"] {
      group := { base := .absolute, groups := ["Order"] } } with
  | .ok _ => none
  | .error error => some error

example : fixedRootError? = some (.rootGroup ["Order"]) := by
  native_decide

private def fixedCount (cells : List ClassifiedCellInput) : Option FilledFieldCount := do
  let checked ← fixedChecked?
  let document ← (checkDocument fixedPrepared "en_US" {
    instantiatedRows := []
    cells }).toOption
  (checked.evaluateCheckedDocumentValidation document []).toOption

private def fixedOperand (cells : List ClassifiedCellInput) : Option NumericOperand := do
  let checked ← fixedChecked?
  let document ← (checkDocument fixedPrepared "en_US" {
    instantiatedRows := []
    cells }).toOption
  (checked.evaluateCheckedDocumentFixedValidationOperand? document []).toOption.join

private def fixedVerdict (cells : List ClassifiedCellInput) : Option Verdict := do
  let operand ← fixedOperand cells
  pure (NumericComparisonOp.less.evalFixedRight operand 3)

private def cell (field : FieldId) (path : List Nat)
    (stored : String) : ClassifiedCellInput :=
  { address := { field, path }
    stored
    raw := .parsed (.str stored) }

example :
    fixedCount [cell 1 [] "s"] = some (.value 1) ∧
    fixedCount [cell 1 [] "s", cell 2 [] "c"] = some (.value 2) ∧
    fixedCount [] = some (.value 0) := by
  native_decide

/- The declared field extent, not the group's valueless path, controls comparison movement. A
   full fixed group therefore fires with VALUE, while the same firing with one empty direct field
   remains OMISSION because that field can still change the count. -/
example :
    fixedOperand [cell 1 [] "s", cell 2 [] "c"] =
        some (.value 2 .fixed) ∧
      fixedOperand [cell 1 [] "s"] = some (.value 1 .growOnly) ∧
      fixedVerdict [cell 1 [] "s", cell 2 [] "c"] =
        some (.fired .value) ∧
      fixedVerdict [cell 1 [] "s"] = some (.fired .omission) := by
  native_decide

private def starredModel : FlatModel :=
  { fields := [
      { id := 10, groupPath := ["Order", "Lines"], name := "A",
        policy := { kind := .string }, repeatableScope := [10] },
      { id := 11, groupPath := ["Order", "Lines"], name := "B",
        policy := { kind := .string }, repeatableScope := [10] }]
    repeatableGroups := [{
      level := 10, path := ["Order", "Lines"], repeatability := some 10 }] }

private def starredPrepared :
    PreparedFlatStringContext starredModel builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler starredModel).toOption.get (by native_decide)

private def starredSource : SurfaceFilledFieldCountStarredGroupValidationSource :=
  { group := {
      base := .absolute
      groups := [{ name := "Order" }, { name := "Lines", starred := true }] } }

private def starredChecked? :
    Option (CheckedFilledFieldCountGroupSource starredModel) :=
  (elaborateFilledFieldCountStarredGroupValidationSource
    starredModel ["Order"] starredSource).toOption

private def starredCount (rows : List RowAddr)
    (cells : List ClassifiedCellInput) : Option FilledFieldCount := do
  let checked ← starredChecked?
  let document ← (checkDocument starredPrepared "en_US" {
    instantiatedRows := rows
    cells }).toOption
  (checked.evaluateCheckedDocumentValidation document []).toOption

private def twoRows : List RowAddr := [
  { group := 10, path := [1] }, { group := 10, path := [2] }]

private def fourFilled : List ClassifiedCellInput := [
  cell 10 [1] "a1", cell 11 [1] "b1",
  cell 10 [2] "a2", cell 11 [2] "b2"]

example :
    starredCount twoRows fourFilled = some (.value 4) ∧
    starredCount [] [] = some (.value 0) ∧
    starredCount twoRows [cell 10 [2] "a2"] = some (.value 1) := by
  native_decide

private def nestedModel : FlatModel :=
  { fields := [
      { id := 20, groupPath := ["Probe", "Flat"], name := "FlatA",
        policy := { kind := .string } },
      { id := 21, groupPath := ["Probe", "Flat", "Rows"], name := "RowR",
        policy := { kind := .string }, repeatableScope := [20] }]
    repeatableGroups := [{
      level := 20, path := ["Probe", "Flat", "Rows"], repeatability := some 3 }] }

private def nestedPrepared :
    PreparedFlatStringContext nestedModel builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler nestedModel).toOption.get (by native_decide)

private def nestedChecked? : Option (CheckedFilledFieldCountGroupSource nestedModel) :=
  (elaborateFilledFieldCountFixedGroupValidationSource nestedModel ["Probe"] {
    group := { base := .absolute, groups := ["Probe", "Flat"] } }).toOption

private def nestedOperand (rows : List RowAddr)
    (cells : List ClassifiedCellInput) : Option NumericOperand := do
  let checked ← nestedChecked?
  let document ← (checkDocument nestedPrepared "en_US" {
    instantiatedRows := rows
    cells }).toOption
  (checked.evaluateCheckedDocumentFixedValidationOperand? document []).toOption.join

private def nestedRows (count : Nat) : List RowAddr :=
  (List.range count).map fun index => { group := 20, path := [index + 1] }

private def nestedFilled (count : Nat) : List ClassifiedCellInput :=
  cell 20 [] "a" :: (List.range count).map fun index => cell 21 [index + 1] "r"

/- Movement is bounded by the subtree's declared **slot capacity**, not by its declaration count. One
   direct field beside a `max 3` descendant row holding one field admits four cells, so a document at
   two or three filled cells can still grow and fires OMISSION, and only the fourth is fixed. Measured
   on kernel 30.8.1 at the
   [nested-capacity checkpoint](../../docs/SOURCES.md#src-filled-field-count-nested-capacity); the two
   numbers coincide exactly when the subtree owns no repeatable descendant, which every other fixture
   here satisfies. -/
example :
    nestedOperand (nestedRows 1) (nestedFilled 1) = some (.value 2 .growOnly) ∧
    nestedOperand (nestedRows 2) (nestedFilled 2) = some (.value 3 .growOnly) ∧
    nestedOperand (nestedRows 3) (nestedFilled 3) = some (.value 4 .fixed) := by
  native_decide

end A12Kernel
