import A12Kernel.Elaboration.NumericComputation.Evaluation
import A12Kernel.Elaboration.ValidationCondition.Reference

/-! # Checked Boolean/Confirm group-scope entity-list carrier

The Boolean value-count carrier certifies one authored group slot against its constant-specific
kind gate. Translate and Analyze retain the slot plus every descendant declaration, Explain
publishes the descendant fields, and checked-document Execute reads the recursive `(row × field)`
extent while preserving declared-but-uninstantiated repeatable capacity.
-/

namespace A12Kernel.Conformance.BooleanEntityGroupOperand

open A12Kernel

private def booleanField (id : FieldId) (groups : GroupPath) (name : String)
    (scope : List RepeatableLevel := []) : FlatFieldDecl :=
  { id, groupPath := groups, name, policy := { kind := .boolean },
    repeatableScope := scope }

private def confirmField (id : FieldId) (groups : GroupPath) (name : String) :
    FlatFieldDecl :=
  { id, groupPath := groups, name, policy := { kind := .confirm } }

private def model : FlatModel :=
  { fields := [
      booleanField 1 ["Form", "Flags"] "Direct",
      booleanField 2 ["Form", "Flags", "Rows"] "Left" [20],
      booleanField 3 ["Form", "Flags", "Rows"] "Right" [20],
      booleanField 4 ["Form", "Choices"] "Flag",
      confirmField 5 ["Form", "Choices"] "Confirmed"]
    repeatableGroups := [
      { level := 20, path := ["Form", "Flags", "Rows"],
        repeatability := some 3 }] }

private def directOperand : SurfaceFieldEntityOperand :=
  .field {
    base := .absolute, groups := ["Form", "Flags"], field := "Direct" }

private def starOperand (field : String) : SurfaceFieldEntityOperand :=
  .star {
    base := .absolute
    groups := [
      { name := "Form" },
      { name := "Flags" },
      { name := "Rows", starred := true }]
    field }

private def source? (expected : Bool) (groups : GroupPath) :
    Option (CheckedBooleanValueCountSource model) :=
  (elaborateBooleanValueCountSource model ["Form"] expected {
    first := .group (.path { base := .absolute, groups })
    rest := [] }).toOption

private def explicitSource? (expected : Bool) :
    Option (CheckedBooleanValueCountSource model) :=
  (elaborateBooleanValueCountSource model ["Form"] expected {
    first := directOperand
    rest := [starOperand "Left", starOperand "Right"] }).toOption

/- Measured with four structured `rule check` rows at clean a12-dmkits `57ddd442`, dmtool 0.13.0,
   against kernel 30.8.1: `True` and `False` over the Boolean group, `True` over the
   Boolean/Confirm group, and the explicit Boolean-field control. -/
example : (source? true ["Form", "Choices"]).isSome = true := by
  native_decide

example : (source? true ["Form", "Flags"]).isSome = true := by
  native_decide

example : (source? false ["Form", "Flags"]).isSome = true := by
  native_decide

/- Measured with `rule check` at clean a12-dmkits `3a4025bb`, dmtool 0.13.0, against kernel
   30.8.1: the `False` mixed Boolean/Confirm group is rejected with `MVK_NO_TYPEYESNO`. -/
example : (source? false ["Form", "Choices"]).isNone = true := by
  native_decide

private def retainedGroup? : Option (GroupPath × Bool × List FieldId) := do
  let source ← source? true ["Form", "Flags"]
  let slot ← source.first.groupSlot?
  pure (slot.groupPath, slot.isStarred, slot.fields.map (·.id))

example :
    retainedGroup? = some (["Form", "Flags"], false, [1, 2, 3]) := by
  native_decide

private def prepared :
    PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def rows (count : Nat) : List RowAddr :=
  (List.range count).map fun index =>
    { group := 20, path := [index + 1] }

private def cell (field : FieldId) (path : List Nat)
    (value : Bool) : ClassifiedCellInput :=
  { address := { field, path }
    stored := booleanValueCountToken value
    raw := .parsed (.bool value) }

private def runtimeCounts? (rowCount : Nat)
    (cells : List ClassifiedCellInput) : Option (NumericOperand × NumericOperand) := do
  let groupSource ← source? true ["Form", "Flags"]
  let explicitSource ← explicitSource? true
  let document ← (checkDocument prepared "en_US" {
    instantiatedRows := rows rowCount
    cells }).toOption
  let groupCount ←
    (groupSource.evaluateCheckedDocumentValidation document []).toOption
  let explicitCount ←
    (explicitSource.evaluateCheckedDocumentValidation document []).toOption
  pure (groupCount, explicitCount)

private def twoRowCells : List ClassifiedCellInput :=
  [cell 1 [] false,
    cell 2 [1] false,
    cell 2 [2] true,
    cell 3 [1] false,
    cell 3 [2] false]

private def threeRowCells : List ClassifiedCellInput :=
  twoRowCells ++ [cell 2 [3] false, cell 3 [3] false]

/- The group and explicit expansion both reach the second row. Remaining declared capacity makes
   equality growable even though every reached cell is filled. -/
example :
    runtimeCounts? 2 twoRowCells =
      some (.value 1 .growOnly, .value 1 .growOnly) := by
  native_decide

/- Instantiating the final declared row removes only the omitted-tail possibility, so the same
   count becomes fixed for both representations. -/
example :
    runtimeCounts? 3 threeRowCells =
      some (.value 1 .fixed, .value 1 .fixed) := by
  native_decide

/- A fully instantiated all-false group stays a fixed zero instead of manufacturing a match or an
   open tail. -/
example :
    runtimeCounts? 3 [
      cell 1 [] false,
      cell 2 [1] false,
      cell 2 [2] false,
      cell 2 [3] false,
      cell 3 [1] false,
      cell 3 [2] false,
      cell 3 [3] false] =
        some (.value 0 .fixed, .value 0 .fixed) := by
  native_decide

private def referenceFields? : Option (List FieldId) := do
  let source ← source? true ["Form", "Choices"]
  (source.referencePointers []).toOption.map fun pointers => pointers.map (·.field)

example : referenceFields? = some [4, 5] := by native_decide

/-! ## Checked `True` computation over one terminal starred group -/

private def computationModel : FlatModel :=
  { fields := [
      { id := 50, groupPath := ["Probe", "Lines"], name := "Flag",
        policy := { kind := .boolean }, repeatableScope := [50] },
      { id := 51, groupPath := ["Probe", "Lines"], name := "Confirmed",
        policy := { kind := .confirm }, repeatableScope := [50] }]
    repeatableGroups := [{
      level := 50, path := ["Probe", "Lines"], repeatability := some 2 }] }

private def computationPrepared :
    PreparedFlatStringContext computationModel builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler computationModel).toOption.get (by native_decide)

private def computationGroup : SurfaceStarGroupPath :=
  { base := .absolute
    groups := [{ name := "Probe" }, { name := "Lines", starred := true }] }

private def checkedComputation? :
    Option (CheckedTrueValueCountStarredGroupSource computationModel) :=
  (elaborateTrueValueCountStarredGroupSource
    computationModel ["Probe"] computationGroup).toOption

private def checkedValidation? :
    Option (CheckedBooleanValueCountSource computationModel) :=
  (elaborateBooleanValueCountSource computationModel ["Probe"] true {
    first := .starredGroup computationGroup
    rest := [] }).toOption

private def twoBooleanComputationModel : FlatModel :=
  { computationModel with
    fields := computationModel.fields.map fun declaration =>
      if declaration.id == 51 then
        { declaration with policy := { kind := .boolean } }
      else declaration }

private def oneBooleanComputationModel : FlatModel :=
  { computationModel with
    fields := computationModel.fields.filter (·.id == 50) }

private def oneConfirmComputationModel : FlatModel :=
  { computationModel with
    fields := computationModel.fields.filter (·.id == 51) }

private def reversedComputationModel : FlatModel :=
  { computationModel with fields := computationModel.fields.reverse }

private def twoConfirmComputationModel : FlatModel :=
  { computationModel with
    fields := computationModel.fields.map fun declaration =>
      if declaration.id == 50 then
        { declaration with policy := { kind := .confirm } }
      else declaration }

private def threeMixedComputationModel : FlatModel :=
  { computationModel with
    fields := computationModel.fields ++ [{
      id := 52, groupPath := ["Probe", "Lines"], name := "Peer",
      policy := { kind := .boolean }, repeatableScope := [50] }] }

private def elaborationFailed : Except ε α → Bool
  | .error _ => true
  | .ok _ => false

example :
    elaborationFailed (elaborateTrueValueCountStarredGroupSource
      oneBooleanComputationModel ["Probe"] computationGroup) = false ∧
    elaborationFailed (elaborateTrueValueCountStarredGroupSource
      oneConfirmComputationModel ["Probe"] computationGroup) = false ∧
    elaborationFailed (elaborateTrueValueCountStarredGroupSource
      reversedComputationModel ["Probe"] computationGroup) = false ∧
    elaborationFailed (elaborateTrueValueCountStarredGroupSource
      twoBooleanComputationModel ["Probe"] computationGroup) = false ∧
    elaborationFailed (elaborateTrueValueCountStarredGroupSource
      twoConfirmComputationModel ["Probe"] computationGroup) = false ∧
    elaborationFailed (elaborateTrueValueCountStarredGroupSource
      threeMixedComputationModel ["Probe"] computationGroup) = false := by
  native_decide

private def nestedComputationModel : FlatModel :=
  { computationModel with
    fields := computationModel.fields.map fun declaration =>
      { declaration with repeatableScope := [49, 50] }
    repeatableGroups :=
      { level := 49, path := ["Probe"], repeatability := some 2 } ::
        computationModel.repeatableGroups }

private def nestedComputationGroup : SurfaceStarGroupPath :=
  { base := .absolute
    groups := [
      { name := "Probe", starred := true },
      { name := "Lines", starred := true }] }

example :
    elaborationFailed (elaborateTrueValueCountStarredGroupSource
      nestedComputationModel ["Probe"] nestedComputationGroup) = true := by
  native_decide

private def computationRow (index : Nat) : RowAddr :=
  { group := 50, path := [index] }

private def computationCell (field : FieldId) (index : Nat)
    (stored : String) (raw : RawCell) : ClassifiedCellInput :=
  { address := { field, path := [index] }, stored, raw }

private def booleanCell (index : Nat) (value : Bool) : ClassifiedCellInput :=
  computationCell 50 index (booleanValueCountToken value) (.parsed (.bool value))

private def confirmCell (index : Nat) : ClassifiedCellInput :=
  computationCell 51 index "true" (.parsed (.conf true))

private def emptyComputationCell (field : FieldId)
    (index : Nat) : ClassifiedCellInput :=
  computationCell field index "" .presentEmpty

private def malformedBooleanCell (index : Nat) : ClassifiedCellInput :=
  computationCell 50 index "bad" (.rejected .booleanToken)

private def computationDocument? (rows : List RowAddr)
    (cells : List ClassifiedCellInput) : Option (CheckedDocument computationModel) :=
  (checkDocument computationPrepared "en_US" {
    instantiatedRows := rows, cells }).toOption

private def checkedComputationResult? (rows : List RowAddr)
    (cells : List ClassifiedCellInput) : Option NumericOperand := do
  let checked ← checkedComputation?
  let document ← computationDocument? rows cells
  (checked.evaluateCheckedDocumentComputation document []).toOption

private def checkedValidationResult? (rows : List RowAddr)
    (cells : List ClassifiedCellInput) : Option NumericOperand := do
  let checked ← checkedValidation?
  let document ← computationDocument? rows cells
  (checked.evaluateCheckedDocumentValidation document []).toOption

example :
    checkedComputationResult? [computationRow 1, computationRow 2] [
      booleanCell 1 true, emptyComputationCell 51 1,
      booleanCell 2 false, confirmCell 2] = some (.value 2 .growOnly) ∧
    checkedComputationResult? [computationRow 1, computationRow 2] [
      booleanCell 1 true, emptyComputationCell 51 1,
      booleanCell 2 false, emptyComputationCell 51 2] =
        some (.value 1 .growOnly) := by
  native_decide

example :
    checkedComputationResult? [computationRow 1, computationRow 2] [
      emptyComputationCell 50 1, emptyComputationCell 51 1,
      emptyComputationCell 50 2, emptyComputationCell 51 2] =
        some (.value 0 .growOnly) ∧
    checkedComputationResult? [] [] = some (.value 0 .fixed) := by
  native_decide

example :
    checkedComputationResult? [computationRow 1, computationRow 2] [
      booleanCell 1 true, emptyComputationCell 51 1,
      malformedBooleanCell 2, emptyComputationCell 51 2] =
        some (.unknown .booleanToken) := by
  native_decide

private def overCapacityRows : List RowAddr :=
  [computationRow 1, computationRow 2, computationRow 3]

example :
    checkedValidationResult? overCapacityRows [
      booleanCell 1 false, emptyComputationCell 51 1,
      booleanCell 2 false, emptyComputationCell 51 2,
      booleanCell 3 true, emptyComputationCell 51 3] =
        some (.unknown .overRepetition) := by
  native_decide

example :
    checkedComputationResult? overCapacityRows [
      booleanCell 1 false, emptyComputationCell 51 1,
      booleanCell 2 false, emptyComputationCell 51 2,
      booleanCell 3 true, emptyComputationCell 51 3] =
        some (.value 0 .growOnly) ∧
    checkedComputationResult? overCapacityRows [
      booleanCell 1 true, emptyComputationCell 51 1,
      booleanCell 2 false, emptyComputationCell 51 2,
      booleanCell 3 true, emptyComputationCell 51 3] =
        some (.value 1 .growOnly) ∧
    checkedComputationResult? overCapacityRows [
      booleanCell 1 true, emptyComputationCell 51 1,
      booleanCell 2 false, emptyComputationCell 51 2,
      malformedBooleanCell 3, emptyComputationCell 51 3] =
        some (.value 1 .growOnly) := by
  native_decide

/-! ## Checked `False` computation over one terminal starred Boolean group -/

private def falseComputationPrepared :
    PreparedFlatStringContext twoBooleanComputationModel
      builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler twoBooleanComputationModel).toOption.get
      (by native_decide)

private def checkedFalseComputation? :
    Option (CheckedFalseValueCountStarredGroupSource
      twoBooleanComputationModel) :=
  (elaborateFalseValueCountStarredGroupSource
    twoBooleanComputationModel ["Probe"] computationGroup).toOption

private def checkedFalseValidation? :
    Option (CheckedBooleanValueCountSource twoBooleanComputationModel) :=
  checkedFalseComputation?.map (·.toCheckedBooleanValueCountSource)

example :
    (checkedFalseComputation?.map fun checked =>
      (checked.scaleSummary,
        checked.referencesField 50,
        checked.referencesField 51,
        checked.referencesField 52,
        checked.toCheckedBooleanValueCountSource.expected)) =
      some (NumericScaleSummary.field 0, true, true, false, false) := by
  native_decide

private def peerBooleanCell (index : Nat)
    (value : Bool) : ClassifiedCellInput :=
  computationCell 51 index (booleanValueCountToken value) (.parsed (.bool value))

private def falseComputationDocument? (rows : List RowAddr)
    (cells : List ClassifiedCellInput) :
    Option (CheckedDocument twoBooleanComputationModel) :=
  (checkDocument falseComputationPrepared "en_US" {
    instantiatedRows := rows, cells }).toOption

private def checkedFalseComputationResult? (rows : List RowAddr)
    (cells : List ClassifiedCellInput) : Option NumericOperand := do
  let checked ← checkedFalseComputation?
  let document ← falseComputationDocument? rows cells
  (checked.evaluateCheckedDocumentComputation document []).toOption

private def checkedFalseValidationResult? (rows : List RowAddr)
    (cells : List ClassifiedCellInput) : Option NumericOperand := do
  let checked ← checkedFalseValidation?
  let document ← falseComputationDocument? rows cells
  (checked.evaluateCheckedDocumentValidation document []).toOption

example :
    checkedFalseComputationResult? [computationRow 1, computationRow 2] [
      booleanCell 1 false, emptyComputationCell 51 1,
      booleanCell 2 true, peerBooleanCell 2 false] =
        some (.value 2 .growOnly) ∧
    checkedFalseComputationResult? [computationRow 1, computationRow 2] [
      booleanCell 1 false, emptyComputationCell 51 1,
      booleanCell 2 true, peerBooleanCell 2 true] =
        some (.value 1 .growOnly) := by
  native_decide

example :
    checkedFalseComputationResult? [computationRow 1, computationRow 2] [
      emptyComputationCell 50 1, emptyComputationCell 51 1,
      emptyComputationCell 50 2, emptyComputationCell 51 2] =
        some (.value 0 .growOnly) ∧
    checkedFalseComputationResult? [] [] = some (.value 0 .fixed) := by
  native_decide

example :
    checkedFalseComputationResult? [computationRow 1, computationRow 2] [
      booleanCell 1 false, emptyComputationCell 51 1,
      malformedBooleanCell 2, emptyComputationCell 51 2] =
        some (.unknown .booleanToken) := by
  native_decide

example :
    checkedFalseValidationResult? overCapacityRows [
      booleanCell 1 true, peerBooleanCell 1 true,
      booleanCell 2 true, peerBooleanCell 2 true,
      booleanCell 3 false, peerBooleanCell 3 true] =
        some (.unknown .overRepetition) := by
  native_decide

example :
    checkedFalseComputationResult? overCapacityRows [
      booleanCell 1 true, peerBooleanCell 1 true,
      booleanCell 2 true, peerBooleanCell 2 true,
      booleanCell 3 false, peerBooleanCell 3 true] =
        some (.value 0 .fixed) ∧
    checkedFalseComputationResult? overCapacityRows [
      booleanCell 1 false, peerBooleanCell 1 true,
      booleanCell 2 true, peerBooleanCell 2 true,
      booleanCell 3 false, peerBooleanCell 3 true] =
        some (.value 1 .fixed) ∧
    checkedFalseComputationResult? overCapacityRows [
      booleanCell 1 false, peerBooleanCell 1 true,
      booleanCell 2 true, peerBooleanCell 2 true,
      malformedBooleanCell 3, peerBooleanCell 3 true] =
        some (.value 1 .fixed) := by
  native_decide

private def nestedTwoBooleanComputationModel : FlatModel :=
  { nestedComputationModel with
    fields := nestedComputationModel.fields.map fun declaration =>
      if declaration.id == 51 then
        { declaration with policy := { kind := .boolean } }
      else declaration }

private def nestedOuterComputationGroup : SurfaceStarGroupPath :=
  { base := .absolute
    groups := [{ name := "Probe", starred := true }] }

private def threeBooleanComputationModel : FlatModel :=
  { twoBooleanComputationModel with
    fields := twoBooleanComputationModel.fields ++ [{
      id := 52, groupPath := ["Probe", "Lines"], name := "Third",
      policy := { kind := .boolean }, repeatableScope := [50] }] }

private def threeBooleanPrepared :
    PreparedFlatStringContext threeBooleanComputationModel
      builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler threeBooleanComputationModel).toOption.get
      (by native_decide)

private def checkedThreeFalseComputation? :
    Option (CheckedFalseValueCountStarredGroupSource
      threeBooleanComputationModel) :=
  (elaborateFalseValueCountStarredGroupSource
    threeBooleanComputationModel ["Probe"] computationGroup).toOption

private def thirdBooleanCell (index : Nat)
    (value : Bool) : ClassifiedCellInput :=
  computationCell 52 index (booleanValueCountToken value) (.parsed (.bool value))

private def malformedThirdBooleanCell (index : Nat) : ClassifiedCellInput :=
  computationCell 52 index "bad" (.rejected .booleanToken)

private def checkedThreeFalseComputationResult? (rows : List RowAddr)
    (cells : List ClassifiedCellInput) : Option NumericOperand := do
  let checked ← checkedThreeFalseComputation?
  let document ← (checkDocument threeBooleanPrepared "en_US" {
    instantiatedRows := rows, cells }).toOption
  (checked.evaluateCheckedDocumentComputation document []).toOption

example :
    checkedThreeFalseComputationResult?
      [computationRow 1, computationRow 2] [
        booleanCell 1 false, emptyComputationCell 51 1, thirdBooleanCell 1 false,
        booleanCell 2 true, peerBooleanCell 2 false, thirdBooleanCell 2 true] =
      some (.value 3 .growOnly) ∧
    checkedThreeFalseComputationResult?
      [computationRow 1, computationRow 2] [
        booleanCell 1 false, peerBooleanCell 1 true, thirdBooleanCell 1 true,
        booleanCell 2 true, peerBooleanCell 2 true, malformedThirdBooleanCell 2] =
      some (.unknown .booleanToken) ∧
    checkedThreeFalseComputationResult? overCapacityRows [
        booleanCell 1 false, peerBooleanCell 1 true, thirdBooleanCell 1 true,
        booleanCell 2 true, peerBooleanCell 2 true, thirdBooleanCell 2 true,
        booleanCell 3 true, peerBooleanCell 3 true, malformedThirdBooleanCell 3] =
      some (.value 1 .fixed) := by
  native_decide

example :
    elaborationFailed (elaborateFalseValueCountStarredGroupSource
      computationModel ["Probe"] computationGroup) = true ∧
    elaborationFailed (elaborateFalseValueCountStarredGroupSource
      oneBooleanComputationModel ["Probe"] computationGroup) = false ∧
    elaborationFailed (elaborateFalseValueCountStarredGroupSource
      nestedTwoBooleanComputationModel ["Probe"] nestedComputationGroup) = true ∧
    elaborationFailed (elaborateFalseValueCountStarredGroupSource
      nestedTwoBooleanComputationModel ["Probe"] nestedOuterComputationGroup) = true ∧
    elaborationFailed (elaborateFalseValueCountStarredGroupSource
      threeBooleanComputationModel ["Probe"] computationGroup) = false := by
  native_decide

/-! ## Fixed-group computation

The retained Kernel matrix has two direct fields in each nonrepeatable group. It separates group
expansion from the zero-producing account currently implemented by a12-dmkits and keeps wider fixed
group shapes outside the checked computation carrier.
-/

private def fixedComputationModel : FlatModel :=
  { fields := [
      booleanField 60 ["Probe", "TrueFlags"] "Flag",
      confirmField 61 ["Probe", "TrueFlags"] "Confirmed",
      booleanField 62 ["Probe", "FalseFlags"] "First",
      booleanField 63 ["Probe", "FalseFlags"] "Second"] }

private def fixedComputationPrepared :
    PreparedFlatStringContext fixedComputationModel
      builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler fixedComputationModel).toOption.get
      (by native_decide)

private def fixedGroup (name : String) : SurfaceGroupReference :=
  .path { base := .absolute, groups := ["Probe", name] }

private def checkedFixedTrueComputation? :
    Option (CheckedTrueValueCountFixedGroupSource fixedComputationModel) :=
  (elaborateTrueValueCountFixedGroupSource fixedComputationModel ["Probe"]
    (fixedGroup "TrueFlags")).toOption

private def checkedFixedFalseComputation? :
    Option (CheckedFalseValueCountFixedGroupSource fixedComputationModel) :=
  (elaborateFalseValueCountFixedGroupSource fixedComputationModel ["Probe"]
    (fixedGroup "FalseFlags")).toOption

private def checkedFixedTrueValidation? :
    Option (CheckedBooleanValueCountSource fixedComputationModel) :=
  (elaborateBooleanValueCountSource fixedComputationModel ["Probe"] true {
    first := .group (fixedGroup "TrueFlags")
    rest := [] }).toOption

private def checkedFixedFalseValidation? :
    Option (CheckedBooleanValueCountSource fixedComputationModel) :=
  (elaborateBooleanValueCountSource fixedComputationModel ["Probe"] false {
    first := .group (fixedGroup "FalseFlags")
    rest := [] }).toOption

private def widerFixedComputationModel : FlatModel :=
  { fixedComputationModel with
    fields := fixedComputationModel.fields ++ [
      booleanField 64 ["Probe", "FalseFlags"] "Third"] }

private def reversedTrueFixedComputationModel : FlatModel :=
  { fixedComputationModel with
    fields := [
      confirmField 61 ["Probe", "TrueFlags"] "Confirmed",
      booleanField 60 ["Probe", "TrueFlags"] "Flag",
      booleanField 62 ["Probe", "FalseFlags"] "First",
      booleanField 63 ["Probe", "FalseFlags"] "Second"] }

private def fixedCell (field : FieldId) (stored : String)
    (raw : RawCell) : ClassifiedCellInput :=
  { address := { field, path := [] }, stored, raw }

private def fixedBooleanCell (field : FieldId)
    (value : Bool) : ClassifiedCellInput :=
  fixedCell field (booleanValueCountToken value) (.parsed (.bool value))

private def fixedConfirmCell : ClassifiedCellInput :=
  fixedCell 61 "true" (.parsed (.conf true))

private def emptyFixedCell (field : FieldId) : ClassifiedCellInput :=
  fixedCell field "" .presentEmpty

private def malformedFixedBooleanCell (field : FieldId) : ClassifiedCellInput :=
  fixedCell field "bad" (.rejected .booleanToken)

private def malformedFixedConfirmCell : ClassifiedCellInput :=
  fixedCell 61 "bad" (.rejected .confirmToken)

private def fixedComputationResults?
    (cells : List ClassifiedCellInput) :
    Option (NumericComputationResult × NumericComputationResult) := do
  let checkedTrue ← checkedFixedTrueComputation?
  let checkedFalse ← checkedFixedFalseComputation?
  let document ← (checkDocument fixedComputationPrepared "en_US"
    { instantiatedRows := [], cells }).toOption
  let trueCount ←
    (checkedTrue.evaluateCheckedDocumentComputation document []).toOption
  let falseCount ←
    (checkedFalse.evaluateCheckedDocumentComputation document []).toOption
  pure (trueCount.toComputationResult, falseCount.toComputationResult)

private def fixedValidationResults?
    (cells : List ClassifiedCellInput) :
    Option (NumericOperand × NumericOperand) := do
  let checkedTrue ← checkedFixedTrueValidation?
  let checkedFalse ← checkedFixedFalseValidation?
  let document ← (checkDocument fixedComputationPrepared "en_US"
    { instantiatedRows := [], cells }).toOption
  let trueCount ←
    (checkedTrue.evaluateCheckedDocumentValidation document []).toOption
  let falseCount ←
    (checkedFalse.evaluateCheckedDocumentValidation document []).toOption
  pure (trueCount, falseCount)

example :
    checkedFixedTrueComputation?.isSome = true ∧
    checkedFixedFalseComputation?.isSome = true ∧
    elaborationFailed (elaborateFalseValueCountFixedGroupSource
      fixedComputationModel ["Probe"] (fixedGroup "TrueFlags")) = true ∧
    elaborationFailed (elaborateTrueValueCountFixedGroupSource
      fixedComputationModel ["Probe"] (fixedGroup "FalseFlags")) = true ∧
    elaborationFailed (elaborateTrueValueCountFixedGroupSource
      reversedTrueFixedComputationModel ["Probe"] (fixedGroup "TrueFlags")) = true ∧
    elaborationFailed (elaborateFalseValueCountFixedGroupSource
      widerFixedComputationModel ["Probe"] (fixedGroup "FalseFlags")) = true := by
  native_decide

example :
    fixedComputationResults? [
      fixedBooleanCell 60 true, fixedConfirmCell,
      fixedBooleanCell 62 false, fixedBooleanCell 63 false] =
        some (.value 2, .value 2) ∧
    fixedComputationResults? [
      fixedBooleanCell 60 false, fixedConfirmCell,
      fixedBooleanCell 62 false, fixedBooleanCell 63 true] =
        some (.value 1, .value 1) ∧
    fixedComputationResults? [
      emptyFixedCell 60, emptyFixedCell 61,
      emptyFixedCell 62, emptyFixedCell 63] =
        some (.value 0, .value 0) := by
  native_decide

/- Full validation reads the same direct-field expansion as computation. When every declaration is
   filled, the fixed group has no missing entity and a firing comparison is VALUE-typed. -/
example :
    fixedValidationResults? [
      fixedBooleanCell 60 true, fixedConfirmCell,
      fixedBooleanCell 62 false, fixedBooleanCell 63 false] =
        some (.value 2 .fixed, .value 2 .fixed) ∧
      fixedValidationResults? [
        fixedBooleanCell 60 true,
        fixedBooleanCell 62 false] =
        some (.value 1 .growOnly, .value 1 .growOnly) := by
  native_decide

example :
    fixedComputationResults? [
      fixedBooleanCell 60 true, malformedFixedConfirmCell,
      fixedBooleanCell 62 false, malformedFixedBooleanCell 63] =
        some (.poison .confirmToken, .poison .booleanToken) := by
  native_decide

end A12Kernel.Conformance.BooleanEntityGroupOperand
