import A12Kernel.Conformance.ValidationRule.OrdinarySupport.Runtime
import A12Kernel.Elaboration.CheckedIndexPreliminary

/-!
# Checked repeatable partial-validation rule locks

This family remains independently buildable with `lake build A12Kernel.Conformance.ValidationRule.PartialRepeatable`; the validation-rule conformance module is only its import umbrella.
-/

namespace A12Kernel.Conformance.ValidationRule.PartialRepeatable

open A12Kernel
open A12Kernel.Conformance.ValidationRule.OrdinarySupport

private def detailFilledCondition? :
    Option (CheckedValidationCondition ordinaryIterationModel) :=
  (CheckedValidationCondition.fromRepeatableFieldPresence
    ordinaryIterationModel ["Order"] .filled
    (ordinaryPath ["Order", "Sections", "Details"] "SectionDetail")).toOption

private def pairedCondition? (disjoin : Bool) :
    Option (CheckedValidationCondition ordinaryIterationModel) := do
  let amount ← outerIterationCondition?
  let detail ← detailFilledCondition?
  if disjoin then (amount.or detail).toOption
  else (amount.and detail).toOption

private def pairedRule? (disjoin : Bool) :
    Option (CheckedResolvedValidationRule ordinaryIterationModel) := do
  let condition ← pairedCondition? disjoin
  (assembleResolvedValidationRule ordinaryIterationModel condition
    outerAmount.id "partialRepeatable" .error { parts := [] }).toOption

private def nestedPresenceRule? :
    Option (CheckedResolvedValidationRule ordinaryIterationModel) := do
  let condition ←
    (CheckedValidationCondition.fromRepeatableFieldPresence
      ordinaryIterationModel ["Order"] .filled
      (ordinaryPath ["Order", "Sections", "Items"] "InnerAmount")).toOption
  (assembleResolvedValidationRule ordinaryIterationModel condition
    innerAmount.id "partialNested" .error { parts := [] }).toOption

private def row (coordinate : Nat) : RowAddr :=
  { group := 10, path := [coordinate] }

private def filled (field : FieldId) (coordinate : Nat) :
    ClassifiedCellInput :=
  { address := { field, path := [coordinate] }
    stored := "1"
    raw := .parsed (.num 1) }

private def twoRows : DocumentData :=
  { instantiatedRows := [row 2, row 1]
    cells := [
      filled outerAmount.id 1,
      filled outerAmount.id 2,
      filled sectionDetail.id 1,
      filled sectionDetail.id 2
    ] }

private def noRows : DocumentData :=
  { instantiatedRows := [], cells := [] }

private def relevantCell
    (declaration : FlatFieldDecl) (coordinate : Nat) :
    RelevantEntityPattern :=
  { path := declaration.path
    indices := declaration.path.map fun segment =>
      if segment == "Sections" then .concrete coordinate else .all }

private def row2Both : ValidationRelevanceScope :=
  .partialSet [
    relevantCell outerAmount 2,
    relevantCell sectionDetail 2
  ]

private def row1ErrorOnly : ValidationRelevanceScope :=
  .partialSet [relevantCell outerAmount 1]

private def orderAncestor : ValidationRelevanceScope :=
  .partialSet [{ path := ["Order"], indices := [.concrete 1] }]

private def partialGroupError : FlatFieldDecl :=
  { id := 50
    groupPath := ["Order", "Sections"]
    name := "Error"
    policy := { kind := .number { scale := 0, signed := true } }
    repeatableScope := [10] }

private def partialGroupIndex : FlatFieldDecl :=
  { id := 51
    groupPath := ["Order", "Sections"]
    name := "Index"
    policy := { kind := .enumeration }
    enumeration := some {
      storedTokens := ["1", "2"]
      defaultStoredToken := some "2"
    }
    repeatableScope := [10] }

private def selectedDetail : FlatFieldDecl :=
  { id := 52
    groupPath := ["Order", "Sections", "Details"]
    name := "Selected"
    policy := { kind := .number { scale := 0, signed := true } }
    repeatableScope := [10] }

private def otherDetail : FlatFieldDecl :=
  { id := 53
    groupPath := ["Order", "Sections", "Details"]
    name := "Other"
    policy := { kind := .number { scale := 0, signed := true } }
    repeatableScope := [10] }

private def partialGroupModel : FlatModel :=
  { fields := [
      partialGroupError, partialGroupIndex, selectedDetail, otherDetail]
    repeatableGroups := [{
      level := 10
      path := ["Order", "Sections"]
      repeatability := some 2
      indexField := some partialGroupIndex.id
    }] }

private def numericIndex : FlatFieldDecl :=
  { id := 60
    groupPath := ["Order", "Rows"]
    name := "Index"
    policy := { kind := .number { scale := 0, signed := true } }
    repeatableScope := [20] }

private def numericRequired : FlatFieldDecl :=
  { id := 61
    groupPath := ["Order"]
    name := "Required"
    policy := { kind := .number { scale := 0, signed := true } }
    requiredness := some .absoluteOrNearestRepeatableAncestor }

private def numericIndexModel : FlatModel :=
  { fields := [numericIndex, numericRequired]
    repeatableGroups := [{
      level := 20
      path := ["Order", "Rows"]
      repeatability := some 2
      indexField := some numericIndex.id
    }] }

private def numericIndexRule? :
    Option (CheckedResolvedValidationRule numericIndexModel) := do
  let numeric ←
    (elaborateRepeatableNumericComparison numericIndexModel
      ["Order", "Rows"] {
        op := .ordinary .greater
        left := .atom (.field {
          base := .absolute
          groups := ["Order", "Rows"]
          field := "Index"
        })
        right := .literal { value := 0, authoredScale := 0 }
      }).toOption
  let condition ←
    (CheckedValidationCondition.fromOrderedNumeric numeric).toOption
  (assembleResolvedValidationRule numericIndexModel condition numericIndex.id
    "partialNumericIndex" .error { parts := [] }).toOption

private def numericIndexStar : SurfaceStarFieldPath :=
  { base := .absolute
    groups := [
      { name := "Order" },
      { name := "Rows", starred := true }]
    field := "Index" }

private def numericIndexAggregateCondition? :
    Option (CheckedValidationCondition numericIndexModel) := do
  let source ←
    (elaborateNumberEntitySource numericIndexModel ["Order"] {
      first := .star numericIndexStar
      rest := []
    }).toOption
  let core : OrderedNumericComparison numericIndexModel := {
    op := .ordinary .greater
    left := .atom (.aggregate .sum source)
    right := .literal { value := 2, authoredScale := 0 }
  }
  let checked ←
    if hCore : core.wellFormedInBool ["Order"] .sameGroupAddressed = true then
      some {
        rowGroup := ["Order"]
        operandScope := .sameGroupAddressed
        core
        modelWellFormed := by native_decide
        wellFormed := hCore
      }
    else
      none
  (CheckedValidationCondition.fromOrderedNumeric checked).toOption

private def numericRequiredAggregateRule? :
    Option (CheckedResolvedValidationRule numericIndexModel) := do
  let flat ←
    (elaborate numericIndexModel ["Order"]
      (.fieldNotFilled {
        base := .absolute
        groups := numericRequired.groupPath
        field := numericRequired.name
      })).toOption
  let required ← (CheckedValidationCondition.fromFlat flat).toOption
  let aggregate ← numericIndexAggregateCondition?
  let condition ← (required.and aggregate).toOption
  (assembleResolvedValidationRule numericIndexModel condition numericIndex.id
    "partialRequiredAggregate" .error { parts := [] }).toOption

private def numericRequiredComparisonAggregateCondition? :
    Option (CheckedValidationCondition numericIndexModel) := do
  let required ← numericRequired.toNumberField?
  let source ←
    (elaborateNumberEntitySource numericIndexModel ["Order"] {
      first := .star numericIndexStar
      rest := []
    }).toOption
  let core : OrderedNumericComparison numericIndexModel := {
    op := .ordinary .greater
    left := .binary .add
      (.atom (.ordinary (.field required)))
      (.atom (.aggregate .sum source))
    right := .literal { value := 2, authoredScale := 0 }
  }
  let checked ←
    if hCore : core.wellFormedInBool ["Order"] .sameGroupAddressed = true then
      some {
        rowGroup := ["Order"]
        operandScope := .sameGroupAddressed
        core
        modelWellFormed := by native_decide
        wellFormed := hCore
      }
    else
      none
  (CheckedValidationCondition.fromOrderedNumeric checked).toOption

private def numericRequiredComparisonAggregateRule? :
    Option (CheckedResolvedValidationRule numericIndexModel) := do
  let condition ← numericRequiredComparisonAggregateCondition?
  (assembleResolvedValidationRule numericIndexModel condition numericIndex.id
    "partialRequiredComparisonAggregate" .error { parts := [] }).toOption

private def duplicatedNumericIndexData : DocumentData :=
  { instantiatedRows := [
      { group := 20, path := [1] },
      { group := 20, path := [2] }]
    cells := [
      { address := { field := numericIndex.id, path := [1] }
        stored := "1"
        raw := .parsed (.num 1) },
      { address := { field := numericIndex.id, path := [2] }
        stored := "1"
        raw := .parsed (.num 1) }
    ] }

private def distinctNumericIndexData : DocumentData :=
  { duplicatedNumericIndexData with
    cells := [
      { address := { field := numericIndex.id, path := [1] }
        stored := "1"
        raw := .parsed (.num 1) },
      { address := { field := numericIndex.id, path := [2] }
        stored := "2"
        raw := .parsed (.num 2) }
    ] }

private def partialGroupPath (field : FlatFieldDecl) : SurfaceFieldPath :=
  { base := .absolute, groups := field.groupPath, field := field.name }

private def partialGroupFilledRule? :
    Option (CheckedResolvedValidationRule partialGroupModel) := do
  let guard ←
    (CheckedValidationCondition.fromRepeatableFieldPresence
      partialGroupModel ["Order"] .filled
      (partialGroupPath partialGroupError)).toOption
  let group ←
    (CheckedValidationCondition.fromGroupPresence partialGroupModel
      ["Order"] (absoluteGroup ["Order", "Sections", "Details"])
      .filled).toOption
  let condition ← (guard.and group).toOption
  (assembleResolvedValidationRule partialGroupModel condition
    partialGroupError.id "partialGroupFilled" .error { parts := [] }).toOption

private def partialGroupNotFilledRule? :
    Option (CheckedResolvedValidationRule partialGroupModel) := do
  let guard ←
    (CheckedValidationCondition.fromRepeatableFieldPresence
      partialGroupModel ["Order"] .filled
      (partialGroupPath partialGroupError)).toOption
  let group ←
    (CheckedValidationCondition.fromGroupPresence partialGroupModel
      ["Order"] (absoluteGroup ["Order", "Sections"]) .notFilled).toOption
  let condition ← (guard.and group).toOption
  (assembleResolvedValidationRule partialGroupModel condition
    partialGroupError.id "partialGroupNotFilled" .error { parts := [] }).toOption

private def partialIndexFilledRule? :
    Option (CheckedResolvedValidationRule partialGroupModel) := do
  let condition ←
    (CheckedValidationCondition.fromRepeatableFieldPresence
      partialGroupModel ["Order"] .filled
      (partialGroupPath partialGroupIndex)).toOption
  (assembleResolvedValidationRule partialGroupModel condition
    partialGroupIndex.id "partialIndexFilled" .error { parts := [] }).toOption

private def partialIndexNumericRule? :
    Option (CheckedResolvedValidationRule partialGroupModel) := do
  let numeric ←
    (elaborateRepeatableNumericComparison partialGroupModel
      ["Order", "Sections"] {
        op := .ordinary .greater
        left := .atom (.fieldValueAsNumber
          (.direct (partialGroupPath partialGroupIndex)))
        right := .literal { value := 0, authoredScale := 0 }
      }).toOption
  let condition ←
    (CheckedValidationCondition.fromOrderedNumeric numeric).toOption
  (assembleResolvedValidationRule partialGroupModel condition
    partialGroupIndex.id "partialIndexNumeric" .error { parts := [] }).toOption

private def partialGroupCell (field : FlatFieldDecl)
    (stored : String) (raw : RawCell) : ClassifiedCellInput :=
  { address := { field := field.id, path := [1] }, stored, raw }

private def partialGroupData
    (index : Option (String × RawCell))
    (other : Option RawCell := none) : DocumentData :=
  { instantiatedRows := [{ group := 10, path := [1] }]
    cells :=
      [partialGroupCell partialGroupError "1" (.parsed (.num 1))] ++
      (index.toList.map fun (stored, raw) =>
        partialGroupCell partialGroupIndex stored raw) ++
      (other.toList.map fun raw =>
        partialGroupCell otherDetail "9" raw) }

private def duplicatedIndexData : DocumentData :=
  { instantiatedRows := [
      { group := 10, path := [1] },
      { group := 10, path := [2] }]
    cells := [
      { address := { field := partialGroupIndex.id, path := [1] }
        stored := "1"
        raw := .parsed (.enum "1") },
      { address := { field := partialGroupIndex.id, path := [2] }
        stored := "1"
        raw := .parsed (.enum "1") }
    ] }

private def relevantPartialGroupField
    (field : FlatFieldDecl) : RelevantEntityPattern :=
  { path := field.path
    indices := field.path.map fun segment =>
      if segment == "Sections" then .concrete 1 else .all }

private def relevantPartialGroupFieldAt
    (field : FlatFieldDecl) (coordinate : Nat) : RelevantEntityPattern :=
  { path := field.path
    indices := field.path.map fun segment =>
      if segment == "Sections" then .concrete coordinate else .all }

private def relevantNumericIndexAt (coordinate : Nat) : RelevantEntityPattern :=
  { path := numericIndex.path
    indices := numericIndex.path.map fun segment =>
      if segment == "Rows" then .concrete coordinate else .all }

private def relevantPartialGroup : RelevantEntityPattern :=
  { path := ["Order", "Sections"]
    indices := [.all, .concrete 1] }

private def partialGroupVerdicts?
    (rule : Option (CheckedResolvedValidationRule partialGroupModel))
    (data : DocumentData) (relevant : List RelevantEntityPattern) :
    Option (List Verdict) := do
  let checkedRule ← rule
  let prepared ←
    (prepareFlatStringContext defaultWorld builtinStringPatternCompiler
      partialGroupModel).toOption
  let checked ← (checkDocument prepared "en_US" data).toOption
  let preliminary ←
    (checked.applyPartialGeneratedPreliminary relevant).toOption
  let result ←
    (checkedRule.evalOrdinaryRepeatablePartialPrepared preliminary).toOption
  match result with
  | .skipped => none
  | .evaluated rows =>
      rows.mapM fun row =>
        match row.2 with
        | .skipped => none
        | .evaluated outcome => some outcome.verdict

private def partialIndexSnapshot?
    (relevant : List RelevantEntityPattern)
    (data : DocumentData := duplicatedIndexData) :
    Option (List (Env × Option Verdict)) := do
  let rule ← partialIndexFilledRule?
  let prepared ←
    (prepareFlatStringContext defaultWorld builtinStringPatternCompiler
      partialGroupModel).toOption
  let checked ← (checkDocument prepared "en_US" data).toOption
  let preliminary ←
    (checked.applyPartialGeneratedPreliminary relevant).toOption
  let result ←
    (rule.evalOrdinaryRepeatablePartialPrepared preliminary).toOption
  match result with
  | .skipped => none
  | .evaluated rows =>
      some (rows.map fun row =>
        (row.1, match row.2 with
          | .skipped => none
          | .evaluated outcome => some outcome.verdict))

private def partialNumericIndexSnapshot?
    (relevant : List RelevantEntityPattern) :
    Option (List (Env × Option Verdict)) := do
  let rule ← numericIndexRule?
  let prepared ←
    (prepareFlatStringContext defaultWorld builtinStringPatternCompiler
      numericIndexModel).toOption
  let checked ←
    (checkDocument prepared "en_US" duplicatedNumericIndexData).toOption
  let preliminary ←
    (checked.applyPartialGeneratedPreliminary relevant).toOption
  let result ←
    (rule.evalOrdinaryRepeatablePartialPrepared preliminary).toOption
  match result with
  | .skipped => none
  | .evaluated rows =>
      some (rows.map fun row =>
        (row.1, match row.2 with
          | .skipped => none
          | .evaluated outcome => some outcome.verdict))

private def partialNumericIndexAggregateVerdict?
    (rule : Option (CheckedResolvedValidationRule numericIndexModel))
    (data : DocumentData) (relevant : List RelevantEntityPattern) :
    Option Verdict := do
  let rule ← rule
  let prepared ←
    (prepareFlatStringContext defaultWorld builtinStringPatternCompiler
      numericIndexModel).toOption
  let checked ← (checkDocument prepared "en_US" data).toOption
  let preliminary ←
    (checked.applyPartialGeneratedPreliminary relevant).toOption
  let result ←
    (rule.evalOrdinaryOncePartialPrepared preliminary).toOption
  match result with
  | .skipped => none
  | .evaluated _ outcome => some outcome.verdict

private def fullPartialGroupVerdicts?
    (rule : Option (CheckedResolvedValidationRule partialGroupModel))
    (data : DocumentData) : Option (List Verdict) := do
  let checkedRule ← rule
  let prepared ←
    (prepareFlatStringContext defaultWorld builtinStringPatternCompiler
      partialGroupModel).toOption
  let checked ← (checkDocument prepared "en_US" data).toOption
  let rows ← (checkedRule.evalOrdinaryRepeatableFull checked).toOption
  pure (rows.map fun row => row.2.verdict)

private def snapshot?
    (rule : Option (CheckedResolvedValidationRule ordinaryIterationModel))
    (data : DocumentData) (scope : ValidationRelevanceScope) :
    Option (Option (List (Env × Option Verdict))) := do
  let checkedRule ← rule
  let prepared ←
    (prepareFlatStringContext defaultWorld builtinStringPatternCompiler
      ordinaryIterationModel).toOption
  let checked ← (checkDocument prepared "en_US" data).toOption
  let result ←
    (checkedRule.evalOrdinaryRepeatablePartial checked scope).toOption
  match result with
  | .skipped => some none
  | .evaluated rows =>
      some (some (rows.map fun rowOutcome =>
        (rowOutcome.1, match rowOutcome.2 with
          | .skipped => none
          | .evaluated outcome => some outcome.verdict)))

private def nestedBoundary? :
    Option (Bool × Option OrdinaryRepeatableRuleEvaluationError) := do
  let rule ← nestedPresenceRule?
  let prepared ←
    (prepareFlatStringContext defaultWorld builtinStringPatternCompiler
      ordinaryIterationModel).toOption
  let checked ← (checkDocument prepared "en_US" ordinaryIterationData).toOption
  pure (rule.supportsOrdinaryRepeatablePartial,
    match rule.evalOrdinaryRepeatablePartial checked .full with
    | .ok _ => none
    | .error error => some error)

/- Actual rows retain immutable document order. Error-instance relevance skips row 1 before reads while row 2 evaluates normally. -/
example :
    snapshot? (pairedRule? false) twoRows row2Both =
      some (some [
        ([(10, 2)], some (.fired .value)),
        ([(10, 1)], none)
      ]) := by
  native_decide

/- A relevant error row with a nonrelevant peer remains an evaluated UNKNOWN under `And`; it is not a rule-level skip. -/
example :
    snapshot? (pairedRule? false) twoRows row1ErrorOnly =
      some (some [
        ([(10, 2)], none),
        ([(10, 1)], some .unknown)
      ]) := by
  native_decide

/- The same relevance split lets a decisive relevant left `Or` branch fire without reading its nonrelevant peer. -/
example :
    snapshot? (pairedRule? true) twoRows row1ErrorOnly =
      some (some [
        ([(10, 2)], none),
        ([(10, 1)], some (.fired .value))
      ]) := by
  native_decide

/- A caller-relevant ancestor does not manufacture a missing physical row for a per-row rule. Phantom row-1 anchoring belongs to the distinct once-evaluation rule shape. -/
example :
    snapshot? (pairedRule? false) noRows orderAncestor =
      some (some []) := by
  native_decide

/- Partial validation uses the same nested validation domain as full validation. A relevant inner Number below an existing outer row evaluates at implicit child row 1 and retains empty-as-zero omission polarity. -/
example :
    snapshot? nestedRepeatableNumericRule? {
        instantiatedRows := [{ group := 10, path := [1] }]
        cells := []
      } (.partialSet [RelevantEntityPattern.allInstances innerAmount.path]) =
      some (some [
        ([(10, 1), (20, 1)], some (.fired .omission))
      ]) := by
  native_decide

/- Complete nested environments use the same addressed presence semantics; depth does not create a second partial-rule execution mode. -/
example :
    nestedBoundary? = some (true, none) := by
  native_decide

/- A nonrelevant filled descendant cannot make a partially selected nonrepeatable group present. The selected empty peer and error target admit the row without relabeling the complete document. -/
example :
    partialGroupVerdicts? partialGroupFilledRule?
      (partialGroupData none (some (.parsed (.num 9))))
      [relevantPartialGroupField partialGroupError,
        relevantPartialGroupField selectedDetail] =
      some [.notFired] ∧
    fullPartialGroupVerdicts? partialGroupFilledRule?
      (partialGroupData none (some (.parsed (.num 9)))) =
      some [.fired .value] := by
  native_decide

/- A fully selected repeatable group distinguishes clean content from both reached formal error and cause-free suppressed-default error through the same partial preliminary view. -/
example :
    partialGroupVerdicts? partialGroupNotFilledRule?
        (partialGroupData (some ("1", .parsed (.enum "1"))))
        [relevantPartialGroup] = some [.notFired] ∧
    partialGroupVerdicts? partialGroupNotFilledRule?
        (partialGroupData (some ("bad", .rejected .malformed)))
        [relevantPartialGroup] = some [.unknown] ∧
    partialGroupVerdicts? partialGroupNotFilledRule?
        (partialGroupData none) [relevantPartialGroup] =
      some [.unknown] := by
  native_decide

/- Ordinary partial reads consume the same relevance-scoped duplicate relation as generated uniqueness. Selecting both equal index cells makes both reads UNKNOWN; selecting only row 1 removes the absent partner from the relation, so row 1 fires and row 2 remains a rule-level skip. -/
example :
    partialIndexSnapshot? [
        relevantPartialGroupFieldAt partialGroupIndex 1,
        relevantPartialGroupFieldAt partialGroupIndex 2] =
      some [
        ([(10, 1)], some .unknown),
        ([(10, 2)], some .unknown)
      ] ∧
    partialIndexSnapshot? [
        relevantPartialGroupFieldAt partialGroupIndex 1] =
      some [
        ([(10, 1)], some (.fired .value)),
        ([(10, 2)], none)
      ] := by
  native_decide

/- Cause-free suppression of a relevant defaulted index remains UNKNOWN to the ordinary reader; it is not reinterpreted as an empty checked cell. -/
example :
    partialIndexSnapshot? [
        relevantPartialGroupFieldAt partialGroupIndex 1] {
          instantiatedRows := [{ group := 10, path := [1] }]
          cells := []
        } =
      some [
        ([(10, 1)], some .unknown)
      ] := by
  native_decide

/- Cause-free default suppression also reaches an ordinary numeric conversion without escaping as a structural addressing error. -/
example :
    partialGroupVerdicts? partialIndexNumericRule?
        (partialGroupData none)
        [relevantPartialGroupField partialGroupIndex] =
      some [.unknown] := by
  native_decide

/- The shared partial read also feeds ordinary numeric atoms: duplicate Number indices are UNKNOWN, while omitting the partner restores the positive comparison on the selected row. -/
example :
    partialNumericIndexSnapshot? [
        relevantNumericIndexAt 1,
        relevantNumericIndexAt 2] =
      some [
        ([(20, 1)], some .unknown),
        ([(20, 2)], some .unknown)
      ] ∧
    partialNumericIndexSnapshot? [
        relevantNumericIndexAt 1] =
      some [
        ([(20, 1)], some (.fired .value)),
        ([(20, 2)], none)
      ] := by
  native_decide

/- A generated absolute-required finding is visible to a flat leaf inside the same addressed partial once rule. -/
example :
    partialNumericIndexAggregateVerdict? numericRequiredAggregateRule?
        distinctNumericIndexData [
          RelevantEntityPattern.allInstances numericIndex.path,
          RelevantEntityPattern.allInstances numericRequired.path] =
      some .unknown := by
  native_decide

/- A direct numeric leaf in the same addressed partial once rule also consumes the generated absolute-required finding instead of comparing immutable empty input as zero. -/
example :
    partialNumericIndexAggregateVerdict?
        numericRequiredComparisonAggregateRule?
        distinctNumericIndexData [
          RelevantEntityPattern.allInstances numericIndex.path,
          RelevantEntityPattern.allInstances numericRequired.path] =
      some .unknown := by
  native_decide

end A12Kernel.Conformance.ValidationRule.PartialRepeatable
