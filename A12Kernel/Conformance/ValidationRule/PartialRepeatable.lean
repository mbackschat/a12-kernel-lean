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
      storedTokens := ["A", "B"]
      defaultStoredToken := some "B"
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

private def relevantPartialGroupField
    (field : FlatFieldDecl) : RelevantEntityPattern :=
  { path := field.path
    indices := field.path.map fun segment =>
      if segment == "Sections" then .concrete 1 else .all }

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
        (partialGroupData (some ("A", .parsed (.enum "A"))))
        [relevantPartialGroup] = some [.notFired] ∧
    partialGroupVerdicts? partialGroupNotFilledRule?
        (partialGroupData (some ("bad", .rejected .malformed)))
        [relevantPartialGroup] = some [.unknown] ∧
    partialGroupVerdicts? partialGroupNotFilledRule?
        (partialGroupData none) [relevantPartialGroup] =
      some [.unknown] := by
  native_decide

end A12Kernel.Conformance.ValidationRule.PartialRepeatable
