import A12Kernel.Conformance.ValidationRule.OrdinarySupport.Runtime

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

end A12Kernel.Conformance.ValidationRule.PartialRepeatable
