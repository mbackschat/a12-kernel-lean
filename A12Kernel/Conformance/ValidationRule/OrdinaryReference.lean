import A12Kernel.Conformance.ValidationRule.OrdinarySupport
import A12Kernel.Elaboration.ValidationCondition.Reference

/-! # A12Kernel.Conformance.ValidationRule.OrdinaryReference — structural reference locks

The separating axis is **coordinate assignment**: one condition holds an unstarred operand bound
by the rule's iteration scope beside a starred operand that reopens a deeper level, so a rule that
wildcarded everything and a rule that wildcarded nothing both fail here. The retained list order is
authored traversal order and carries no kernel claim.
-/

namespace A12Kernel.Conformance.ValidationRule.OrdinaryReference

open A12Kernel A12Kernel.Conformance.ValidationRule.OrdinarySupport

/-- `OuterAmount + Sum(/Order/Sections/Items*/InnerAmount) > 5`, iterating `/Order/Sections`. -/
private def mixedReferences? (environment : Env) :
    Option (List MessagePointer) := do
  let rule ← outerWithInnerAggregateRule?
  (rule.condition.core.referencePointers environment).toOption

private def mixedReferenceError? (environment : Env) :
    Option ReferenceProjectionError := do
  let rule ← outerWithInnerAggregateRule?
  match rule.condition.core.referencePointers environment with
  | .error error => some error
  | .ok _ => none

/- The bound level stays concrete on both operands; only the level the star reopened is wildcard. -/
example :
    mixedReferences? [(10, 2)] = some [
      { field := outerAmount.id, coordinates := [.concrete 2] },
      { field := innerAmount.id, coordinates := [.concrete 2, .wildcard] }] := by
  native_decide

/- The concrete coordinate tracks the firing row, so the projection is per-instance rather than
   per-declaration. -/
example :
    mixedReferences? [(10, 1)] = some [
      { field := outerAmount.id, coordinates := [.concrete 1] },
      { field := innerAmount.id, coordinates := [.concrete 1, .wildcard] }] := by
  native_decide

/- An environment that does not bind the rule's own level fails closed at that exact level instead
   of inventing an unknown or first-row coordinate. -/
example : mixedReferenceError? [] = some (.binding (.missingBinding 10)) := by
  native_decide

private def conditionReferences?
    (condition : Option (CheckedValidationCondition ordinaryIterationModel))
    (environment : Env) : Option (List MessagePointer) := do
  let checked ← condition
  (checked.core.referencePointers environment).toOption

private def conditionReferenceError?
    (condition : Option (CheckedValidationCondition ordinaryIterationModel))
    (environment : Env) : Option ReferenceProjectionError := do
  let checked ← condition
  match checked.core.referencePointers environment with
  | .error error => some error
  | .ok _ => none

private def comparisonCondition?
    (comparison : Option (CheckedOrderedNumericComparison ordinaryIterationModel)) :
    Option (CheckedValidationCondition ordinaryIterationModel) := do
  let checked ← comparison
  (CheckedValidationCondition.fromOrderedNumeric checked).toOption

/- `FirstFilledValue` references every authored slot. The projection has no document argument at
   all, so no operand can be dropped for having been superseded at runtime. -/
example :
    conditionReferences? (comparisonCondition? outerWithInnerFirstFilledComparison?)
        [(10, 2)] = some [
      { field := outerAmount.id, coordinates := [.concrete 2] },
      { field := innerAmount.id, coordinates := [.concrete 2, .wildcard] }] := by
  native_decide

/- A nonrepeatable reference beside a starred one carries no coordinates rather than a padded or
   wildcarded slot. -/
example :
    (mixedDirectStarNumberSource?.bind fun source =>
      conditionReferences?
        (comparisonCondition? (outerWithInnerEntityComparison? (.aggregate .sum source) 5))
        [(10, 2)]) = some [
      { field := outerAmount.id, coordinates := [.concrete 2] },
      { field := baseAmount.id, coordinates := [] },
      { field := innerAmount.id, coordinates := [.concrete 2, .wildcard] }] := by
  native_decide

/- A reached filter refuses the whole projection instead of returning the star pointer alone. An
   incomplete set that looks complete is the failure this boundary exists to prevent. -/
example :
    conditionReferenceError?
        (comparisonCondition? outerWithFilteredInnerFirstFilledComparison?) [(10, 2)] =
      some .filteredStarOperand := by
  native_decide

/- Both connectives contribute every branch and the union is deduplicated once, so a repeated
   operand does not repeat its pointer. -/
example :
    conditionReferences?
        (do
          let condition ← comparisonCondition? outerWithInnerAggregateComparison?
          (condition.and condition).toOption)
        [(10, 2)] = some [
      { field := outerAmount.id, coordinates := [.concrete 2] },
      { field := innerAmount.id, coordinates := [.concrete 2, .wildcard] }] := by
  native_decide

/-- A presence guard on the iterating row's own field: an ordinary leaf this fragment does not
    classify. -/
private def outerPresenceGuard? :
    Option (CheckedValidationCondition ordinaryIterationModel) :=
  (CheckedValidationCondition.fromRepeatableFieldPresence
    ordinaryIterationModel ["Order", "Sections"] .filled
    (ordinaryPath ["Order", "Sections"] "OuterAmount")).toOption

/- An unclassified leaf fails its own projection, and fails the whole rule's projection when it is
   only one branch. Silence would be read as "this rule references nothing", which no rule can be. -/
example : conditionReferenceError? outerPresenceGuard? [(10, 2)] = some .unclassifiedLeaf := by
  native_decide

example :
    conditionReferenceError?
        (do
          let guard ← outerPresenceGuard?
          let aggregate ← comparisonCondition? outerWithInnerAggregateComparison?
          (guard.and aggregate).toOption)
        [(10, 2)] = some .unclassifiedLeaf := by
  native_decide

end A12Kernel.Conformance.ValidationRule.OrdinaryReference
