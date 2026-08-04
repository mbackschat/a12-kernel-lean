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

/-! ## Starred group operands

A starred group never yields a group pointer. It expands to its descendant fields, and the same one
coordinate rule applies to each: concrete for the levels the rule's iteration scope bound, wildcard
from the reopened level down. Both terminals are exercised because the two carry different scope
lengths, and each chosen group has exactly one descendant field so the expected set stays exact.
-/

/-- `/Order/Sections/Notes*` — repeatable terminal, one descendant field at scope `[10, 30]`. -/
private def notesGroupStar : SurfaceGroupListOperand :=
  .starredGroup {
    base := .absolute
    groups := [
      { name := "Order" },
      { name := "Sections" },
      { name := "Notes", starred := true }] }

/-- `/Order/Sections*/Details` — nonrepeatable terminal below the outermost star, one descendant
    field at scope `[10]`. -/
private def detailsGroupStar : SurfaceGroupListOperand :=
  .starredGroup {
    base := .absolute
    groups := [
      { name := "Order" },
      { name := "Sections", starred := true },
      { name := "Details" }] }

private def groupListCondition? (operator : GroupFillQuantifier)
    (operands : List SurfaceGroupListOperand) :
    Option (CheckedValidationCondition ordinaryIterationModel) :=
  (CheckedValidationCondition.fromGroupList ordinaryIterationModel ["Order"]
    operator operands).toOption

example :
    conditionReferences? (groupListCondition? .atLeastOneGroupFilled [notesGroupStar])
      [(10, 2)] = some [
      { field := siblingDate.id, coordinates := [.concrete 2, .wildcard] }] := by
  native_decide

/- A star at the outermost repeatable level leaves nothing concrete, and the nonrepeatable terminal
   contributes no coordinate of its own. -/
example :
    conditionReferences? (groupListCondition? .atLeastOneGroupFilled [detailsGroupStar])
      [] = some [{ field := sectionDetail.id, coordinates := [.wildcard] }] := by
  native_decide

/- A fixed field beside a starred group keeps its own concrete projection. `AllGroupsFilled` is not
   available here: the accepted operator-sensitivity rule rejects a starred operand under it. -/
example :
    conditionReferences? (groupListCondition? .atLeastOneGroupFilled
        [.field (ordinaryPath ["Order"] "BaseAmount"), notesGroupStar]) [(10, 2)] = some [
      { field := baseAmount.id, coordinates := [] },
      { field := siblingDate.id, coordinates := [.concrete 2, .wildcard] }] := by
  native_decide

/-- `/Order/Sections*` — the recursion witness. Its descendants span three deeper groups, two of
    them repeatable, so direct-child expansion and recursive expansion disagree here. -/
private def sectionsGroupStar : SurfaceGroupListOperand :=
  .starredGroup {
    base := .absolute
    groups := [{ name := "Order" }, { name := "Sections", starred := true }] }

/- Expansion is recursive, and each descendant's coordinate count comes from its **own** scope: a
   field declared in the starred group carries one wildcard, one declared in a deeper repeatable
   descendant carries two. The exact cardinality pins that nothing beyond the subtree joins. -/
example :
    (conditionReferences? (groupListCondition? .atLeastOneGroupFilled [sectionsGroupStar])
      []).map (fun pointers =>
        (pointers.contains { field := outerAmount.id, coordinates := [.wildcard] },
          pointers.contains
            { field := siblingDate.id, coordinates := [.wildcard, .wildcard] },
          pointers.length)) = some (true, true, 14) := by
  native_decide

/-- A presence guard on the iterating row's own field: an ordinary leaf this fragment does not
    classify. -/
private def outerPresenceGuard? :
    Option (CheckedValidationCondition ordinaryIterationModel) :=
  (CheckedValidationCondition.fromRepeatableFieldPresence
    ordinaryIterationModel ["Order", "Sections"] .filled
    (ordinaryPath ["Order", "Sections"] "OuterAmount")).toOption

/- An ordinary non-starred repeatable presence reference is bound by the rule's iteration scope, so
   it is concrete at the firing row. -/
example :
    conditionReferences? outerPresenceGuard? [(10, 2)] =
      some [{ field := outerAmount.id, coordinates := [.concrete 2] }] := by
  native_decide

/- The guard's reference merges with the guarded leaf's rather than appearing twice: this is the
   standard iteration-guard rule shape, projected end to end. -/
example :
    conditionReferences?
        (do
          let guard ← outerPresenceGuard?
          let aggregate ← comparisonCondition? outerWithInnerAggregateComparison?
          (guard.and aggregate).toOption)
        [(10, 2)] = some [
      { field := outerAmount.id, coordinates := [.concrete 2] },
      { field := innerAmount.id, coordinates := [.concrete 2, .wildcard] }] := by
  native_decide

/-! ## Flat leaves

The flat fragment carries no starred operand, so its own exhaustive `referencesField` can supply
membership and every reference is concretely addressed by the rule's environment. -/

private def flatCondition? (condition : SurfaceCondition) :
    Option (CheckedValidationCondition ordinaryIterationModel) := do
  let checked ← (elaborate ordinaryIterationModel ["Order"] condition).toOption
  (CheckedValidationCondition.fromFlat checked).toOption

/- Both connective branches and both presence polarities contribute; nonrepeatable references carry
   no coordinates. -/
example :
    conditionReferences?
        (flatCondition? (.and (.fieldFilled (ordinaryPath ["Order"] "BaseAmount"))
          (.fieldNotFilled (ordinaryPath ["Order"] "BaseToken")))) [] = some [
      { field := baseAmount.id, coordinates := [] },
      { field := baseToken.id, coordinates := [] }] := by
  native_decide

/- A leaf family this fragment does not classify still fails the whole rule's projection. Silence
   would be read as "this rule references nothing", which no rule can be. -/
example :
    conditionReferenceError? innerGroupFilledCondition? [(10, 2)] =
      some .unclassifiedLeaf := by
  native_decide

end A12Kernel.Conformance.ValidationRule.OrdinaryReference
