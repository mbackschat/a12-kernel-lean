import A12Kernel.Conformance.NumericComputation.Support
import A12Kernel.Elaboration.NumericComputation.Table

/-! # Checked Number computation-table locks -/

namespace A12Kernel.Conformance.NumericComputation.Table

open A12Kernel
open A12Kernel.Conformance.NumericComputation.Support

private abbrev NumericRow := ComputationAlternative
  (CheckedNumericTargetComputationOperation model)

private def operation? (target : FieldId)
    (expression : AuthoredNumericExpr SurfaceNumericAtom) :
    Option (CheckedNumericTargetComputationOperation model) :=
  (elaborateNumericTargetComputationOperation
    model ["Root"] target expression).toOption

private def operationAt? (declaringGroup : GroupPath) (target : FieldId)
    (expression : AuthoredNumericExpr SurfaceNumericAtom) :
    Option (CheckedNumericTargetComputationOperation model) :=
  (elaborateNumericTargetComputationOperation
    model declaringGroup target expression).toOption

private def literalRow? (guard : ComputationCondition) (target : FieldId)
    (value : Rat) : Option NumericRow := do
  let operation ← operation? target
    (.literal { value, authoredScale := 0 })
  pure {
    precondition := guard
    operation := operation
  }

private def literalRowAt? (declaringGroup : GroupPath)
    (guard : ComputationCondition) (target : FieldId)
    (value : Rat) : Option NumericRow := do
  let operation ← operationAt? declaringGroup target
    (.literal { value, authoredScale := 0 })
  pure {
    precondition := guard
    operation := operation
  }

private def divisionRow? (guard : ComputationCondition) : Option NumericRow := do
  let operation ←
    (elaborateNumericTargetComputationOperation model ["Root"] targetId
    (.binary .divide
      (.literal { value := 1, authoredScale := 0 })
      (.literal { value := 0, authoredScale := 0 }))
      (suppressExactScaleWarning := true)).toOption
  pure {
    precondition := guard
    operation := operation
  }

private def alteredPolicyRow? (guard : ComputationCondition) : Option NumericRow := do
  let operation ← operation? targetId
    (.literal { value := 3, authoredScale := 0 })
  let policy := { operation.policy with zeroAllowed := true }
  let alteredOperation : CheckedNumericTargetComputationOperation model := {
    operation := operation.operation
    policy
    targetMatches := operation.targetMatches }
  pure {
    precondition := guard
    operation := alteredOperation
  }

private def collectRows? : List (Option NumericRow) → Option (List NumericRow)
  | [] => some []
  | some row :: remaining => (row :: ·) <$> collectRows? remaining
  | none :: _ => none

private def tableError? (rows : List (Option NumericRow)) :
    Option NumericComputationTableError := do
  let alternatives ← collectRows? rows
  match certifyNumericComputationTable alternatives with
  | .error error => some error
  | .ok _ => none

private def tableOutcome? (rows : List (Option NumericRow))
    (input : ScalarComputationContext := context) :
    Option NumericTargetCheckResult := do
  let alternatives ← collectRows? rows
  let table ← (certifyNumericComputationTable alternatives).toOption
  (table.evaluate input).toOption

private def tableDeclaringGroups? (rows : List (Option NumericRow)) :
    Option (List GroupPath) := do
  let alternatives ← collectRows? rows
  let table ← (certifyNumericComputationTable alternatives).toOption
  pure table.declaringGroups

/- Construction rejects empty input and the first row that changes target or complete policy. -/
example :
    tableError? [] = some .empty ∧
    tableError? [
      literalRow? (.fieldNotFilled laterId) targetId 1,
      literalRow? (.fieldNotFilled laterId) sourceId 2] =
        some (.targetMismatch 2 targetId sourceId) ∧
    tableError? [
      literalRow? (.fieldNotFilled laterId) targetId 1,
      alteredPolicyRow? (.fieldNotFilled laterId)] =
        some (.targetPolicyMismatch 2) := by
  native_decide

/- Same-target table assembly retains each row's definition placement even though target-owned runtime
evaluation does not consume it. -/
example :
    tableDeclaringGroups? [
      literalRow? (.fieldFilled sourceId) targetId 1,
      literalRowAt? ["Rules"] (.fieldNotFilled sourceId) targetId 2] =
      some [["Root"], ["Rules"]] := by
  native_decide

/- Guard admission is model-relative, and a target-presence guard is rejected independently of the checked expression. -/
example :
    tableError? [literalRow? (.fieldNotFilled 999) targetId 1] =
        some (.guardNotAdmitted 1) ∧
    tableError? [literalRow? (.fieldNotFilled targetId) targetId 1] =
        some (.guardTargetReference 1) := by
  native_decide

/- A false guard crosses row boundaries, but the first selected operation ends the scan even on numeric domain failure. -/
example :
    tableOutcome? [
      literalRow? (.fieldFilled laterId) targetId 1,
      literalRow? (.fieldNotFilled laterId) targetId 3] =
        some (.supported (.accepted { unscaled := 3, scale := 0 })) ∧
    tableOutcome? [
      divisionRow? (.fieldNotFilled laterId),
      literalRow? (.fieldNotFilled laterId) targetId 3] =
        some (.supported (.invalidNoValue .calculationValue)) := by
  native_decide

/- No selected guard is clean no-value; a poison reached during selection stops before a later holding row. -/
example :
    tableOutcome? [
      literalRow? (.fieldFilled sourceId) targetId 1,
      literalRow? (.fieldFilled laterId) targetId 3] =
        some (.supported .noValue) ∧
    tableOutcome? [
      literalRow? (.fieldFilled laterId) targetId 1,
      literalRow? (.fieldNotFilled sourceId) targetId 3]
      (context (later := (checkedNumber .empty).withFinding .malformed)) =
        some (.supported (.inheritedPoison .malformed)) := by
  native_decide

end A12Kernel.Conformance.NumericComputation.Table
