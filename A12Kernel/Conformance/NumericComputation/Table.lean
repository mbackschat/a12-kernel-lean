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

private def unguardedLiteralRow? (target : FieldId)
    (value : Rat) : Option NumericRow := do
  let operation ← operation? target
    (.literal { value, authoredScale := 0 })
  pure {
    precondition := none
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

/- Only a sole alternative may omit its precondition, and it selects directly without reading a guard field. -/
example :
    tableOutcome? [unguardedLiteralRow? targetId 3] =
      some (.supported (.accepted { unscaled := 3, scale := 0 })) ∧
    tableError? [unguardedLiteralRow? targetId 3,
      literalRow? (.fieldNotFilled laterId) targetId 4] =
        some (.unguardedAlternative 1) ∧
    tableError? [literalRow? (.fieldNotFilled laterId) targetId 3,
      unguardedLiteralRow? targetId 4] = some (.unguardedAlternative 2) := by
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

/- A guard reading its own target draws the reference class, in the only alternative and in a later
one, while an inadmissible guard claims none
([checkpoint](../../../docs/sources/evaluation-and-application-routes.md#src-join-operators-and-guards)). -/
example :
    (tableError? [literalRow? (.fieldNotFilled targetId) targetId 1]).bind (·.diagnostic?) =
        some .errorReferenceToCalculatedField ∧
    (tableError? [literalRow? (.fieldFilled sourceId) targetId 1,
        literalRow? (.fieldFilled targetId) targetId 2]).bind (·.diagnostic?) =
        some .errorReferenceToCalculatedField ∧
    (tableError? [literalRow? (.fieldNotFilled 999) targetId 1]).bind (·.diagnostic?) = none := by
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

/-- The fixture beside a scale-2 Number, so one alternative's scale gate can fail. -/
private def fractionModel : FlatModel :=
  { model with fields := model.fields ++
      [{ numberDeclaration 35 "Frac" with policy := { kind := .number { scale := 2, signed := true } } }] }

/-- The class a whole two-alternative computation draws, guarded on `Source` and `Later`, or the
refusal's arm where it projects none. -/
private def computationClass (first second : AuthoredNumericExpr SurfaceNumericAtom)
    (firstGuard : ComputationCondition := .fieldFilled sourceId) : String :=
  match elaborateNumericTargetComputationTable fractionModel ["Root"] targetId
      [(some firstGuard, first), (some (.fieldFilled laterId), second)] with
  | .ok _ => "admitted"
  | .error error =>
      (error.diagnostic?.map (·.kernelCode)).getD ("none:" ++ (reprStr error).takeWhile (!·.isWhitespace))

/- The Kernel asks every alternative's other gates before a read of the target, so a self-read in one
alternative beside a scale mismatch or a second unbraced division in another draws that other class
in either order, and beside a later unresolved name that name's refusal; beside a clean alternative,
and from a guard, the self-read draws its own class
([checkpoint](../../../docs/sources/evaluation-and-application-routes.md#src-join-operators-and-guards),
`settle.tsv` A01 to A10). -/
example :
    let target := surfaceField ["Root"] "Target"
    let source := surfaceField ["Root"] "Source"
    let later := surfaceField ["Root"] "Later"
    let frac := surfaceField ["Root"] "Frac"
    let two : AuthoredNumericExpr SurfaceNumericAtom := .literal { value := 2, authoredScale := 0 }
    let oneHalf : AuthoredNumericExpr SurfaceNumericAtom := .literal { value := 3 / 2, authoredScale := 1 }
    let divisions : AuthoredNumericExpr SurfaceNumericAtom := .binary .divide (.binary .divide source later) source
    [computationClass (.binary .multiply target two) (.binary .multiply source oneHalf),
      computationClass (.binary .multiply source oneHalf) (.binary .multiply target two),
      computationClass target frac, computationClass frac target,
      computationClass target divisions, computationClass divisions target,
      computationClass target later, computationClass source frac,
      computationClass source frac (firstGuard := .fieldFilled targetId),
      computationClass source later (firstGuard := .fieldFilled targetId),
      computationClass source later] =
      ["MVK_INVALID_COMPARE_DEC_PLACES", "MVK_INVALID_COMPARE_DEC_PLACES",
        "MVK_INVALID_COMPARE_DEC_PLACES", "MVK_INVALID_COMPARE_DEC_PLACES",
        "MVK_TOO_MANY_DIV_FOR_CALC", "MVK_TOO_MANY_DIV_FOR_CALC",
        "MVK_ERROR_REFERENCE_TO_CALCULATED_FIELD", "MVK_INVALID_COMPARE_DEC_PLACES",
        "MVK_INVALID_COMPARE_DEC_PLACES", "MVK_ERROR_REFERENCE_TO_CALCULATED_FIELD", "admitted"] ∧
    (match elaborateNumericTargetComputationTable fractionModel ["Root"] targetId
        [(some (.fieldFilled sourceId), target),
          (some (.fieldFilled laterId), surfaceField ["Root"] "Nope")] with
      | .error (.operation 2 (.resolve _)) => true
      | _ => false) = true := by
  native_decide

end A12Kernel.Conformance.NumericComputation.Table
