import A12Kernel.Proofs.DateAggregate
import A12Kernel.Proofs.DateTimeComparison
import A12Kernel.Semantics.DateTimeAggregate

/-! # Resolved DateTime instant-extremum laws -/

namespace A12Kernel

/-- On a strict instant pair, minimum selects the earlier instant and maximum the later instant. -/
theorem dateTimeExtremum_select_of_before (left right : Instant)
    (before : TemporalComparisonOp.before.holdsInstant left right = true) :
    TemporalExtremumOp.minimum.selectInstant left right = left ∧
      TemporalExtremumOp.maximum.selectInstant left right = right := by
  have reverse : TemporalComparisonOp.before.holdsInstant right left = false := by
    simpa [TemporalComparisonOp.holdsInstant] using
      dateTimeComparison_before_excludes_after left right before
  simp [TemporalExtremumOp.selectInstant, before, reverse]

/-- Instant selection never manufactures a value outside its two inputs. -/
theorem dateTimeExtremum_select_eq_left_or_right (op : TemporalExtremumOp)
    (left right : Instant) :
    op.selectInstant left right = left ∨ op.selectInstant left right = right := by
  cases op <;> simp only [TemporalExtremumOp.selectInstant] <;>
    split <;> simp_all

/-- A DateTime extremum over no resolved operands has no synthetic instant. -/
theorem dateTimeExtremum_empty (op : TemporalExtremumOp)
    (hasUninstantiatedTail hasHaving : Bool) :
    evalDateTimeExtremumAggregate op {
      operands := []
      hasUninstantiatedTail
      hasHaving
    } = .notEvaluated := by
  exact temporalExtremum_empty op.selectInstant hasUninstantiatedTail hasHaving

/-- A reached formally unavailable DateTime operand aborts before every suffix. -/
theorem dateTimeExtremum_unknown_head (op : TemporalExtremumOp)
    (cause : FormalCause) (operands : List (SimpleComparisonOperand Instant))
    (hasUninstantiatedTail hasHaving : Bool) :
    evalDateTimeExtremumAggregate op {
      operands := .unknown cause :: operands
      hasUninstantiatedTail
      hasHaving
    } = .unknown cause := by
  exact temporalExtremum_unknown_head op.selectInstant cause operands
    hasUninstantiatedTail hasHaving

/-- One fixed instant with no structural missing source remains fixed. -/
theorem dateTimeExtremum_fixed_singleton (op : TemporalExtremumOp)
    (value : Instant) :
    evalDateTimeExtremumAggregate op {
      operands := [.value value true]
      hasUninstantiatedTail := false
      hasHaving := false
    } = .value value true := by
  exact temporalExtremum_fixed_singleton op.selectInstant value

/-- Omitted-tail missingness reaches the established DateTime comparison polarity through the shared fold. -/
theorem dateTimeExtremum_tail_comparison_firing (op : TemporalExtremumOp)
    (comparison : TemporalComparisonOp) (selected expected : Instant)
    (holds : comparison.holdsInstant selected expected = true) :
    comparison.evalInstant
        (evalDateTimeExtremumAggregate op {
          operands := [.value selected true]
          hasUninstantiatedTail := true
          hasHaving := false
        })
        (.value expected true) = .fired .omission := by
  simpa [evalDateTimeExtremumAggregate, evalTemporalExtremumAggregate,
    scanTemporalExtremumOperands, TemporalComparisonOp.evalInstant] using
      evalSymmetricComparison_missing_firing comparison.holdsInstant
        selected expected false true (by decide) holds

/-- The instant projection obeys its siblings' rule: **only** an absent cell is skipped. Stated as an
equivalence because the useful direction is the reverse one — nothing else may reach the fold as an
absent operand, so a malformed payload cannot be silently dropped and read as unfilled. The payload
arms differ from the Date and Time families', which makes this a third obligation rather than a
specialization of either. -/
theorem asDateTimeExtremumOperand_notEvaluated_iff_empty
    (observation : CellObservation) :
    observation.asDateTimeExtremumOperand = .notEvaluated ↔ observation = .empty := by
  constructor
  · intro projected
    cases observation with
    | empty => rfl
    | value payload =>
        cases payload with
        | temporal value => cases value <;> cases projected
        | _ => cases projected
    | unknown _ => cases projected
    | poison _ => cases projected
  · intro isEmpty
    subst isEmpty
    rfl

/-- The projection carries a formal cause through verbatim in either phase, so the fold's abort
reports the cell's own cause rather than a generic one. -/
theorem asDateTimeExtremumOperand_preserves_cause (cause : FormalCause) :
    (CellObservation.unknown (α := Value) cause).asDateTimeExtremumOperand =
        .unknown cause ∧
      (CellObservation.poison (α := Value) cause).asDateTimeExtremumOperand =
        .unknown cause := by
  exact ⟨rfl, rfl⟩

end A12Kernel
