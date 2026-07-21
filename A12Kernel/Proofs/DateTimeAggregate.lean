import A12Kernel.Proofs.DateAggregate
import A12Kernel.Proofs.DateTimeComparison
import A12Kernel.Semantics.DateTimeAggregate

/-! # Resolved DateTime instant-extremum laws -/

namespace A12Kernel

/-- On a strict instant pair, minimum selects the earlier instant and maximum the later instant. -/
theorem dateTimeExtremum_select_of_before (left right : Instant)
    (before : DateComparisonOp.before.holdsInstant left right = true) :
    TemporalExtremumOp.minimum.selectInstant left right = left ∧
      TemporalExtremumOp.maximum.selectInstant left right = right := by
  have reverse : DateComparisonOp.before.holdsInstant right left = false := by
    simpa [DateComparisonOp.holdsInstant] using
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
    (comparison : DateComparisonOp) (selected expected : Instant)
    (holds : comparison.holdsInstant selected expected = true) :
    comparison.evalInstant
        (evalDateTimeExtremumAggregate op {
          operands := [.value selected true]
          hasUninstantiatedTail := true
          hasHaving := false
        })
        (.value expected true) = .fired .omission := by
  simpa [evalDateTimeExtremumAggregate, evalTemporalExtremumAggregate,
    scanTemporalExtremumOperands, DateComparisonOp.evalInstant] using
      evalSymmetricComparison_missing_firing comparison.holdsInstant
        selected expected false true (by decide) holds

end A12Kernel
