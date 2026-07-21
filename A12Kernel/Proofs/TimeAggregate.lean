import A12Kernel.Proofs.DateAggregate
import A12Kernel.Proofs.TimeComparison
import A12Kernel.Semantics.TimeAggregate

/-! # Resolved time-of-day extremum laws -/

namespace A12Kernel

/-- On a strict time pair, minimum selects the earlier time and maximum the later time. -/
theorem timeExtremum_select_of_before (left right : TimeOfDay)
    (before : TemporalComparisonOp.before.holdsTime left right = true) :
    TemporalExtremumOp.minimum.selectTime left right = left ∧
      TemporalExtremumOp.maximum.selectTime left right = right := by
  have reverse : TemporalComparisonOp.before.holdsTime right left = false := by
    simpa [TemporalComparisonOp.holdsTime] using
      timeComparison_before_excludes_after left right before
  simp [TemporalExtremumOp.selectTime, before, reverse]

/-- Time selection never manufactures a value outside its two inputs. -/
theorem timeExtremum_select_eq_left_or_right (op : TemporalExtremumOp)
    (left right : TimeOfDay) :
    op.selectTime left right = left ∨ op.selectTime left right = right := by
  cases op <;> simp only [TemporalExtremumOp.selectTime] <;>
    split <;> simp_all

/-- A Time extremum over no resolved operands has no synthetic value. -/
theorem timeExtremum_empty (op : TemporalExtremumOp)
    (hasUninstantiatedTail hasHaving : Bool) :
    evalTimeExtremumAggregate op {
      operands := []
      hasUninstantiatedTail
      hasHaving
    } = .notEvaluated := by
  exact temporalExtremum_empty op.selectTime hasUninstantiatedTail hasHaving

/-- A reached formally unavailable Time operand aborts before every suffix. -/
theorem timeExtremum_unknown_head (op : TemporalExtremumOp)
    (cause : FormalCause) (operands : List (SimpleComparisonOperand TimeOfDay))
    (hasUninstantiatedTail hasHaving : Bool) :
    evalTimeExtremumAggregate op {
      operands := .unknown cause :: operands
      hasUninstantiatedTail
      hasHaving
    } = .unknown cause := by
  exact temporalExtremum_unknown_head op.selectTime cause operands
    hasUninstantiatedTail hasHaving

/-- One fixed time with no structural missing source remains fixed. -/
theorem timeExtremum_fixed_singleton (op : TemporalExtremumOp)
    (value : TimeOfDay) :
    evalTimeExtremumAggregate op {
      operands := [.value value true]
      hasUninstantiatedTail := false
      hasHaving := false
    } = .value value true := by
  exact temporalExtremum_fixed_singleton op.selectTime value

/-- Omitted-tail missingness reaches the established Time comparison polarity through the shared fold. -/
theorem timeExtremum_tail_comparison_firing (op : TemporalExtremumOp)
    (comparison : TemporalComparisonOp) (selected expected : TimeOfDay)
    (holds : comparison.holdsTime selected expected = true) :
    comparison.evalTime
        (evalTimeExtremumAggregate op {
          operands := [.value selected true]
          hasUninstantiatedTail := true
          hasHaving := false
        })
        (.value expected true) = .fired .omission := by
  simpa [evalTimeExtremumAggregate, evalTemporalExtremumAggregate,
    scanTemporalExtremumOperands, TemporalComparisonOp.evalTime] using
      evalSymmetricComparison_missing_firing comparison.holdsTime
        selected expected false true (by decide) holds

end A12Kernel
