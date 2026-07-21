import A12Kernel.Proofs.ScalarEquality
import A12Kernel.Semantics.TimeComparison

/-! # Resolved time-of-day comparison laws -/

namespace A12Kernel

/-- Valid decoded times have a unique seconds-since-midnight coordinate. -/
theorem timeOfDay_secondsSinceMidnight_injective :
    Function.Injective TimeOfDay.secondsSinceMidnight := by
  intro left right same
  rcases left with ⟨leftHour, leftMinute, leftSecond, leftValid⟩
  rcases right with ⟨rightHour, rightMinute, rightSecond, rightValid⟩
  simp only [TimeOfDay.secondsSinceMidnight] at same
  congr <;> omega

/-- Resolved Time equality fires exactly on identical decoded times. -/
theorem timeComparison_equal_iff (left right : TimeOfDay) :
    TemporalComparisonOp.equal.holdsTime left right = true ↔ left = right := by
  simp [TemporalComparisonOp.holdsTime]

/-- Resolved Time inequality fires exactly on distinct decoded times. -/
theorem timeComparison_notEqual_iff (left right : TimeOfDay) :
    TemporalComparisonOp.notEqual.holdsTime left right = true ↔ left ≠ right := by
  simp [TemporalComparisonOp.holdsTime]

/-- Resolved Time equality agrees exactly with equality of the ordering coordinate. -/
theorem timeComparison_equal_iff_sameCoordinate (left right : TimeOfDay) :
    TemporalComparisonOp.equal.holdsTime left right = true ↔
      left.secondsSinceMidnight = right.secondsSinceMidnight := by
  rw [timeComparison_equal_iff]
  exact timeOfDay_secondsSinceMidnight_injective.eq_iff.symm

/-- Exchanging times and the directional operator preserves every resolved comparison result. -/
theorem timeComparison_swapped (op : TemporalComparisonOp)
    (left right : TimeOfDay) :
    op.swapped.holdsTime left right = op.holdsTime right left := by
  cases op with
  | equal => exact Bool.beq_comm
  | notEqual => exact congrArg (!·) Bool.beq_comm
  | before | beforeOrEqual | after | afterOrEqual => rfl

/-- A strict time-of-day comparison cannot hold in both directions. -/
theorem timeComparison_before_excludes_after (left right : TimeOfDay)
    (before : TemporalComparisonOp.before.holdsTime left right = true) :
    TemporalComparisonOp.after.holdsTime left right = false := by
  simp [TemporalComparisonOp.holdsTime] at before ⊢
  omega

/-- Operand exchange plus the matching directional operator preserves classified Time verdicts and polarity. -/
theorem timeComparison_eval_swapped (op : TemporalComparisonOp)
    (left right : SimpleComparisonOperand TimeOfDay) :
    op.swapped.evalTime left right = op.evalTime right left := by
  exact evalSymmetricComparison_swapped op.holdsTime op.swapped.holdsTime
    (timeComparison_swapped op) left right

/-- A true comparison over clean typed Time observations delegates to the existing fixed-value verdict law. -/
theorem timeComparison_evalObserved_clean_firing (op : TemporalComparisonOp)
    (left right : TimeOfDay) (holds : op.holdsTime left right = true) :
    op.evalTimeObserved (.value left) (.value right) = .fired .value := by
  exact evalSymmetricComparison_fixed_firing op.holdsTime left right holds

/-- Typed Time unavailability remains UNKNOWN through the shared observation classifier. -/
theorem timeComparison_evalObserved_unknown_left (op : TemporalComparisonOp)
    (cause : FormalCause) (right : CellObservation TimeOfDay) :
    op.evalTimeObserved (.unknown cause) right = .unknown := by
  exact evalSymmetricComparison_unknown_left op.holdsTime cause
    right.asValidationSimpleOperand

end A12Kernel
