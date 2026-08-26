import A12Kernel.Elaboration.TimeFromDateTimeComputation
import A12Kernel.Proofs.TimeComputation
import A12Kernel.Proofs.ValueAsDateTimeExtraction

/-! # Checked scalar `TimeFromDateTime` computation laws -/

namespace A12Kernel

/-- A present complete DateTime reaches exact target rendering through its retained wall clock alone. -/
theorem timeFromDateTimeComputation_value
    (operation : CheckedTimeFromDateTimeComputation model)
    (input : CheckedDocument model)
    (instant : Instant) (date : DateParts) (clock : TimeOfDay)
    (basis : DateCalendarBasis)
    (read : input.read {
      field := operation.source.source.id, path := [] } = .ok cell)
    (observed : observeCell .computation cell =
      .value (.temporal (.dateTime instant date clock basis))) :
    operation.evaluateOutcome input =
      .ok (.accepted (operation.target.format.render clock)) := by
  have sourceRead :
      operation.source.readTime .computation input =
        .ok (.value clock false) := by
    unfold CheckedDateTimeSource.readTime readTimeFromDateTimeSource
      readTimeFromDateTimeSourceAt
    rw [read]
    simp only [Except.mapError, Bind.bind, Except.bind]
    rw [observed]
    rfl
  have operandRead :
      operation.evaluateOperand input = .ok (.value clock) := by
    unfold CheckedTimeFromDateTimeComputation.evaluateOperand
    rw [sourceRead]
    simp [Except.map, ValueAsDateTimeTimeOperand.asTimeComputationResult]
  unfold CheckedTimeFromDateTimeComputation.evaluateOutcome
  rw [operandRead]
  simp [Except.map, CheckedTimeTarget.evaluate]

end A12Kernel
