import A12Kernel.Elaboration.TemporalExtractorEntry

namespace A12Kernel

/-- A failed literal recognizer preempts the extractor-specific gates. -/
theorem temporalExtractorEntry_invalid_literal (family : TemporalExtractorFamily) :
    checkTemporalExtractorEntry family (.literal none) = .error .invalidDateString := by
  rfl

/-- Numeric component extractors reject every recognized direct literal, including one of a different temporal kind. -/
theorem temporalExtractorEntry_numeric_literal (kind : TemporalKind) :
    checkTemporalExtractorEntry .numeric (.literal (some kind)) = .error .noConst := by
  rfl

/-- Only recognized DateTime literals complete entry, and only for the Date- and Time-valued projections. -/
theorem temporalExtractorEntry_complete_iff
    (family : TemporalExtractorFamily) (operand : TemporalExtractorEntryOperand) :
    checkTemporalExtractorEntry family operand = .ok .complete ↔
      family ≠ .numeric ∧ operand = .literal (some .dateTime) := by
  cases family <;> cases operand with
  | nonliteral => simp [checkTemporalExtractorEntry]
  | literal kind => cases kind with
    | none => simp [checkTemporalExtractorEntry]
    | some kind => cases kind <;> simp [checkTemporalExtractorEntry]

/-- Nonliteral syntax leaves the independent source-admission checks outstanding. -/
theorem temporalExtractorEntry_continuation_iff
    (family : TemporalExtractorFamily) (operand : TemporalExtractorEntryOperand) :
    checkTemporalExtractorEntry family operand = .ok .nonliteralSource ↔
      operand = .nonliteral := by
  cases family <;> cases operand with
  | nonliteral => simp [checkTemporalExtractorEntry]
  | literal kind => cases kind with
    | none => simp [checkTemporalExtractorEntry]
    | some kind => cases kind <;> simp [checkTemporalExtractorEntry]

end A12Kernel
