import A12Kernel.Elaboration.NumericSource

namespace A12Kernel

/-- A diagnostic at this boundary identifies conversion refusal exactly, so unsupported projections and category failures cannot inherit it. -/
theorem fieldValueAsNumberSource_diagnostic_iff
    (error : FieldValueAsNumberSourceError) (diagnostic : KernelStaticDiagnostic) :
    error.diagnostic? = some diagnostic ↔
      error = .notConvertible ∧ diagnostic = .noConvertInNumber := by
  cases error <;> simp [FieldValueAsNumberSourceError.diagnostic?, eq_comm]

end A12Kernel
