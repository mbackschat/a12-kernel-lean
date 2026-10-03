import A12Kernel.Elaboration.DateConstantTarget

namespace A12Kernel

/-- Without a Base Year, the written literal and stored format must agree about year presence;
    neither yearless side is independently forbidden. -/
theorem checkedDateConstantTarget_yearAgreement
    (target : CheckedDateConstantTarget model sourceCarriesYear) :
    (sourceCarriesYear != target.carriesYear && !model.hasBaseYear) = false := by
  cases target with
  | complete target agreement =>
      cases sourceCarriesYear with
      | false =>
          have present : model.hasBaseYear = true := by simpa using agreement
          simp [CheckedDateConstantTarget.carriesYear, present]
      | true => simp [CheckedDateConstantTarget.carriesYear]
  | omittedComponent target => exact target.yearAgreement

/-- Accepted constants store the declaration's format, irrespective of the source's written year.
    Both fixed literals and the existing repeatable carrier specialize this target-owned fact. -/
theorem checkedDateConstantTarget_accepted_rendersInTargetFormat
    (target : CheckedDateConstantTarget model sourceCarriesYear) (constant : CivilDate)
    (stored : StoredDate) (accepted : target.evaluateCivil constant = .accepted stored) :
    stored = target.renderCivil constant := by
  cases hTarget : target with
  | complete target _ =>
      simp only [hTarget, CheckedDateConstantTarget.evaluateCivil,
        CheckedDateFormatTarget.evaluateCivil] at accepted
      simp only [CheckedDateConstantTarget.renderCivil]
      split at accepted
      · exact absurd accepted (by simp)
      · split at accepted
        · exact absurd accepted (by simp)
        · exact (FullDateTargetOutcome.accepted.inj accepted).symm
  | omittedComponent target =>
      simp only [hTarget, CheckedDateConstantTarget.evaluateCivil,
        CheckedOmittedComponentDateTarget.evaluateCivil] at accepted
      simp only [CheckedDateConstantTarget.renderCivil]
      split at accepted
      · exact absurd accepted (by simp)
      · split at accepted
        · exact absurd accepted (by simp)
        · exact (FullDateTargetOutcome.accepted.inj accepted).symm

end A12Kernel
