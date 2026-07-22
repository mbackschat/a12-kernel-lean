import A12Kernel.Semantics.StringFieldPolicy

/-! # Declaration-owned String formal-policy laws -/

namespace A12Kernel

/-- Empty String input bypasses every format bound and remains semantic emptiness. -/
@[simp] theorem stringFieldPolicy_checkText_empty (policy : StringFieldPolicy) :
    policy.checkText "" = .ok none := by
  rfl

/-- A forbidden raw CR/LF wins before normalization and both length checks. -/
theorem stringFieldPolicy_forbiddenLineBreak_preemptsLength
    (policy : StringFieldPolicy) (text : String)
    (nonempty : text.isEmpty = false)
    (forbidden : policy.lineBreaksPermitted = false)
    (hasBreak : containsLineBreak text = true) :
    policy.checkText text = .error .lineBreak := by
  simp [StringFieldPolicy.checkText, nonempty, forbidden, hasBreak]

/-- A successful nonempty policy check is cached exactly once through the shared checked-cell boundary. -/
theorem stringFieldPolicy_checkRaw_success_exact
    (policy : StringFieldPolicy) (text checked : String)
    (success : policy.checkText text = .ok (some checked)) :
    policy.checkRaw (.parsed (.str text)) = {
      rawPresent := true
      parsed := some (.str checked)
      findings := [] } := by
  simp [StringFieldPolicy.checkRaw, StringFieldPolicy.classifyValue, success]

/-- Every ordinary String policy failure enters the one checked-cell invalidity channel. -/
theorem stringFieldPolicy_checkRaw_failure_exact
    (policy : StringFieldPolicy) (text : String) (error : StringFieldError)
    (failure : policy.checkText text = .error error) :
    policy.checkRaw (.parsed (.str text)) = {
      rawPresent := true
      parsed := none
      findings := [.declaredConstraint] } := by
  cases error <;>
    simp [StringFieldPolicy.checkRaw, StringFieldPolicy.classifyValue, failure,
      StringFieldError.toBaseFormalCause, BaseFormalCause.toFormalCause]

end A12Kernel
