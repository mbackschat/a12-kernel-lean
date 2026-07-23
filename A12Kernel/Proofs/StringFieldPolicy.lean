import A12Kernel.Semantics.StringFieldPolicy

/-! # Declaration-owned String formal-policy laws -/

namespace A12Kernel

/-- Empty String input bypasses every format bound and remains semantic emptiness. -/
@[simp] theorem stringFieldPolicy_checkText_empty (policy : StringFieldPolicy) :
    policy.checkText "" = .ok none := by
  rfl

/-- Empty String input also bypasses an effective declared matcher. -/
@[simp] theorem stringFieldPolicy_checkTextWithPattern_empty
    (policy : StringFieldPolicy) (wholeValueMatches? : Option (String → Bool)) :
    policy.checkTextWithPattern wholeValueMatches? "" = .ok none := by
  rfl

/-- A forbidden raw CR/LF wins before normalization, the declared pattern, and both length checks. -/
theorem stringFieldPolicy_forbiddenLineBreak_preemptsLength
    (policy : StringFieldPolicy) (text : String)
    (nonempty : text.isEmpty = false)
    (forbidden : policy.lineBreaksPermitted = false)
    (hasBreak : containsLineBreak text = true) :
    policy.checkText text = .error .lineBreak := by
  simp [StringFieldPolicy.checkText, StringFieldPolicy.checkTextWithPattern,
    nonempty, forbidden, hasBreak]

/-- With line breaks admitted, a failed normalized matcher precedes every length decision. -/
theorem stringFieldPolicy_pattern_preemptsLength
    (policy : StringFieldPolicy) (wholeValueMatches : String → Bool)
    (text : String)
    (nonempty : text.isEmpty = false)
    (permitted : policy.lineBreaksPermitted = true)
    (mismatch :
      wholeValueMatches (normalizeEvaluatedString text) = false) :
    policy.checkTextWithPattern (some wholeValueMatches) text =
      .error .pattern := by
  simp [StringFieldPolicy.checkTextWithPattern, nonempty, permitted, mismatch]

/-- A successful nonempty policy-and-pattern check is cached exactly once through the shared checked-cell boundary. -/
theorem stringFieldPolicy_checkRawWithPattern_success_exact
    (policy : StringFieldPolicy)
    (wholeValueMatches? : Option (String → Bool)) (text checked : String)
    (success :
      policy.checkTextWithPattern wholeValueMatches? text =
        .ok (some checked)) :
    policy.checkRawWithPattern wholeValueMatches? (.parsed (.str text)) = {
      rawPresent := true
      parsed := some (.str checked)
      findings := [] } := by
  simp [StringFieldPolicy.checkRawWithPattern,
    StringFieldPolicy.classifyValueWithPattern, success]

/-- Every ordinary String policy-or-pattern failure enters the one checked-cell invalidity channel. -/
theorem stringFieldPolicy_checkRawWithPattern_failure_exact
    (policy : StringFieldPolicy)
    (wholeValueMatches? : Option (String → Bool))
    (text : String) (error : StringFieldError)
    (failure :
      policy.checkTextWithPattern wholeValueMatches? text = .error error) :
    policy.checkRawWithPattern wholeValueMatches? (.parsed (.str text)) = {
      rawPresent := true
      parsed := none
      findings := [.declaredConstraint] } := by
  cases error <;>
    simp [StringFieldPolicy.checkRawWithPattern,
      StringFieldPolicy.classifyValueWithPattern, failure,
      StringFieldError.toBaseFormalCause, BaseFormalCause.toFormalCause]

/-- The ordinary no-pattern checked-cell route is the exact specialization of the shared format checker. -/
theorem stringFieldPolicy_checkRaw_success_exact
    (policy : StringFieldPolicy) (text checked : String)
    (success : policy.checkText text = .ok (some checked)) :
    policy.checkRaw (.parsed (.str text)) = {
      rawPresent := true
      parsed := some (.str checked)
      findings := [] } := by
  apply stringFieldPolicy_checkRawWithPattern_success_exact
  exact success

/-- The ordinary no-pattern failure route is the same specialization. -/
theorem stringFieldPolicy_checkRaw_failure_exact
    (policy : StringFieldPolicy) (text : String) (error : StringFieldError)
    (failure : policy.checkText text = .error error) :
    policy.checkRaw (.parsed (.str text)) = {
      rawPresent := true
      parsed := none
      findings := [.declaredConstraint] } := by
  apply stringFieldPolicy_checkRawWithPattern_failure_exact
  exact failure

end A12Kernel
