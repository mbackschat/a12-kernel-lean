import A12Kernel.Elaboration.DateRangeInput

/-! # Checked stored DateRange input laws

These laws connect declaration admission to stored-input capability. They are internal
consequences of the two owners, not claims about the Kernel's own dispatch.
-/

namespace A12Kernel

/-- Every statically admitted declaration pair selects exactly one stored-input profile. The `unsupportedPolicy` refusal therefore has no witness among admitted declarations, so it stays fail-closed for callers that bypass declaration validation rather than being claimed unreachable. -/
theorem dateRangeInputFormat_ofPolicy_isSome_of_admitted
    (policy : DateRangeDeclarationPolicy)
    (admitted : policy.admitted = true) :
    (DateRangeInputFormat.ofPolicy? policy).isSome = true := by
  unfold DateRangeDeclarationPolicy.admitted at admitted
  split at admitted <;>
    simp_all [DateRangeInputFormat.ofPolicy?, DateRangeFormat.ofPolicy?]

end A12Kernel
