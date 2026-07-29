import A12Kernel.Semantics.ScalarText

/-! # Canonical stored Boolean and Confirm text laws -/

namespace A12Kernel

/-- Every rejected stored Boolean token reaches validation as the exact Boolean formal cause. -/
theorem classifiedStoredBoolean_rejection_observes_unknown
    (text : String)
    (rejected :
      classifyStoredBooleanText text = .rejected .booleanToken) :
    observeCell .validation
        (formalCheck { kind := .boolean }
          (classifyStoredBooleanText text)) =
      .unknown .booleanToken := by
  rw [rejected]
  rfl

/-- Every rejected stored Confirm token reaches computation as the exact Confirm poison cause. -/
theorem classifiedStoredConfirm_rejection_observes_poison
    (text : String)
    (rejected :
      classifyStoredConfirmText text = .rejected .confirmToken) :
    observeCell .computation
        (formalCheck { kind := .confirm }
          (classifyStoredConfirmText text)) =
      .poison .confirmToken := by
  rw [rejected]
  rfl

/-- No stored text can manufacture the comparison-only false Confirm value. -/
theorem classifyStoredConfirmText_ne_false (text : String) :
    classifyStoredConfirmText text ≠ .parsed (.conf false) := by
  by_cases empty : text = ""
  · simp [classifyStoredConfirmText, empty]
  · by_cases trueToken : text = "true"
    · simp [classifyStoredConfirmText, trueToken]
    · simp [classifyStoredConfirmText, empty, trueToken]

end A12Kernel
