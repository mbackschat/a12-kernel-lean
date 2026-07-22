import A12Kernel.Elaboration.LegalCharset

/-! # A12Kernel.Proofs.LegalCharsetElaboration — definition-admission laws -/

namespace A12Kernel

/-- An empty/absent `supportedCharacters` declaration always selects the default BMP policy, independently of the injected cluster capability. -/
theorem admitSupportedCharacters_empty
    (clustersOf : String → List String) :
    admitSupportedCharacters clustersOf [] = .ok .defaultBmp := by
  rfl

/-- An empty entry is malformed rather than another spelling of the default policy. -/
theorem admitSupportedCharacters_emptyEntry
    (clustersOf : String → List String) :
    admitSupportedCharacters clustersOf [""] = .error (.emptyEntry 0) := by
  rfl

end A12Kernel
