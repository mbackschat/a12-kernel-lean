import A12Kernel.Semantics.LegalCharset

/-! # A12Kernel.Proofs.LegalCharset — supported-character laws

Runtime scanning and checked-cell propagation begin with an already-admitted bounded representation.
-/

namespace A12Kernel

/-- The default policy is exactly the non-supplementary scalar test over the complete input. -/
theorem legalCharset_defaultBmp_accepts_iff (value : String) :
    LegalCharset.defaultBmp.accepts value =
      value.toList.all (fun character => character.toNat < 0x10000) := by
  rfl

/-- Both default and restricted policies accept the empty input; definition emptiness and value emptiness remain distinct. -/
theorem legalCharset_accepts_empty (charset : LegalCharset) :
    charset.accepts "" = true := by
  cases charset <;> rfl

/-- The atom representation itself establishes strict scan progress. -/
theorem legalCharAtom_length_positive (atom : LegalCharAtom) :
    0 < atom.length := by
  cases atom <;> simp [LegalCharAtom.length]

/-- Every atomic entry has exactly the encoded bounded size. -/
theorem legalCharAtom_character_length (atom : LegalCharAtom) :
    atom.characters.length = atom.length := by
  cases atom <;> rfl

/-- An accepted raw input is retained exactly for the later scalar parser; this baseline does not normalize or reinterpret it. -/
theorem legalCharset_checkRawText_accepts (charset : LegalCharset)
    (value : String) (accepted : charset.accepts value = true) :
    charset.checkRawText (.parsed value) = {
      rawPresent := true
      parsed := some value
      findings := []
    } := by
  simp [LegalCharset.checkRawText, accepted]

/-- A rejected raw input is represented by the existing cross-kind formal cause. -/
theorem legalCharset_checkRawText_rejects (charset : LegalCharset)
    (value : String) (rejected : charset.accepts value = false) :
    charset.checkRawText (.parsed value) = {
      rawPresent := true
      parsed := none
      findings := [.unsupportedCharacter]
    } := by
  simp [LegalCharset.checkRawText, rejected, BaseFormalCause.toFormalCause]

/-- The same charset failure is validation-unknown and computation-poisoned through the ordinary checked-cell phase projection. -/
theorem legalCharset_rejection_phase_projection (charset : LegalCharset)
    (value : String) (rejected : charset.accepts value = false) :
    observeCell .validation (charset.checkRawText (.parsed value)) =
        .unknown .unsupportedCharacter ∧
      observeCell .computation (charset.checkRawText (.parsed value)) =
        .poison .unsupportedCharacter := by
  rw [legalCharset_checkRawText_rejects charset value rejected]
  decide

end A12Kernel
