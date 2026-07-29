import A12Kernel.Semantics.NumericInput

/-! # Stored Number input laws -/

namespace A12Kernel

@[simp] theorem numericStoredInput_formalReadText_text
    (text : String) (minimumScale : Nat) :
    (NumericStoredInput.text text).formalReadText minimumScale = text := by
  rfl

@[simp] theorem numericStoredInput_sourceIdentity_text (text : String) :
    (NumericStoredInput.text text).sourceIdentity = .nonComputedForm := by
  rfl

theorem numericInputDecimal_sourceIdentity_of_negativeScale
    (value : NumericInputDecimal) (negative : value.scale < 0) :
    value.sourceIdentity = .nonComputedForm := by
  simp [NumericInputDecimal.sourceIdentity, negative]

@[simp] theorem numericStoredInput_sourceIdentity_ofStoredNumber
    (value : StoredNumber) :
    (NumericStoredInput.ofStoredNumber value).sourceIdentity =
      .decimal value := by
  simp [NumericStoredInput.ofStoredNumber,
    NumericStoredInput.sourceIdentity,
    NumericInputDecimal.sourceIdentity]

end A12Kernel
