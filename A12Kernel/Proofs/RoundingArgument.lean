import A12Kernel.Elaboration.RoundingArgument

namespace A12Kernel

theorem roundingArgument_ok_iff (input : Option Nat) (places : RoundingPlaces) :
    checkRoundingArgument input = .ok places ↔ input.getD 0 = places.val := by
  cases input with
  | none => simp [checkRoundingArgument, omittedRoundingPlaces, Fin.ext_iff]
  | some value =>
      have bound := places.isLt
      by_cases overflow : roundingArgumentOverflow ≤ value
      · have different : value ≠ places.val := by
          simp only [roundingArgumentOverflow, maxRoundingPlaces] at *
          omega
        simp [checkRoundingArgument, overflow, different]
      · by_cases admitted : value < maxRoundingPlaces + 1
        · simp [checkRoundingArgument, overflow, RoundingPlaces.ofNat?, admitted,
            Fin.ext_iff]
        · have different : value ≠ places.val := by omega
          simp [checkRoundingArgument, overflow, RoundingPlaces.ofNat?, admitted,
            different]

theorem roundingArgument_overflow_iff (value : Nat) :
    checkRoundingArgument (some value) = .error .internalError ↔
      roundingArgumentOverflow ≤ value := by
  by_cases overflow : roundingArgumentOverflow ≤ value
  · simp [checkRoundingArgument, overflow]
  · cases admitted : RoundingPlaces.ofNat? value <;>
      simp [checkRoundingArgument, overflow, admitted]

theorem roundingArgument_scale_refusal_iff (value : Nat) :
    checkRoundingArgument (some value) = .error .invalidDigitForRounding ↔
      maxRoundingPlaces < value ∧ value < roundingArgumentOverflow := by
  by_cases overflow : roundingArgumentOverflow ≤ value
  · simp [checkRoundingArgument, overflow]
  · by_cases admitted : value < maxRoundingPlaces + 1
    · simp [checkRoundingArgument, overflow, RoundingPlaces.ofNat?, admitted]; omega
    · simp [checkRoundingArgument, overflow, RoundingPlaces.ofNat?, admitted]; omega

end A12Kernel
