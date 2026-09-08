import A12Kernel.Semantics.NumericRounding
import A12Kernel.Elaboration.StaticDiagnostic

/-! # Authored rounding places after operand admission

The input is the exact nonnegative value of the grammar's decimal digit token, or omission. It must not be narrowed before this check. The caller retains its authored token and operand tree; lexical recognition and the earlier field/operation admission checks remain separate.

Signed-64-bit overflow and the ordinary `0..14` scale refusal have different diagnostics. Successful checking returns the existing `RoundingPlaces` certificate used by rounding expressions and evaluators.
-/

namespace A12Kernel

/-- The first nonnegative argument that overflows the signed-64-bit read in Kernel `CheckOpUtils.isSpecificationForRounding`. -/
def roundingArgumentOverflow : Nat := 2 ^ 63

def checkRoundingArgument : Option Nat → Except KernelStaticDiagnostic RoundingPlaces
  | none => .ok omittedRoundingPlaces
  | some places =>
      if roundingArgumentOverflow ≤ places then
        .error .internalError
      else
        match RoundingPlaces.ofNat? places with
        | some admitted => .ok admitted
        | none => .error .invalidDigitForRounding

end A12Kernel
