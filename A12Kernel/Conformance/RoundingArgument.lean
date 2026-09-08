import A12Kernel.Elaboration.RoundingArgument

namespace A12Kernel.Conformance.RoundingArgument

open A12Kernel

private def argumentResult (places : Option Nat) : Option String × Option Nat :=
  match checkRoundingArgument places with
  | .error diagnostic => (some diagnostic.kernelCode, none)
  | .ok places => (none, some places.val)

example :
    [none, some 0, some 14, some 15, some 2147483648,
        some 9223372036854775807, some 9223372036854775808,
        some 18446744073709551616].map argumentResult =
      [(none, some 0), (none, some 0), (none, some 14),
        (some "MVK_INVALID_DIGIT_FOR_ROUNDING", none),
        (some "MVK_INVALID_DIGIT_FOR_ROUNDING", none),
        (some "MVK_INVALID_DIGIT_FOR_ROUNDING", none),
        (some "MVK_INTERNAL_ERROR", none), (some "MVK_INTERNAL_ERROR", none)] := by
  native_decide

end A12Kernel.Conformance.RoundingArgument
