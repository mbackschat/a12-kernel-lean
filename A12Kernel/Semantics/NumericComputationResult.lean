import A12Kernel.Cell

/-! # Numeric computation-expression results

This operation-neutral result sits between numeric expression evaluation and every later computation consumer. It keeps an ordinary value, arithmetic domain failure, and inherited computation-read poison distinct.
-/

namespace A12Kernel

/-- The numeric expression result before any computed-target policy is applied. Number has no clean no-value arm: an empty Number operand contributes the real value zero. -/
inductive NumericComputationResult where
  | value (amount : Rat)
  | domainFailure
  | poison (cause : FormalCause)
  deriving Repr, DecidableEq

end A12Kernel
