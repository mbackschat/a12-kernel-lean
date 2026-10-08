import A12Kernel.Semantics.HavingCollectionCount

namespace A12Kernel

/-- Declared capacity affects validation movement but cannot change computation's count or
its reached read failure. The conformance module separates the validation non-law. -/
theorem havingFilledFields_computation_capacity_independent
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame)
    (slots : List (HavingFieldListSlot HavingPresenceRef)) (left right : Option Nat) :
    HavingCollectionCount.evaluate .computation context frame (.filledFields slots left) =
      HavingCollectionCount.evaluate .computation context frame (.filledFields slots right) := by
  rfl

end A12Kernel
