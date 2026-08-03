import A12Kernel.Semantics.MessagePointer

/-! # Shared formal-message pointer laws -/

namespace A12Kernel

private theorem messagePointer_toConcretePath_map
    (path : List Nat) :
    MessagePointer.toConcretePath?
      (path.map MessageRepetitionCoordinate.concrete) = some path := by
  induction path with
  | nil =>
      rfl
  | cons index remaining inductionHypothesis =>
      simp [MessagePointer.toConcretePath?, inductionHypothesis]

/-- Embedding an exact document address and projecting it back is lossless. -/
theorem messagePointer_toCellAddr_ofCellAddr
    (address : CellAddr) :
    (MessagePointer.ofCellAddr address).toCellAddr? = some address := by
  cases address with
  | mk field path =>
      simp [MessagePointer.ofCellAddr, MessagePointer.toCellAddr?,
        messagePointer_toConcretePath_map]

end A12Kernel
