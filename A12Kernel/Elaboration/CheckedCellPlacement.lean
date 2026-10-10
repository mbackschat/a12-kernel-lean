import A12Kernel.Document
import A12Kernel.Semantics.NumericInput

namespace A12Kernel

structure CheckedCellPlacement where
  address : CellAddr
  cell : CheckedCell
  /-- The exact selected Number input regime. Non-Number and empty placements carry `none`. -/
  numericInput : Option NumericStoredInput := none
  /-- The selected Number formal-read text, including on a formally rejected Number placement. Non-Number and empty placements carry `none`. -/
  numericFormalReadText : Option String := none
  /-- The stored text this placement's cell was read from, which a reader pairs with that cell: a
  token scan's selected text and a partial Date's spelling. It travels with the cell, so a document
  overlaid with a completed target reads that target's rendering rather than the source's text.
  A placement with no text carries `none`. -/
  storedText : Option String := none
  deriving Repr, DecidableEq

end A12Kernel
