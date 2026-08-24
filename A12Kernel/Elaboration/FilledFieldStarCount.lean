import A12Kernel.Elaboration.CheckedStarDocument
import A12Kernel.Semantics.FieldFillQuantifier

/-! # Checked plain-star filled-field counts

This boundary admits one plain starred field as the complete `NumberOfFilledFields` operand. Its evaluation domain excludes checked cells beneath declared-capacity violations, matching the exact single-level Kernel row, while in-cap emptiness and formal invalidity retain the existing validation count semantics. Nested capacity behavior is an internally executable account with external correspondence pending. Direct lists, filters, group operands, partial validation, computation, comparison movement, and raw-document execution remain outside.
-/

namespace A12Kernel

/-- Reuse the established star-path gates without introducing another checked representation. -/
def elaborateFilledFieldStarValidationSource (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceStarFieldPath) :
    Except StarPathElabError (CheckedStarFieldPath model) :=
  elaborateStarFieldPath model declaringGroup authored

namespace CheckedStarFieldPath

/-- Count one capacity-bounded plain-star field extent in full validation. Over-limit rows remain in the immutable checked document but do not enter this operator's evaluation domain. -/
def evaluateFilledFieldCountValidation
    (checked : CheckedStarFieldPath model)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError FilledFieldCount := do
  let resolved ←
    checked.resolveCheckedValidationEntityOperandCore document outer none
  pure (numberOfFilledFields
    (resolved.inCapacityAddressedCells.map fun addressed =>
      observeCell .validation addressed.cell))

end CheckedStarFieldPath

end A12Kernel
