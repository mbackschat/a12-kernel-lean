import A12Kernel.Elaboration.CheckedStarDocument
import A12Kernel.Semantics.FieldFillQuantifier

/-! # Checked plain-star filled-field counts

This boundary admits one plain starred field as the complete `NumberOfFilledFields` operand. Its evaluation domain excludes checked cells beneath declared-capacity violations, matching the exact single-level Kernel row, while in-cap emptiness and formal invalidity retain the existing validation count semantics. The partial-validation route applies the local reduced-universal account that matches the measured outcome pattern. Nested capacity and nested partial relevance are internally executable accounts with external correspondence pending. Direct lists, filters, group operands, computation, comparison movement, and raw-document execution remain outside.
-/

namespace A12Kernel

/-- Partial filled-field count evaluation distinguishes an unavailable operand extent from an evaluated count whose cells may still be formally unknown. -/
inductive PartialValidationFilledFieldCountResult where
  | nonRelevant
  | evaluated (count : FilledFieldCount)
  deriving Repr, DecidableEq

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

/-- Count a plain starred field in partial validation only when its normalized field-specific identifiers establish the complete reduced-universal extent. The gate precedes topology and cell reads. -/
def evaluatePartialFilledFieldCountValidation
    (checked : CheckedStarFieldPath model)
    (document : CheckedDocument model) (outer : Env)
    (scope : ValidationRelevanceScope) :
    Except CheckedAddressingError PartialValidationFilledFieldCountResult :=
  if checked.allRowsRelevant scope outer then do
    pure (.evaluated (← checked.evaluateFilledFieldCountValidation document outer))
  else
    pure .nonRelevant

end CheckedStarFieldPath

end A12Kernel
