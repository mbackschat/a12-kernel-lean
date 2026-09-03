import A12Kernel.Elaboration.CheckedStarDocument
import A12Kernel.Elaboration.Correlation
import A12Kernel.Semantics.FieldFillQuantifier

/-! # Checked plain- and filtered-star filled-field counts

This boundary admits one starred field, plain or carrying a row-local `Having`, as the complete `NumberOfFilledFields` operand. Its evaluation domain excludes checked cells beneath declared-capacity violations, matching the exact single-level Kernel row, while in-cap emptiness and formal invalidity retain the existing validation count semantics. A filter selects candidates before any counted cell is read, so a non-true row drops and the count answers over the survivors instead of becoming unavailable.

The partial-validation route applies the local reduced-universal account that matches the measured outcome pattern, and covers the **plain** star only: no observation places a filtered count under partial coverage, so that arm is absent rather than assumed from the token family's `skippedHaving` rule. Nested capacity, filtered capacity interaction, and nested partial relevance are internally executable or open accounts with external correspondence pending. Direct lists, group operands, computation, comparison movement, and raw-document execution remain outside.
-/

namespace A12Kernel

/-- Partial filled-field count evaluation distinguishes an unavailable operand extent, a rule the
    coverage gate skipped because its operand carries a filter, and an evaluated count whose cells
    may still be formally unknown. -/
inductive PartialValidationFilledFieldCountResult where
  | nonRelevant
  | skippedHaving
  | evaluated (count : FilledFieldCount)
  deriving Repr, DecidableEq

/-- Reuse the established star-path gates without introducing another checked representation. -/
def elaborateFilledFieldStarValidationSource (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceStarFieldPath) :
    Except StarPathElabError (CheckedStarFieldPath model) :=
  elaborateStarFieldPath model declaringGroup authored

namespace CheckedStarFieldPath

/-- Resolve one capacity-bounded starred extent and fold it into a count, under an optional
    row-local filter. Both public entry points below route through this one body, so the plain and
    filtered counts cannot drift apart into two accounts of the same fold. -/
private def countInCapacity (checked : CheckedStarFieldPath model)
    (document : CheckedDocument model) (outer : Env)
    (having : Option CorrelatedHaving) :
    Except CheckedAddressingError FilledFieldCount := do
  let resolved ←
    checked.resolveCheckedValidationEntityOperandCore document outer having
  pure (numberOfFilledFields
    (resolved.inCapacityAddressedCells.map fun addressed =>
      observeCell .validation addressed.cell))

/-- Count one capacity-bounded plain-star field extent in full validation. Over-limit rows remain in the immutable checked document but do not enter this operator's evaluation domain. -/
def evaluateFilledFieldCountValidation
    (checked : CheckedStarFieldPath model)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError FilledFieldCount :=
  checked.countInCapacity document outer none

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

/-- Why a filled-field count source failed to elaborate. The two arms stay separate because a
    rejected star path and a rejected filter send an author to different halves of the operand. -/
inductive FilledFieldStarCountElabError where
  | path (error : StarPathElabError)
  | having (error : CorrelationElabError)
  deriving Repr

/-- One checked `NumberOfFilledFields` star operand: the plain star plus an optional row-local
    filter. The filter type is indexed by this exact source and declaring group, so a checked filter
    cannot be paired with another star or lifted to a different rule scope. -/
structure CheckedFilledFieldStarSource (model : FlatModel) where
  private mk ::
  declaringGroup : GroupPath
  source : CheckedStarFieldPath model
  filter : Option (CheckedStarHaving model source declaringGroup)

namespace CheckedFilledFieldStarSource

/-- Whether this operand carries a filter. Consumers that must refuse a filtered operand read this
    rather than inspecting the dependent filter field. -/
def hasHaving (checked : CheckedFilledFieldStarSource model) : Bool :=
  checked.filter.isSome

/-- Elaborate one starred filled-field operand, with or without a filter, reusing the established
    star-path gates and the shared star `Having` fragment. -/
def elaborate (model : FlatModel) (declaringGroup : GroupPath)
    (authored : SurfaceStarFieldPath) (having : Option SurfaceCorrelatedHaving) :
    Except FilledFieldStarCountElabError (CheckedFilledFieldStarSource model) := do
  let source ←
    (elaborateFilledFieldStarValidationSource model declaringGroup authored).mapError .path
  match having with
  | none => pure { declaringGroup, source, filter := none }
  | some authoredHaving =>
      let filter ←
        (elaborateStarHavingCore model declaringGroup source authoredHaving).mapError .having
      pure { declaringGroup, source, filter := some filter }

/-- Count one capacity-bounded starred field extent in full validation. A filter selects candidate
    rows before any counted cell is read, so a row whose condition is not true drops with its cells
    and cannot contribute its own formal invalidity to the count. -/
def evaluateFilledFieldCountValidation
    (checked : CheckedFilledFieldStarSource model)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError FilledFieldCount :=
  checked.source.countInCapacity document outer (checked.filter.map (·.condition))

/-- Count a starred field under partial coverage. A filtered operand is skipped before topology and
    cell reads, and the skip is **unconditional**: relevance over the filter's own operand fields
    does not lift it, nor does relevance over the whole tree. An unfiltered operand falls through to
    the reduced-universal extent gate. -/
def evaluatePartialFilledFieldCountValidation
    (checked : CheckedFilledFieldStarSource model)
    (document : CheckedDocument model) (outer : Env)
    (scope : ValidationRelevanceScope) :
    Except CheckedAddressingError PartialValidationFilledFieldCountResult :=
  if checked.hasHaving then
    pure .skippedHaving
  else
    checked.source.evaluatePartialFilledFieldCountValidation document outer scope

end CheckedFilledFieldStarSource

/-- Elaborate a starred filled-field count operand. The plain and filtered surfaces share one entry
    point so a consumer never has to choose between two elaborators. -/
def elaborateFilledFieldStarSource (model : FlatModel) (declaringGroup : GroupPath)
    (authored : SurfaceStarFieldPath)
    (having : Option SurfaceCorrelatedHaving) :
    Except FilledFieldStarCountElabError (CheckedFilledFieldStarSource model) :=
  CheckedFilledFieldStarSource.elaborate model declaringGroup authored having

end A12Kernel
