import A12Kernel.Semantics.DateRangeOverlap
import A12Kernel.Core
import A12Kernel.Semantics.Condition
import A12Kernel.Semantics.Observation

/-! # Resolved Date-range overlap operators

This capsule begins after authored operands have been expanded and filtered in order. A slot records only whether one resulting cell supplies a filled range; every empty, unavailable, or filter-dropped cell is already classified as skipped. Operand boundaries remain because the two overlap operators derive firing polarity from different filter provenance.
-/

namespace A12Kernel

/-- One expanded position after formal checking and filter selection, over whichever interval domain the operand's declarations denote. -/
inductive OverlapSlot (α : Type) where
  | skipped
  | kept (range : α)
  deriving Repr, DecidableEq

/-- One authored operand after ordered expansion and filtering. `hasFilter` records the presence of that operand's `Having` clause, not its result. -/
structure OverlapOperand (α : Type) where
  slots : List (OverlapSlot α)
  hasFilter : Bool
  deriving Repr, DecidableEq

/-- A kept range tagged with the operand provenance needed by the consuming operator. -/
structure OverlapOccurrence (α : Type) where
  range : α
  fromFilteredOperand : Bool
  deriving Repr, DecidableEq

/-- The resolved full-Date instantiation, which every Base-Year-completed and year-bearing declaration uses. -/
abbrev ResolvedDateRangeSlot := OverlapSlot ResolvedDateRange
abbrev ResolvedDateRangeOperand := OverlapOperand ResolvedDateRange
abbrev ResolvedDateRangeOccurrence := OverlapOccurrence ResolvedDateRange

namespace OverlapOperand

/-- Retain kept occurrences in slot order. A filter-bearing operand with only skipped slots contributes nothing. -/
def occurrences {α : Type} (operand : OverlapOperand α) :
    List (OverlapOccurrence α) :=
  operand.slots.filterMap fun
    | .skipped => none
    | .kept range =>
        some { range, fromFilteredOperand := operand.hasFilter }

end OverlapOperand

/-- Flatten authored operands without losing operand order, slot order, or duplicate occurrences. -/
def flattenOverlapOccurrences {α : Type}
    (operands : List (OverlapOperand α)) :
    List (OverlapOccurrence α) :=
  operands.flatMap OverlapOperand.occurrences

@[inherit_doc flattenOverlapOccurrences]
abbrev flattenDateRangeOccurrences :
    List ResolvedDateRangeOperand → List ResolvedDateRangeOccurrence :=
  flattenOverlapOccurrences

/-- Prefix scan for `DateRangesOverlap`, parameterized by the interval domain's own overlap relation. The filter marker becomes sticky only after a kept occurrence is reached and is observed before that occurrence is compared with earlier ones. -/
def scanOverlapOccurrences {α : Type} (overlaps : α → α → Bool)
    (seen : List α)
    (reachedFilter : Bool) :
    List (OverlapOccurrence α) → Verdict
  | [] => Verdict.notFired
  | current :: rest =>
      let reachedFilter :=
        reachedFilter || current.fromFilteredOperand
      if seen.any (overlaps current.range) then
        Verdict.fired
          (if reachedFilter then Polarity.omission else Polarity.value)
      else
        scanOverlapOccurrences overlaps
          (current.range :: seen) reachedFilter rest

@[inherit_doc scanOverlapOccurrences]
abbrev scanDateRangesOverlapOccurrences :
    List ResolvedDateRange → Bool → List ResolvedDateRangeOccurrence → Verdict :=
  scanOverlapOccurrences ResolvedDateRange.overlaps

/-- Any-pair DateRange overlap with order-sensitive reached-filter polarity. -/
def evalDateRangesOverlap
    (operands : List ResolvedDateRangeOperand) : Verdict :=
  scanOverlapOccurrences ResolvedDateRange.overlaps [] false
    (flattenOverlapOccurrences operands)

/-- The same any-pair scan over unconfigured yearless intervals, which no Base Year completes. -/
def evalYearlessRangesOverlap
    (operands : List (OverlapOperand YearlessInterval)) : Verdict :=
  scanOverlapOccurrences YearlessInterval.overlaps [] false
    (flattenOverlapOccurrences operands)

/-- First-match scan for the list side of `AtLeastOneDateRangeOverlaps`, over any interval domain with an overlap relation. Only the matched list operand contributes polarity. -/
def scanAtLeastOneOverlapOccurrence {α} (overlaps : α → α → Bool) (scalar : α) :
    List (OverlapOccurrence α) → Verdict
  | [] => Verdict.notFired
  | current :: rest =>
      if overlaps scalar current.range then
        Verdict.fired
          (if current.fromFilteredOperand then
            Polarity.omission
          else
            Polarity.value)
      else
        scanAtLeastOneOverlapOccurrence overlaps scalar rest

/-- Scalar-versus-list overlap over any interval domain. A skipped scalar terminates before list-internal pairs can matter. -/
def evalAtLeastOneOverlap {α} (overlaps : α → α → Bool)
    (scalar : OverlapSlot α) (operands : List (OverlapOperand α)) : Verdict :=
  match scalar with
  | .skipped => Verdict.notFired
  | .kept range =>
      scanAtLeastOneOverlapOccurrence overlaps range
        (flattenOverlapOccurrences operands)

/-- First-match scan over resolved exact ranges. -/
abbrev scanAtLeastOneDateRangeOverlapOccurrences :
    ResolvedDateRange → List ResolvedDateRangeOccurrence → Verdict :=
  scanAtLeastOneOverlapOccurrence ResolvedDateRange.overlaps

/-- Scalar-versus-list DateRange overlap over resolved exact ranges. -/
abbrev evalAtLeastOneDateRangeOverlaps :
    ResolvedDateRangeSlot → List ResolvedDateRangeOperand → Verdict :=
  evalAtLeastOneOverlap ResolvedDateRange.overlaps

/-- Scalar-versus-list overlap over unconfigured yearless labels. The relation disagrees with any completion, so this is a distinct domain rather than a specialization of the exact one. -/
abbrev evalAtLeastOneYearlessRangeOverlaps :
    OverlapSlot YearlessInterval →
      List (OverlapOperand YearlessInterval) → Verdict :=
  evalAtLeastOneOverlap YearlessInterval.overlaps

/-- The plural operator keeps its scalar fixed; the any-pair operator accumulates earlier
ranges. This distinction prevents list-internal matches from deciding a scalar-versus-list guard. -/
inductive ComputationOverlapSearch (α : Type) where
  | anyPair (seen : List α)
  | against (scalar : α)
  deriving Repr, DecidableEq

namespace ComputationOverlapSearch

/-- A reached invalid cell aborts computation, while an empty cell leaves the search unchanged.
The overlap-guard kernel grid (2026-10-04) separates both effects from an unread invalid suffix. -/
def step (overlaps : α → α → Bool) (search : ComputationOverlapSearch α) :
    CellObservation α → ComputationOverlapSearch α ⊕ ComputationConditionResult
  | .empty => .inl search
  | .unknown cause | .poison cause => .inr (.poison cause)
  | .value value => match search with
      | .anyPair seen => if seen.any (overlaps value) then .inr .holds
          else .inl (.anyPair (value :: seen))
      | .against scalar => if overlaps scalar value then .inr .holds else .inl search

/-- An empty scalar bypasses the entire list, including its filter and addressing effects. -/
def scalarUsing (scalar : CellObservation α)
    (scanList : ComputationOverlapSearch α → Except error ComputationConditionResult) :
    Except error ComputationConditionResult :=
  match scalar with
  | .empty => pure .notTrue
  | .unknown cause | .poison cause => pure (.poison cause)
  | .value value => scanList (.against value)

end ComputationOverlapSearch

end A12Kernel
