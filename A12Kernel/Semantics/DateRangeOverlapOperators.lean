import A12Kernel.Semantics.DateRangeOverlap
import A12Kernel.Core

/-! # Resolved Date-range overlap operators

This capsule begins after authored operands have been expanded and filtered in order. A slot records only whether one resulting cell supplies a filled range; every empty, unavailable, or filter-dropped cell is already classified as skipped. Operand boundaries remain because the two overlap operators derive firing polarity from different filter provenance.
-/

namespace A12Kernel

/-- One expanded DateRange position after formal checking and filter selection. -/
inductive ResolvedDateRangeSlot where
  | skipped
  | kept (range : ResolvedDateRange)
  deriving Repr, DecidableEq

/-- One authored operand after ordered expansion and filtering. `hasFilter` records the presence of that operand's `Having` clause, not its result. -/
structure ResolvedDateRangeOperand where
  slots : List ResolvedDateRangeSlot
  hasFilter : Bool
  deriving Repr, DecidableEq

/-- A kept range tagged with the operand provenance needed by the consuming operator. -/
structure ResolvedDateRangeOccurrence where
  range : ResolvedDateRange
  fromFilteredOperand : Bool
  deriving Repr, DecidableEq

namespace ResolvedDateRangeOperand

/-- Retain kept occurrences in slot order. A filter-bearing operand with only skipped slots contributes nothing. -/
def occurrences (operand : ResolvedDateRangeOperand) :
    List ResolvedDateRangeOccurrence :=
  operand.slots.filterMap fun
    | .skipped => none
    | .kept range =>
        some { range, fromFilteredOperand := operand.hasFilter }

end ResolvedDateRangeOperand

/-- Flatten authored operands without losing operand order, slot order, or duplicate occurrences. -/
def flattenDateRangeOccurrences
    (operands : List ResolvedDateRangeOperand) :
    List ResolvedDateRangeOccurrence :=
  operands.flatMap ResolvedDateRangeOperand.occurrences

/-- Prefix scan for `DateRangesOverlap`. The filter marker becomes sticky only after a kept occurrence is reached and is observed before that occurrence is compared with earlier ones. -/
def scanDateRangesOverlapOccurrences
    (seen : List ResolvedDateRange)
    (reachedFilter : Bool) :
    List ResolvedDateRangeOccurrence → Verdict
  | [] => Verdict.notFired
  | current :: rest =>
      let reachedFilter :=
        reachedFilter || current.fromFilteredOperand
      if seen.any current.range.overlaps then
        Verdict.fired
          (if reachedFilter then Polarity.omission else Polarity.value)
      else
        scanDateRangesOverlapOccurrences
          (current.range :: seen) reachedFilter rest

/-- Any-pair DateRange overlap with order-sensitive reached-filter polarity. -/
def evalDateRangesOverlap
    (operands : List ResolvedDateRangeOperand) : Verdict :=
  scanDateRangesOverlapOccurrences [] false
    (flattenDateRangeOccurrences operands)

/-- First-match scan for the list side of `AtLeastOneDateRangeOverlaps`. Only the matched list operand contributes polarity. -/
def scanAtLeastOneDateRangeOverlapOccurrences
    (scalar : ResolvedDateRange) :
    List ResolvedDateRangeOccurrence → Verdict
  | [] => Verdict.notFired
  | current :: rest =>
      if scalar.overlaps current.range then
        Verdict.fired
          (if current.fromFilteredOperand then
            Polarity.omission
          else
            Polarity.value)
      else
        scanAtLeastOneDateRangeOverlapOccurrences scalar rest

/-- Scalar-versus-list DateRange overlap. A skipped scalar terminates before list-internal pairs can matter. -/
def evalAtLeastOneDateRangeOverlaps
    (scalar : ResolvedDateRangeSlot)
    (operands : List ResolvedDateRangeOperand) : Verdict :=
  match scalar with
  | .skipped => Verdict.notFired
  | .kept range =>
      scanAtLeastOneDateRangeOverlapOccurrences range
        (flattenDateRangeOccurrences operands)

end A12Kernel
