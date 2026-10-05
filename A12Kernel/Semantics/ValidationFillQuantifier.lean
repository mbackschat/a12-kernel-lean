import A12Kernel.Semantics.Observation
import A12Kernel.Cell
import A12Kernel.Core
import A12Kernel.Semantics.FieldFillQuantifier

/-! # Resolved validation field-fill quantifiers

This capsule classifies instantiated validation observations, combines adjacent resolved ranges extensionally, and evaluates the seven unfiltered field-fill operators over the resulting counts. Validation exposes only `fired polarity` versus the kernel's collapsed `FALSE_OR_UNKNOWN`; it does not invent a hidden false/unknown distinction. Declared-but-uninstantiated slots are empty only for declared-range predicates. Ordered selected ranges additionally retain filter ownership for deciding-prefix polarity. Authored expansion, filter evaluation, row eligibility, partial validation, and physical read traces remain separate boundaries.
-/

namespace A12Kernel

/-- The exact validation-side observable retained by this capsule. -/
inductive ValidationFillOutcome where
  | fired (polarity : Polarity)
  | falseOrUnknown
  deriving Repr, DecidableEq

namespace ValidationFillOutcome

/-- Embed the kernel-visible three-way result in the richer checked-condition result without inventing a definite false branch. The collapsed member is the least-information `unknown`; positive `And`/`Or` consumers can still be decided by an independent fired branch. -/
def asConservativeVerdict : ValidationFillOutcome → Verdict
  | .fired polarity => .fired polarity
  | .falseOrUnknown => .unknown

end ValidationFillOutcome

/-- Extensional classification of one already-resolved, unfiltered field range. Unknown cells count in the range but are neither filled nor empty. -/
structure ValidationFillTally where
  filled : Nat
  empty : Nat
  unknown : Nat
  uninstantiated : Nat
  deriving Repr, DecidableEq

namespace CellObservation

/-- Classify one instantiated validation read for an extensional field-fill tally. Formal unavailability is neither filled nor empty. -/
@[simp]
def asValidationFillTally : CellObservation → ValidationFillTally
  | .empty => { filled := 0, empty := 1, unknown := 0, uninstantiated := 0 }
  | .value _ => { filled := 1, empty := 0, unknown := 0, uninstantiated := 0 }
  | .unknown _ => { filled := 0, empty := 0, unknown := 1, uninstantiated := 0 }
  | .poison _ => { filled := 0, empty := 0, unknown := 1, uninstantiated := 0 }

end CellObservation

namespace ValidationFillTally

/-- Combine adjacent resolved operand ranges. Validation is extensional, so every classification count adds independently. -/
def combine (left right : ValidationFillTally) : ValidationFillTally :=
  { filled := left.filled + right.filled
    empty := left.empty + right.empty
    unknown := left.unknown + right.unknown
    uninstantiated := left.uninstantiated + right.uninstantiated }

end ValidationFillTally

/-- One authored operand after selection. `uninstantiated` counts only missing declared slots
kept by its filter; the other buckets count selected instantiated cells. Operand boundaries retain
the deciding-prefix polarity measured by the filtered field-fill grid (2026-10-03). -/
structure ValidationFillRange where
  tally : ValidationFillTally
  hasHaving : Bool
  deriving Repr, DecidableEq

namespace ValidationFillRange

/-- Counts compose extensionally; filter ownership does not. -/
def total (ranges : List ValidationFillRange) : ValidationFillTally :=
  ranges.foldr (fun range rest => range.tally.combine rest)
    { filled := 0, empty := 0, unknown := 0, uninstantiated := 0 }

/-- Whether a filtered operand contributes a filled witness before the threshold is met.
Empty and unknown filtered operands do not contribute; later operands cannot change a decision. -/
def filteredWitness (needed : Nat) : List ValidationFillRange → Bool
  | [] => false
  | range :: rest =>
      needed != 0 && ((range.hasHaving && 0 < range.tally.filled) ||
        (range.tally.filled < needed && filteredWitness (needed - range.tally.filled) rest))

end ValidationFillRange

namespace FieldFillQuantifier

/-- Evaluate an unfiltered validation field-fill operator. The tally is intentionally unordered: the externally visible validation result depends on the final classifications, not on a computation-style deciding read prefix. -/
def evalValidation (operator : FieldFillQuantifier)
    (input : ValidationFillTally) : ValidationFillOutcome :=
  match operator with
  | .allFieldsFilled =>
      if input.empty == 0 && input.unknown == 0 &&
          input.uninstantiated == 0 then
        .fired .value
      else
        .falseOrUnknown
  | .noFieldFilled =>
      if input.filled == 0 && input.unknown == 0 then
        .fired .omission
      else
        .falseOrUnknown
  | .atLeastOneFieldFilled =>
      if 0 < input.filled then .fired .value else .falseOrUnknown
  | .moreThanOneFieldFilled =>
      if 1 < input.filled then .fired .value else .falseOrUnknown
  | .notAllFieldsFilled =>
      if 0 < input.empty + input.uninstantiated then
        .fired .omission
      else
        .falseOrUnknown
  | .notExactlyOneFieldFilled =>
      if input.filled == 0 && input.unknown == 0 then
        .fired .omission
      else if 1 < input.filled then
        .fired .value
      else
        .falseOrUnknown
  | .fieldsNotCollectivelyFilled =>
      if 0 < input.filled &&
          0 < input.empty + input.uninstantiated then
        .fired .omission
      else
        .falseOrUnknown

/-- Direct correlated lists reuse the ordinary tally, preserving eager structural reads before
filter selection discards non-true outcomes (spec/07 §3). -/
def evalValidationRead [Monad m] (operator : FieldFillQuantifier)
    (read : slot → m CellObservation) (slots : List slot) : m Verdict := do
  let tally ← slots.foldlM (fun tally slot => do
    pure (tally.combine (← read slot).asValidationFillTally))
    ({ filled := 0, empty := 0, unknown := 0, uninstantiated := 0 } : ValidationFillTally)
  pure (operator.evalValidation tally).asConservativeVerdict

/-- Evaluate an ordered list of selected validation ranges. Firing uses the shared tally law;
VALUE polarity depends on the decisive witnesses, except `AllFieldsFilled`, whose successful scan
reaches every operand. Selection and the declared-slot filter evaluation remain the caller's job. -/
def evalValidationRanges (operator : FieldFillQuantifier)
    (ranges : List ValidationFillRange) : ValidationFillOutcome :=
  match operator.evalValidation (ValidationFillRange.total ranges) with
  | .fired .value =>
      let filtered := match operator with
        | .allFieldsFilled => ranges.any (·.hasHaving)
        | .atLeastOneFieldFilled => ValidationFillRange.filteredWitness 1 ranges
        | .moreThanOneFieldFilled | .notExactlyOneFieldFilled =>
            ValidationFillRange.filteredWitness 2 ranges
        | .noFieldFilled | .notAllFieldsFilled | .fieldsNotCollectivelyFilled => false
      .fired (if filtered then .omission else .value)
  | outcome => outcome

end FieldFillQuantifier

end A12Kernel
