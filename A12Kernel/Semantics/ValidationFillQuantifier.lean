import A12Kernel.Core
import A12Kernel.Semantics.FieldFillQuantifier

/-! # Resolved validation field-fill quantifiers

This capsule evaluates the seven unfiltered field-fill operators over already-resolved counts. Validation exposes only `fired polarity` versus the kernel's collapsed `FALSE_OR_UNKNOWN`; it does not invent a hidden false/unknown distinction. Declared-but-uninstantiated slots are empty only for declared-range predicates. Authored expansion, `Having`, row eligibility, partial validation, and physical read traces remain separate boundaries.
-/

namespace A12Kernel

/-- The exact validation-side observable retained by this capsule. -/
inductive ValidationFillOutcome where
  | fired (polarity : Polarity)
  | falseOrUnknown
  deriving Repr, DecidableEq

/-- Extensional classification of one already-resolved, unfiltered field range. Unknown cells count in the range but are neither filled nor empty. -/
structure ValidationFillTally where
  filled : Nat
  empty : Nat
  unknown : Nat
  uninstantiated : Nat
  deriving Repr, DecidableEq

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

end FieldFillQuantifier

end A12Kernel
