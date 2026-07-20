import A12Kernel.Semantics.ValidationFillQuantifier
import A12Kernel.Semantics.ComputationFillQuantifier

/-! # Resolved validation field-fill quantifier locks

These examples exercise the exact unfiltered `TRUE_WF | TRUE_AF | FALSE_OR_UNKNOWN` projection over already-classified counts. They distinguish instantiated cells from declared-but-uninstantiated absences and validation unknown from computation poison without claiming authored expansion, `Having`, row eligibility, or partial validation.
-/

namespace A12Kernel.Conformance.ValidationFillQuantifier

open A12Kernel

private def tally (filled empty unknown uninstantiated : Nat) :
    ValidationFillTally :=
  { filled, empty, unknown, uninstantiated }

private def eval (operator : FieldFillQuantifier)
    (input : ValidationFillTally) : ValidationFillOutcome :=
  operator.evalValidation input

/- The separating fill-count matrix fixes both firing and unfiltered polarity. -/
example : eval .allFieldsFilled (tally 2 0 0 0) = .fired .value := by rfl
example : eval .allFieldsFilled (tally 1 1 0 0) = .falseOrUnknown := by rfl
example : eval .noFieldFilled (tally 0 2 0 0) = .fired .omission := by rfl
example : eval .noFieldFilled (tally 1 1 0 0) = .falseOrUnknown := by rfl
example : eval .atLeastOneFieldFilled (tally 1 1 0 0) = .fired .value := by rfl
example : eval .atLeastOneFieldFilled (tally 0 2 0 0) = .falseOrUnknown := by rfl
example : eval .moreThanOneFieldFilled (tally 2 0 0 0) = .fired .value := by rfl
example : eval .moreThanOneFieldFilled (tally 1 1 0 0) = .falseOrUnknown := by rfl
example : eval .notAllFieldsFilled (tally 1 1 0 0) = .fired .omission := by rfl
example : eval .notAllFieldsFilled (tally 2 0 0 0) = .falseOrUnknown := by rfl
example : eval .notExactlyOneFieldFilled (tally 0 2 0 0) = .fired .omission := by rfl
example : eval .notExactlyOneFieldFilled (tally 1 1 0 0) = .falseOrUnknown := by rfl
example : eval .notExactlyOneFieldFilled (tally 2 0 0 0) = .fired .value := by rfl
example : eval .fieldsNotCollectivelyFilled (tally 1 1 0 0) = .fired .omission := by rfl
example : eval .fieldsNotCollectivelyFilled (tally 0 2 0 0) = .falseOrUnknown := by rfl
example : eval .fieldsNotCollectivelyFilled (tally 2 0 0 0) = .falseOrUnknown := by rfl

/- Unknown cells count in neither bucket; a sufficient clean witness can still decide a fire. -/
example : eval .allFieldsFilled (tally 2 0 1 0) = .falseOrUnknown := by rfl
example : eval .noFieldFilled (tally 0 1 1 0) = .falseOrUnknown := by rfl
example : eval .atLeastOneFieldFilled (tally 1 0 1 0) = .fired .value := by rfl
example : eval .moreThanOneFieldFilled (tally 1 0 1 0) = .falseOrUnknown := by rfl
example : eval .moreThanOneFieldFilled (tally 2 0 1 0) = .fired .value := by rfl
example : eval .notAllFieldsFilled (tally 0 1 1 0) = .fired .omission := by rfl
example : eval .notAllFieldsFilled (tally 0 0 1 0) = .falseOrUnknown := by rfl
example : eval .notExactlyOneFieldFilled (tally 0 0 1 0) =
    .falseOrUnknown := by rfl
example : eval .notExactlyOneFieldFilled (tally 2 0 1 0) =
    .fired .value := by rfl
example : eval .fieldsNotCollectivelyFilled (tally 1 1 1 0) =
    .fired .omission := by rfl
example : eval .fieldsNotCollectivelyFilled (tally 1 0 1 0) =
    .falseOrUnknown := by rfl
example : eval .fieldsNotCollectivelyFilled (tally 0 1 1 0) =
    .falseOrUnknown := by rfl

/- Declared omissions affect only the declared or mixed ranges. -/
example : eval .allFieldsFilled (tally 0 0 0 1) = .falseOrUnknown := by rfl
example : eval .notAllFieldsFilled (tally 0 0 0 1) = .fired .omission := by rfl
example : eval .noFieldFilled (tally 0 0 0 1) = .fired .omission := by rfl
example : eval .notExactlyOneFieldFilled (tally 0 0 0 1) =
    .fired .omission := by rfl
example : eval .fieldsNotCollectivelyFilled (tally 1 0 0 1) =
    .fired .omission := by rfl
example : eval .notExactlyOneFieldFilled (tally 1 0 0 1) =
    .falseOrUnknown := by rfl
example : eval .atLeastOneFieldFilled (tally 0 0 0 2) =
    .falseOrUnknown := by rfl
example : eval .moreThanOneFieldFilled (tally 0 0 0 2) =
    .falseOrUnknown := by rfl

/- The validation/computation phase split is observable before any connective integration. -/
example :
    eval .atLeastOneFieldFilled (tally 0 0 1 0) = .falseOrUnknown ∧
      FieldFillQuantifier.atLeastOneFieldFilled.evalComputation
        [.poison .malformed] = .poison .malformed := by
  constructor <;> rfl

end A12Kernel.Conformance.ValidationFillQuantifier
