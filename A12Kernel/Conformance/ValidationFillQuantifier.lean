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

/-! ## The erroneous-member table, locked as a set

Every cell below is already reachable from the single-operator cases above; what none of them
expresses is the **law those cells jointly establish**, and that gap is what let a wrong account
survive. The account "an erroneous member suppresses every quantifier over its list" was measured on
four rules that all needed the erroneous member's state, so it fitted every row and was still false.
The two rows that refute it — an existential decided by a known TRUE, a negation decided by a known
FALSE — are the third and fourth here, and the two clean documents are the controls that make a
silence a reading rather than a dead fixture ([checkpoint](../../docs/SOURCES.md#src-erroneous-member-quantifier-undecidable)).
-/

/-- The three-member lists behind the measured table. The two malformed documents carry **different**
formal causes, because the measurement used two converters and the result belongs to the class. -/
private def threeValid : List CellObservation :=
  [.value (.num 1), .value (.num 2), .value (.num 3)]

private def oneEmptyTwoValid : List CellObservation :=
  [.value (.num 1), .empty, .value (.num 3)]

private def oneErroneousTwoValid : List CellObservation :=
  [.value (.num 1), .unknown .malformed, .value (.num 3)]

private def oneErroneousTwoEmpty : List CellObservation :=
  [.empty, .unknown .dateFormat, .empty]

private def tallyOf (cells : List CellObservation) : ValidationFillTally :=
  cells.foldl (fun accumulated cell =>
    accumulated.combine cell.asValidationFillTally) (tally 0 0 0 0)

/-- One document's row of the table: the four quantifiers the measurement ran, then the count that
covers both of its comparison columns at once — an unavailable count fires no comparison. -/
private def tableRow (cells : List CellObservation) :
    List ValidationFillOutcome × FilledFieldCount :=
  ([.allFieldsFilled, .notAllFieldsFilled, .atLeastOneFieldFilled, .noFieldFilled].map
    fun operator => eval operator (tallyOf cells),
   numberOfFilledFields cells)

/- A quantifier is decided exactly when the members whose state is **known** already settle it. Rows
   three and four are the whole content: an erroneous member leaves undecided only the verdicts that
   needed it, and it is the fourth row that makes the statement symmetric rather than making the
   existential an exception. -/
example :
    [tableRow threeValid, tableRow oneEmptyTwoValid,
     tableRow oneErroneousTwoValid, tableRow oneErroneousTwoEmpty] =
    [([.fired .value, .falseOrUnknown, .fired .value, .falseOrUnknown], .value 3),
     ([.falseOrUnknown, .fired .omission, .fired .value, .falseOrUnknown], .value 2),
     ([.falseOrUnknown, .falseOrUnknown, .fired .value, .falseOrUnknown], .unknown),
     ([.falseOrUnknown, .fired .omission, .falseOrUnknown, .falseOrUnknown], .unknown)] := by
  native_decide

/- The validation/computation phase split is observable before any connective integration. -/
example :
    eval .atLeastOneFieldFilled (tally 0 0 1 0) = .falseOrUnknown ∧
      FieldFillQuantifier.atLeastOneFieldFilled.evalComputation
        [.poison .malformed] = .poison .malformed := by
  constructor <;> rfl

end A12Kernel.Conformance.ValidationFillQuantifier
