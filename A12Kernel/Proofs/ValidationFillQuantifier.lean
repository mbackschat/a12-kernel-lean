import A12Kernel.Semantics.ValidationFillQuantifier
import A12Kernel.Semantics.ComputationFillQuantifier

/-! # Resolved validation field-fill quantifier laws

These laws characterize the extensional, unfiltered validation evaluator after range resolution. They preserve the kernel-visible collapse of false and unknown and prove the declared-versus-instantiated range split, sufficient witnesses, polarity changes, and the phase separator from ordered computation scans. They do not cover authored expansion, `Having`, row eligibility, partial validation, physical read traces, or correspondence to the external kernel.
-/

namespace A12Kernel

private def validationTally
    (filled empty unknown uninstantiated : Nat) : ValidationFillTally :=
  { filled, empty, unknown, uninstantiated }

/-- `AllFieldsFilled` fires exactly at the clean declared boundary, including a vacuous leaf range before any whole-condition row gate. -/
theorem validationAllFieldsFilled_cleanDeclaredRange_fires
    (filled : Nat) :
    FieldFillQuantifier.allFieldsFilled.evalValidation
      (validationTally filled 0 0 0) = .fired .value := by
  rfl

/-- One unavailable cell prevents `AllFieldsFilled` regardless of the other three counts. -/
theorem validationAllFieldsFilled_unknown_prevents
    (filled empty unknown uninstantiated : Nat) :
    FieldFillQuantifier.allFieldsFilled.evalValidation
      (validationTally filled empty (unknown + 1) uninstantiated) =
        .falseOrUnknown := by
  simp [FieldFillQuantifier.evalValidation, validationTally]

/-- With no instantiated fill and no unknown, `NoFieldFilled` fires with omission polarity regardless of the empty range sizes. -/
theorem validationNoFieldFilled_zeroKnownFilled_fires
    (empty uninstantiated : Nat) :
    FieldFillQuantifier.noFieldFilled.evalValidation
      (validationTally 0 empty 0 uninstantiated) = .fired .omission := by
  rfl

/-- One known filled witness decides `AtLeastOneFieldFilled` even when unknown cells remain. -/
theorem validationAtLeastOne_filledWitness_fires
    (filled empty unknown uninstantiated : Nat) :
    FieldFillQuantifier.atLeastOneFieldFilled.evalValidation
      (validationTally (filled + 1) empty unknown uninstantiated) =
        .fired .value := by
  simp [FieldFillQuantifier.evalValidation, validationTally]

/-- Two known filled witnesses decide `MoreThanOneFieldFilled` even when unknown cells remain. -/
theorem validationMoreThanOne_twoFilled_fires
    (filled empty unknown uninstantiated : Nat) :
    FieldFillQuantifier.moreThanOneFieldFilled.evalValidation
      (validationTally (filled + 2) empty unknown uninstantiated) =
        .fired .value := by
  simp [FieldFillQuantifier.evalValidation, validationTally]

/-- One declared empty witness decides `NotAllFieldsFilled` even when unknown cells remain. -/
theorem validationNotAll_emptyWitness_fires
    (filled empty unknown uninstantiated : Nat) :
    FieldFillQuantifier.notAllFieldsFilled.evalValidation
      (validationTally filled (empty + 1) unknown uninstantiated) =
        .fired .omission := by
  simp [FieldFillQuantifier.evalValidation, validationTally]

/-- A known filled witness and a declared empty witness decide the mixed predicate even when unknown cells remain. -/
theorem validationNotCollectively_mixedWitnesses_fire
    (filled empty unknown uninstantiated : Nat) :
    FieldFillQuantifier.fieldsNotCollectivelyFilled.evalValidation
      (validationTally (filled + 1) (empty + 1) unknown uninstantiated) =
        .fired .omission := by
  simp [FieldFillQuantifier.evalValidation, validationTally]

/-- An unknown cell is neither empty nor filled: it prevents the all-empty `NoFieldFilled` result. -/
theorem validationFillQuantifier_unknown_isNotEmpty :
    FieldFillQuantifier.noFieldFilled.evalValidation
      (validationTally 0 0 1 0) = .falseOrUnknown := by
  rfl

/-- A declared-but-uninstantiated slot is empty for declared-range predicates but invisible to instantiated-range predicates. -/
theorem validationFillQuantifier_uninstantiated_rangeFork :
    FieldFillQuantifier.allFieldsFilled.evalValidation
        (validationTally 0 0 0 1) = .falseOrUnknown ∧
      FieldFillQuantifier.notAllFieldsFilled.evalValidation
        (validationTally 0 0 0 1) = .fired .omission ∧
      FieldFillQuantifier.noFieldFilled.evalValidation
        (validationTally 0 0 0 1) = .fired .omission := by
  constructor
  · rfl
  constructor <;> rfl

/-- Every instantiated-range predicate is independent of the declared-but-uninstantiated count. -/
theorem validationFillQuantifier_instantiatedRange_ignoresUninstantiated
    (filled empty unknown left right : Nat) :
    FieldFillQuantifier.noFieldFilled.evalValidation
        (validationTally filled empty unknown left) =
          FieldFillQuantifier.noFieldFilled.evalValidation
            (validationTally filled empty unknown right) ∧
      FieldFillQuantifier.atLeastOneFieldFilled.evalValidation
        (validationTally filled empty unknown left) =
          FieldFillQuantifier.atLeastOneFieldFilled.evalValidation
            (validationTally filled empty unknown right) ∧
      FieldFillQuantifier.moreThanOneFieldFilled.evalValidation
        (validationTally filled empty unknown left) =
          FieldFillQuantifier.moreThanOneFieldFilled.evalValidation
            (validationTally filled empty unknown right) ∧
      FieldFillQuantifier.notExactlyOneFieldFilled.evalValidation
        (validationTally filled empty unknown left) =
          FieldFillQuantifier.notExactlyOneFieldFilled.evalValidation
            (validationTally filled empty unknown right) := by
  constructor
  · rfl
  constructor
  · rfl
  constructor <;> rfl

/-- `NotExactlyOneFieldFilled` changes polarity between its zero-filled and at-least-two-filled firing regions. -/
theorem validationNotExactlyOne_zeroTwo_polarityChanges :
    FieldFillQuantifier.notExactlyOneFieldFilled.evalValidation
        (validationTally 0 2 0 0) = .fired .omission ∧
      FieldFillQuantifier.notExactlyOneFieldFilled.evalValidation
        (validationTally 2 0 0 0) = .fired .value := by
  constructor <;> rfl

/-- An unavailable cell blocks the zero-filled branch but not a known at-least-two-filled witness. -/
theorem validationNotExactlyOne_unknown_zeroTwo_separator
    (unknown : Nat) :
    FieldFillQuantifier.notExactlyOneFieldFilled.evalValidation
        (validationTally 0 0 (unknown + 1) 0) = .falseOrUnknown ∧
      FieldFillQuantifier.notExactlyOneFieldFilled.evalValidation
        (validationTally 2 0 (unknown + 1) 0) = .fired .value := by
  constructor
  · simp [FieldFillQuantifier.evalValidation, validationTally]
  · rfl

/-- `FieldsNotCollectivelyFilled` is not `NotAllFieldsFilled`: an all-empty range lacks the required filled witness. -/
theorem validationNotCollectively_isNot_notAll :
    FieldFillQuantifier.fieldsNotCollectivelyFilled.evalValidation
        (validationTally 0 2 0 0) ≠
      FieldFillQuantifier.notAllFieldsFilled.evalValidation
        (validationTally 0 2 0 0) := by
  intro impossible
  cases impossible

/-- Validation collapses a malformed-only range while computation preserves the reached poison cause. -/
theorem validationComputationFillQuantifier_unknownPoison_separator
    (cause : FormalCause) :
    FieldFillQuantifier.atLeastOneFieldFilled.evalValidation
        (validationTally 0 0 1 0) = .falseOrUnknown ∧
      FieldFillQuantifier.atLeastOneFieldFilled.evalComputation
        [.poison cause] = .poison cause := by
  constructor <;> rfl

end A12Kernel
