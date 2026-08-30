import A12Kernel.Semantics.ComputationSelfValidation

/-! # Laws of the computed target's implicit self-validation message

These are internal consequences of the chosen account, not correspondence claims. The measured
region is stated as such: the boundary law holds in every direction, while the omission law is
conditioned on the computed value lying below its seed, which is where every retained observation
sits.
-/

namespace A12Kernel

/-- The message exists exactly on a stored-versus-computed mismatch.

    The comparison is the ordinary normalized one, so two spellings of the same value produce no
    message — the equal-seed control measures that at an exact integer, and this states it at the
    scale the comparison actually uses. -/
theorem computedNumberSelfValidation_notFired_iff
    (stored computed : Rat) (operands : List ComputationOperandGrowth) :
    computedNumberSelfValidation stored computed operands = .notFired ↔
      normalizedComparisonValue computed = normalizedComparisonValue stored := by
  simp only [computedNumberSelfValidation, NumericComparisonOp.eval,
    NumericComparisonOp.holds]
  by_cases equal : normalizedComparisonValue computed = normalizedComparisonValue stored
  · simp [equal]
  · have fires : (normalizedComparisonValue computed != normalizedComparisonValue stored) = true :=
      by simp [equal]
    simp only [fires, if_pos]
    split <;> simp [equal]

/-- A computation whose every operand is closed types VALUE.

    This is the half that does not depend on direction: with the computed side unable to move and
    the stored side fixed, no legal fill can falsify the firing whichever way the gap runs. The
    at-capacity all-filled document is its measured instance. -/
theorem computedNumberSelfValidation_closed_value
    (stored computed : Rat) (operands : List ComputationOperandGrowth)
    (closed : operands.any ComputationOperandGrowth.canGrow = false)
    (differs : ¬ normalizedComparisonValue computed = normalizedComparisonValue stored) :
    computedNumberSelfValidation stored computed operands = .fired .value := by
  simp only [computedNumberSelfValidation, NumericComparisonOp.eval,
    NumericComparisonOp.holds, NumericComparisonOp.fillCanBreak,
    numericDifferenceFillCanClose, computedNumberFillability, closed,
    NumericFillability.fixed]
  simp [differs]

/-- Below its seed, the message types OMISSION exactly when some operand can still grow.

    The hypothesis is the measured region rather than a convenience: every retained document has
    its computed value below its stored one, so nothing here separates this directional reading
    from a coarser one that ignores the gap's sign. -/
theorem computedNumberSelfValidation_below_omission_iff
    (stored computed : Rat) (operands : List ComputationOperandGrowth)
    (below : normalizedComparisonValue computed < normalizedComparisonValue stored) :
    computedNumberSelfValidation stored computed operands = .fired .omission ↔
      operands.any ComputationOperandGrowth.canGrow = true := by
  have differs : ¬ normalizedComparisonValue computed = normalizedComparisonValue stored :=
    Rat.ne_of_lt below
  simp only [computedNumberSelfValidation, NumericComparisonOp.eval,
    NumericComparisonOp.holds, NumericComparisonOp.fillCanBreak,
    numericDifferenceFillCanClose, computedNumberFillability, NumericFillability.fixed]
  cases growth : operands.any ComputationOperandGrowth.canGrow <;> simp [differs, below]

/-- The two starred channels are independent, at every declared capacity.

    Exhausting capacity closes a row count and leaves a value read inside those same rows open.
    The nearest false generalization is that one starred operand has one headroom: the at-capacity
    empty-row document refutes it, and this states the refutation for any capacity rather than for
    the measured five. -/
theorem starredChannels_separate_at_capacity (rows : Nat) :
    (ComputationOperandGrowth.starredGroupCount rows rows).canGrow = false ∧
      (ComputationOperandGrowth.starredRowValues rows rows false).canGrow = true := by
  simp [ComputationOperandGrowth.canGrow]

/-- `fillToFix` is never a proper subset of the referenced set.

    It carries all of it or none of it, so a consumer reading a listed pointer as "this cell is
    empty" is reading a decision that was made once for the whole message. -/
theorem selfValidationFillToFix_all_or_nothing
    (referenced : List MessagePointer) (verdict : Verdict) :
    selfValidationFillToFix referenced verdict = referenced ∨
      selfValidationFillToFix referenced verdict = [] := by
  cases verdict with
  | fired polarity => cases polarity <;> simp [selfValidationFillToFix]
  | notFired => exact Or.inr rfl
  | unknown => exact Or.inr rfl

end A12Kernel
