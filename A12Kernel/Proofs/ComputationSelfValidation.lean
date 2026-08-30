import A12Kernel.Elaboration.NumericComputation
import A12Kernel.Semantics.ComputationSelfValidation
import A12Kernel.Semantics.GroupPresence

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

/-- The starred channel is the validation arm's declared-extent movement, not a second rule.

    `FilledGroupCount.availableWithFillability?` already decides a count's movement by comparing it
    to its declared extent, and this states that the computation arm's row channel *is* that
    decision rather than a restatement of it. Without this the two arms could drift apart on the
    same group while both still passed their own cases. -/
theorem starredGroupCount_canGrow_eq_declared_extent_movement
    (instantiated capacity : Nat) :
    (ComputationOperandGrowth.starredGroupCount instantiated capacity).canGrow =
      (((FilledGroupCount.value instantiated).availableWithFillability? capacity).any
        fun available => available.2.canGrow) := by
  simp only [ComputationOperandGrowth.canGrow, FilledGroupCount.availableWithFillability?,
    Option.any_some]
  by_cases below : instantiated < capacity <;>
    simp [below, NumericFillability.growOnly, NumericFillability.fixed]

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

/-! ## The producer -/

/-- A fixed operand can grow exactly when it currently contributes nothing.

    Growth and contribution are one decision read twice, so a message cannot type VALUE on an
    operand the count treats as absent, nor OMISSION on one it treats as present. -/
theorem fixedGroup_canGrow_iff_contributes_zero (cells : List CellObservation) :
    (ComputationOperandGrowth.fixedGroup (groupPresentForComputation cells)).canGrow = true ↔
      (GroupCountOperandReading.fixed cells).contribution = 0 := by
  simp only [ComputationOperandGrowth.canGrow, GroupCountOperandReading.contribution]
  cases groupPresentForComputation cells <;> simp

/-- The two readings of a fixed operand refuse together, because they share one descendant read.

    This is what keeps a consumer from reaching a typed message without a channel behind it, or a
    channel for a group the count itself refused. -/
theorem growthOfGroupCountOperand_fixed_refuses_iff
    {model : FlatModel} (context : NumericComputationEvaluationContext)
    (reference : ResolvedGroupReference) (fault : NumericComputationFault) :
    context.growthOfGroupCountOperand model (.fixed reference) = .error fault ↔
      context.readGroupCountOperand model (.fixed reference) = .error fault := by
  simp only [NumericComputationEvaluationContext.growthOfGroupCountOperand,
    NumericComputationEvaluationContext.readGroupCountOperand]
  cases context.scalar.readGroupDescendants model reference <;> simp [Except.map]

end A12Kernel
