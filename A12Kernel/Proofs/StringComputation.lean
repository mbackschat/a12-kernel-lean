import A12Kernel.Semantics.StringComputation

/-! # A12Kernel.Proofs.StringComputation — String expression/store/delta laws -/

namespace A12Kernel

/-- The library evaluator maps a computation-phase empty field observation to a clean missing term. This bridges the phase-sensitive checked-cell boundary to the String expression semantics. -/
theorem emptyStringField_evaluates_noValue (context : StringComputationContext)
    (field : FieldId)
    (emptyRead : observeCell .computation (context.read field) = .empty) :
  (StringExpr.field field).eval context = .ok .noValue := by
  simp [StringExpr.eval, StringComputationContext.readTerm, emptyRead] <;> rfl

/-- Concatenation consumes an empty field as `""`, so a non-empty literal still reaches the root store as its own value. -/
theorem emptyStringField_concat_literal_stores_literal (context : StringComputationContext)
    (field : FieldId) (literal : String)
    (emptyRead : observeCell .computation (context.read field) = .empty)
    (nonempty : literal ≠ "") :
  (StringExpr.concat (.field field) (.literal literal)).evaluate context =
      .ok (.produced { text := literal, nonempty }) := by
  simp [StringExpr.evaluate, StringExpr.eval, StringComputationContext.readTerm, emptyRead,
    StringTerm.concat, StringTerm.store, nonempty] <;> rfl

/-- The library evaluator preserves computation-phase formal invalidity as poison instead of collapsing it into ordinary absence. -/
theorem poisonedStringField_evaluates_poison (context : StringComputationContext)
    (field : FieldId) (cause : FormalCause)
    (poisonedRead : observeCell .computation (context.read field) = .poison cause) :
    (StringExpr.field field).evaluate context = .ok (.poison cause) := by
  simp [StringExpr.evaluate, StringExpr.eval, StringComputationContext.readTerm, poisonedRead,
    StringTerm.store] <;> rfl

/-- A poisoned left field aborts concatenation before the arbitrary right expression is consulted. The result therefore depends only on the left read, preserving the computation language's read-driven poison order. -/
theorem poisonedLeftStringField_shortCircuits_concat (context : StringComputationContext)
    (field : FieldId) (cause : FormalCause) (right : StringExpr)
    (poisonedRead : observeCell .computation (context.read field) = .poison cause) :
    (StringExpr.concat (.field field) right).evaluate context = .ok (.poison cause) := by
  simp [StringExpr.evaluate, StringExpr.eval, StringComputationContext.readTerm, poisonedRead,
    StringTerm.store] <;> rfl

/-- A clean missing left field does not short-circuit: concatenation must still read and preserve a poisoned right field. -/
theorem emptyLeftStringField_reads_poisonedRight (context : StringComputationContext)
    (left right : FieldId) (cause : FormalCause)
    (emptyLeft : observeCell .computation (context.read left) = .empty)
    (poisonedRight : observeCell .computation (context.read right) = .poison cause) :
    (StringExpr.concat (.field left) (.field right)).evaluate context = .ok (.poison cause) := by
  simp [StringExpr.evaluate, StringExpr.eval, StringComputationContext.readTerm, emptyLeft,
    poisonedRight, StringTerm.concat, StringTerm.store] <;> rfl

/-- A clean missing operand contributes the empty text on the left of concatenation. -/
theorem noValue_concat_text (text : String) :
    StringTerm.concat .noValue (.text text) = .text text := by
  rfl

/-- A clean missing operand contributes the empty text on the right of concatenation. -/
theorem text_concat_noValue (text : String) :
    StringTerm.concat (.text text) .noValue = .text text := by
  rfl

/-- Concatenation of already evaluated terms is associative while preserving left-to-right poison precedence. This theorem alone does not justify reassociating expression trees across effectful reads. -/
theorem stringTerm_concat_associative (left middle right : StringTerm) :
    StringTerm.concat (StringTerm.concat left middle) right =
      StringTerm.concat left (StringTerm.concat middle right) := by
  cases left <;> cases middle <;> cases right <;>
    simp [StringTerm.concat, String.append_assoc]

/-- Two missing operands still produce an evaluated empty text at the expression layer. -/
theorem twoNoValues_concat_to_emptyText :
    StringTerm.concat .noValue .noValue = .text "" := by
  rfl

/-- An evaluated final empty text is not a legal stored String. -/
theorem finalEmptyString_is_noValue :
    (StringTerm.text "").store = .noValue := by
  rfl

/-- Adding a clean missing right operand preserves the root store decision, including poison. This is the safe boundary for a refactoring law; the stronger expression-result equality is false for `noValue`. -/
theorem concat_noValue_right_preserves_store (term : StringTerm) :
    (StringTerm.concat term .noValue).store = term.store := by
  cases term <;> rfl

/-- The same store-preservation law holds for a clean missing left operand. -/
theorem concat_noValue_left_preserves_store (term : StringTerm) :
    (StringTerm.concat .noValue term).store = term.store := by
  cases term <;> rfl

/-- Store preservation immediately lifts to every prior-target delta projection. -/
theorem concat_noValue_right_preserves_delta (term : StringTerm) (prior : PriorStringTarget) :
    (StringTerm.concat term .noValue).store.projectDelta prior =
      term.store.projectDelta prior := by
  rw [concat_noValue_right_preserves_store]

/-- Store preservation immediately lifts to every prior-target delta projection in the other direction. -/
theorem concat_noValue_left_preserves_delta (term : StringTerm) (prior : PriorStringTarget) :
    (StringTerm.concat .noValue term).store.projectDelta prior =
      term.store.projectDelta prior := by
  rw [concat_noValue_left_preserves_store]

/-- The nearest stronger claim is false: concatenation records that it evaluated even when both contributions are missing. -/
theorem concat_noValue_is_not_term_identity :
    StringTerm.concat .noValue .noValue ≠ .noValue := by
  decide

/-- A quiet no-value clears exactly a previously filled target. -/
theorem noValue_delta_iff_prior_filled (prior : PriorStringTarget) :
    StringStore.noValue.projectDelta prior = some .cleared ↔
      ∃ previous, prior = .filled previous := by
  cases prior with
  | empty => simp [StringStore.projectDelta]
  | filled previous => simp [StringStore.projectDelta]

/-- A formally poisoned computation and a quiet no-value have the same immediate target delta, while remaining distinct semantic states. -/
theorem poison_and_noValue_same_immediate_delta (cause : FormalCause)
    (prior : PriorStringTarget) :
    (StringStore.poison cause).projectDelta prior =
      StringStore.noValue.projectDelta prior := by
  cases prior <;> rfl

/-- The semantic states hidden by that immediate delta equivalence are never equal. -/
theorem poison_is_not_noValue (cause : FormalCause) :
    StringStore.poison cause ≠ .noValue := by
  simp

/-- A produced String equal to the prior typed value is omitted from the delta. -/
theorem unchangedString_has_no_delta (value : StoredString) :
    (StringStore.produced value).projectDelta (.filled value) = none := by
  simp [StringStore.projectDelta]

/-- A produced String different from the prior typed value is reported as `VALUE`. -/
theorem changedString_has_value_delta (value previous : StoredString)
    (changed : value ≠ previous) :
    (StringStore.produced value).projectDelta (.filled previous) = some (.value value) := by
  simp [StringStore.projectDelta, changed]

end A12Kernel
