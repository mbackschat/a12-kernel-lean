import A12Kernel.Semantics.StringComputation
import A12Kernel.Proofs.StringFieldPolicy

/-! # A12Kernel.Proofs.StringComputation — String expression, store, target, application-value, and delta laws -/

namespace A12Kernel

/-- The library evaluator maps a computation-phase empty field observation to a clean missing term. This bridges the phase-sensitive checked-cell boundary to the String expression semantics. -/
theorem emptyStringField_evaluates_noValue (context : StringComputationContext)
    (field : FieldId)
    (emptyRead : observeCell .computation (context.read field) = .empty) :
  (StringExpr.field field).eval context = .ok .noValue := by
  simp [StringExpr.eval, StringComputationContext.readTerm, emptyRead] <;> rfl

/-- `RangeAsString` is an evaluated coercion: a clean missing field yields empty text rather than the bare field term's `noValue`. -/
theorem emptyStringRange_evaluates_emptyText (context : StringComputationContext)
    (field : FieldId) (start finish : Nat)
    (startPositive : 1 ≤ start) (ordered : start ≤ finish)
    (emptyRead : observeCell .computation (context.read field) = .empty) :
    (StringExpr.range field start finish).eval context = .ok (.text "") := by
  have positive : 0 < start := Nat.lt_of_lt_of_le Nat.zero_lt_one startPositive
  have valid : validStringRange start finish = true := by
    simp [validStringRange, positive, ordered]
  simp [StringExpr.eval, StringComputationContext.readTerm, emptyRead, valid] <;> rfl

/-- A formally invalid ranged source preserves its exact poison cause before any interval content decision. -/
theorem poisonedStringRange_preserves_cause (context : StringComputationContext)
    (field : FieldId) (start finish : Nat) (cause : FormalCause)
    (startPositive : 1 ≤ start) (ordered : start ≤ finish)
    (poisonedRead : observeCell .computation (context.read field) = .poison cause) :
    (StringExpr.range field start finish).eval context = .ok (.poison cause) := by
  have positive : 0 < start := Nat.lt_of_lt_of_le Nat.zero_lt_one startPositive
  have valid : validStringRange start finish = true := by
    simp [validStringRange, positive, ordered]
  simp [StringExpr.eval, StringComputationContext.readTerm, poisonedRead, valid] <;> rfl

/-- An end beyond the normalized UTF-16 length returns empty text, never the available prefix. -/
theorem overshootingStringRange_evaluates_emptyText (context : StringComputationContext)
    (field : FieldId) (start finish : Nat) (text : String)
    (startPositive : 1 ≤ start) (ordered : start ≤ finish)
    (nonempty : text.isEmpty = false)
    (overshoots : utf16CodeUnitLength text < finish)
    (valueRead : observeCell .computation (context.read field) = .value (.str text)) :
    (StringExpr.range field start finish).eval context = .ok (.text "") := by
  have positive : 0 < start := Nat.lt_of_lt_of_le Nat.zero_lt_one startPositive
  have valid : validStringRange start finish = true := by
    simp [validStringRange, positive, ordered]
  simp [StringExpr.eval, StringComputationContext.readTerm, valueRead, nonempty,
    valid, overshoots] <;> rfl

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
  | empty => simp [StringStore.projectDelta, StringDelta.projectNoValue]
  | filled previous => simp [StringStore.projectDelta, StringDelta.projectNoValue]

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
  simp [StringStore.projectDelta, StringDelta.projectValue]

/-- A produced String different from the prior typed value is reported as `VALUE`. -/
theorem changedString_has_value_delta (value previous : StoredString)
    (changed : value ≠ previous) :
    (StringStore.produced value).projectDelta (.filled previous) = some (.value value) := by
  simp [StringStore.projectDelta, StringDelta.projectValue, changed]

/-- Successful prepared target checking retains the exact attempted payload rather than the normalized text used internally for pattern and length measurement. -/
theorem acceptedStringTargetWithPattern_preserves_attempt
    (policy : StringFieldPolicy) (wholeValueMatches? : Option (String → Bool))
    (attempted : StoredString) (checked : Option String)
    (accepted :
      policy.checkTextWithPattern wholeValueMatches? attempted.text = .ok checked) :
    policy.checkTargetWithPattern wholeValueMatches? (.produced attempted) =
      .accepted attempted := by
  simp [StringFieldPolicy.checkTargetWithPattern, accepted]

/-- Successful no-pattern target checking is the exact specialization retained by the resolved computation boundary. -/
theorem acceptedStringTarget_preserves_attempt (policy : StringFieldPolicy)
    (attempted : StoredString) (checked : Option String)
    (accepted : policy.checkText attempted.text = .ok checked) :
    policy.checkTarget (.produced attempted) = .accepted attempted := by
  apply acceptedStringTargetWithPattern_preserves_attempt
  simpa [StringFieldPolicy.checkText] using accepted

/-- Every declaration-owned prepared target failure retains the exact attempted payload and first failure cause. -/
theorem rejectedStringTargetWithPattern_preserves_attempt
    (policy : StringFieldPolicy) (wholeValueMatches? : Option (String → Bool))
    (attempted : StoredString) (cause : StringTargetError)
    (rejected :
      policy.checkTextWithPattern wholeValueMatches? attempted.text = .error cause) :
    policy.checkTargetWithPattern wholeValueMatches? (.produced attempted) =
      .errored attempted cause := by
  simp [StringFieldPolicy.checkTargetWithPattern, rejected]

/-- The no-pattern target failure law remains an exact specialization. -/
theorem rejectedStringTarget_preserves_attempt (policy : StringFieldPolicy)
    (attempted : StoredString) (cause : StringTargetError)
    (rejected : policy.checkText attempted.text = .error cause) :
    policy.checkTarget (.produced attempted) = .errored attempted cause := by
  apply rejectedStringTargetWithPattern_preserves_attempt
  simpa [StringFieldPolicy.checkText] using rejected

/-- A forbidden raw CR/LF is the target error before either length clause. -/
theorem forbiddenLineBreakStringTarget_is_errored (policy : StringFieldPolicy)
    (attempted : StoredString)
    (forbidden : policy.lineBreaksPermitted = false)
    (lineBreak : containsLineBreak attempted.text = true) :
    policy.checkTarget (.produced attempted) = .errored attempted .lineBreak := by
  apply rejectedStringTarget_preserves_attempt
  apply stringFieldPolicy_forbiddenLineBreak_preemptsLength
  · simpa [String.isEmpty] using attempted.nonempty
  · exact forbidden
  · exact lineBreak

/-- A clean root no-value bypasses every ordinary String target policy. In particular, a positive minimum cannot turn absence into `tooShort`. -/
theorem noValue_bypassesStringTargetPolicy (policy : StringFieldPolicy) :
    policy.checkTarget .noValue = .noValue := by
  rfl

/-- A poisoned root result bypasses every ordinary String target policy while preserving its formal cause. -/
theorem poison_bypassesStringTargetPolicy (policy : StringFieldPolicy)
    (cause : FormalCause) :
    policy.checkTarget (.poison cause) = .poison cause := by
  rfl

/-- Whenever target checking accepts a produced value, its delta is exactly the established clean projection for every prior target. -/
theorem acceptedStringTarget_preserves_store_delta
    (policy : StringFieldPolicy) (attempted : StoredString)
    (checked : Option String)
    (accepted : policy.checkText attempted.text = .ok checked)
    (prior : PriorStringTarget) :
    (policy.checkTarget (.produced attempted)).projectDelta prior =
      (StringStore.produced attempted).projectDelta prior := by
  rw [acceptedStringTarget_preserves_attempt policy attempted checked accepted]
  rfl

/-- ERRORED reporting is independent of target absence, stale content, or typed equality. -/
theorem erroredStringTarget_reports_unconditionally (attempted : StoredString)
    (cause : StringTargetError) (prior : PriorStringTarget) :
    (StringTargetOutcome.errored attempted cause).projectDelta prior =
      some (.errored attempted cause) := by
  cases prior <;> rfl

/-- The lossy application projection exposes no stored value for an errored outcome; exact absent versus present-empty shape belongs to `StringApplication`. -/
theorem erroredStringTarget_has_no_appliedValue (attempted : StoredString)
    (cause : StringTargetError) :
    (StringTargetOutcome.errored attempted cause).appliedValue = none := by
  rfl

/-- Applying an accepted outcome exposes its checked stored value. -/
theorem acceptedStringTarget_applies_value (value : StoredString) :
    (StringTargetOutcome.accepted value).appliedValue = some value := by
  rfl

/-- The nearest stronger application claim is false: equal value-only application results do not imply equal computation deltas. A quiet no-value and ERRORED both apply to no stored value, but only ERRORED reports its attempted value and cause. -/
theorem same_appliedValue_does_not_imply_same_delta (attempted : StoredString)
    (cause : StringTargetError) :
    (StringTargetOutcome.errored attempted cause).appliedValue =
        StringTargetOutcome.noValue.appliedValue ∧
      (StringTargetOutcome.errored attempted cause).projectDelta .empty ≠
        StringTargetOutcome.noValue.projectDelta .empty := by
  simp [StringTargetOutcome.appliedValue, StringTargetOutcome.projectDelta,
    StringDelta.projectNoValue]

end A12Kernel
