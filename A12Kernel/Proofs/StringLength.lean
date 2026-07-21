import A12Kernel.Proofs.NumericComparison
import A12Kernel.Proofs.Observation
import A12Kernel.Semantics.FlatValidation

/-! # A12Kernel.Proofs.StringLength — exact operator-sensitive empty-String laws -/

namespace A12Kernel

/-- Both direct String equality operators consume a clean empty field as not evaluated, independently of the literal. -/
theorem directEmptyStringComparison_notFired (context : FlatContext)
    (field : FlatStringField) (op : EqualityOp) (expected : String)
    (empty : context.observeValidationAt field.id = .empty) :
    (FlatComparison.string op field expected).eval context = .notFired := by
  simp [FlatComparison.eval, FlatContext.resolveDirectStringComparisonOperand, empty,
    SimpleComparisonOperand.evalDirectString]

/-- An empty direct String literal suppresses both equality operators after a clean nonempty field value has been reached. -/
theorem directEmptyStringLiteral_notFired (context : FlatContext)
    (field : FlatStringField) (op : EqualityOp) (actual : String)
    (resolved : context.resolveDirectStringComparisonOperand field =
      .value actual true) :
    (FlatComparison.string op field "").eval context = .notFired := by
  simp [FlatComparison.eval, resolved, SimpleComparisonOperand.evalDirectString]

/-- Formal unavailability is observed before empty-literal suppression for both direct String equality operators. -/
theorem directEmptyStringLiteral_unknown (context : FlatContext)
    (field : FlatStringField) (op : EqualityOp) (cause : FormalCause)
    (resolved : context.resolveDirectStringComparisonOperand field =
      .unknown cause) :
    (FlatComparison.string op field "").eval context = .unknown := by
  simp [FlatComparison.eval, resolved, SimpleComparisonOperand.evalDirectString]

/-- The Length consumer turns the same clean empty String into grow-only zero, so any satisfied less-than comparison fires as omission. -/
theorem emptyStringLengthLess_fires_omission (context : FlatContext)
    (field : FlatStringField) (expected : Rat)
    (empty : context.observeValidationAt field.id = .empty)
    (holds : NumericComparisonOp.less.holds 0 expected = true) :
    (FlatComparison.stringLength .less field expected).eval context = .fired .omission := by
  simpa [FlatComparison.eval, FlatContext.resolveStringLengthOperand, empty,
    StringLengthComparisonOp.toNumeric] using
      growOnlyLessFiring_is_omission 0 expected holds

/-- Inclusive upper bounds have the same grow-only repair direction. -/
theorem emptyStringLengthLessEqual_fires_omission (context : FlatContext)
    (field : FlatStringField) (expected : Rat)
    (empty : context.observeValidationAt field.id = .empty)
    (holds : NumericComparisonOp.lessEqual.holds 0 expected = true) :
    (FlatComparison.stringLength .lessEqual field expected).eval context =
      .fired .omission := by
  simp [FlatComparison.eval, FlatContext.resolveStringLengthOperand, empty,
    StringLengthComparisonOp.toNumeric, NumericComparisonOp.evalFixedRight,
    NumericComparisonOp.eval, holds, NumericComparisonOp.fillCanBreak,
    NumericFillability.growOnly]

/-- Strict lower bounds cannot be repaired by growing an already-satisfying grow-only Length. -/
theorem emptyStringLengthGreater_fires_value (context : FlatContext)
    (field : FlatStringField) (expected : Rat)
    (empty : context.observeValidationAt field.id = .empty)
    (holds : NumericComparisonOp.greater.holds 0 expected = true) :
    (FlatComparison.stringLength .greater field expected).eval context =
      .fired .value := by
  simp [FlatComparison.eval, FlatContext.resolveStringLengthOperand, empty,
    StringLengthComparisonOp.toNumeric, NumericComparisonOp.evalFixedRight,
    NumericComparisonOp.eval, holds, NumericComparisonOp.fillCanBreak,
    NumericFillability.growOnly, NumericFillability.fixed]

/-- The grow-only zero cannot move downward, so any satisfied greater-or-equal comparison fires as value. -/
theorem emptyStringLengthGreaterEqual_fires_value (context : FlatContext)
    (field : FlatStringField) (expected : Rat)
    (empty : context.observeValidationAt field.id = .empty)
    (holds : NumericComparisonOp.greaterEqual.holds 0 expected = true) :
    (FlatComparison.stringLength .greaterEqual field expected).eval context = .fired .value := by
  simpa [FlatComparison.eval, FlatContext.resolveStringLengthOperand, empty,
    StringLengthComparisonOp.toNumeric] using
      growOnlyGreaterEqualFiring_is_value 0 expected holds

/-- Same field, same empty observation, different consuming operator: direct equality suppresses while Length exposes both directional polarities. -/
theorem emptyString_operatorDistinction (context : FlatContext) (field : FlatStringField)
    (lessThreshold greaterEqualThreshold : Rat)
    (empty : context.observeValidationAt field.id = .empty)
    (lessHolds : NumericComparisonOp.less.holds 0 lessThreshold = true)
    (greaterEqualHolds : NumericComparisonOp.greaterEqual.holds 0 greaterEqualThreshold = true) :
    (FlatComparison.string .equal field "ABC").eval context = .notFired ∧
      (FlatComparison.stringLength .less field lessThreshold).eval context = .fired .omission ∧
      (FlatComparison.stringLength .greaterEqual field greaterEqualThreshold).eval context =
        .fired .value := by
  exact ⟨directEmptyStringComparison_notFired context field .equal "ABC" empty,
    emptyStringLengthLess_fires_omission context field lessThreshold empty lessHolds,
    emptyStringLengthGreaterEqual_fires_value context field greaterEqualThreshold empty
      greaterEqualHolds⟩

/-- Physical String placement is not presence: absent and present-empty checked cells differ, while both presence predicates observe the same empty evaluation state. -/
theorem stringPresence_absent_presentEmpty_separator (field : FlatStringField) :
    let policy : FieldPolicy := { kind := .string }
    let absent : FlatContext := { read := fun _ => formalCheck policy .empty }
    let presentEmpty : FlatContext :=
      { read := fun _ => formalCheck policy .presentEmpty }
    formalCheck policy .empty ≠ formalCheck policy .presentEmpty ∧
      (FlatField.string field).evalFilled absent =
        (FlatField.string field).evalFilled presentEmpty ∧
      (FlatField.string field).evalNotFilled absent =
        (FlatField.string field).evalNotFilled presentEmpty := by
  simp [FlatField.evalFilled, FlatField.evalNotFilled,
    FlatField.observeValidation, FlatContext.observeValidationAt,
    formalCheck, observeCell]

end A12Kernel
