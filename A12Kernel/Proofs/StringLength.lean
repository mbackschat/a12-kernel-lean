import A12Kernel.Proofs.NumericComparison
import A12Kernel.Proofs.Observation
import A12Kernel.Semantics.FlatValidation

/-! # A12Kernel.Proofs.StringLength — exact operator-sensitive empty-String laws -/

namespace A12Kernel

/-- Direct equality consumes a clean empty String as not evaluated, independently of the nonempty literal. -/
theorem directEmptyStringComparison_notFired (context : FlatContext) (field : FlatStringField)
    (expected : String) (empty : context.observeValidationAt field.id = .empty) :
    (FlatComparison.stringEqual field expected).eval context = .notFired := by
  simp [FlatComparison.eval, FlatContext.resolveDirectStringComparisonOperand, empty,
    SimpleComparisonOperand.evalDirectStringEqual]

/-- The Length consumer turns the same clean empty String into grow-only zero, so any satisfied less-than comparison fires as omission. -/
theorem emptyStringLengthLess_fires_omission (context : FlatContext)
    (field : FlatStringField) (expected : Rat)
    (empty : context.observeValidationAt field.id = .empty)
    (holds : NumericComparisonOp.less.holds 0 expected = true) :
    (FlatComparison.stringLength .less field expected).eval context = .fired .omission := by
  simpa [FlatComparison.eval, FlatContext.resolveStringLengthOperand, empty,
    StringLengthComparisonOp.toNumeric] using
      growOnlyLessFiring_is_omission 0 expected holds

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
    (FlatComparison.stringEqual field "ABC").eval context = .notFired ∧
      (FlatComparison.stringLength .less field lessThreshold).eval context = .fired .omission ∧
      (FlatComparison.stringLength .greaterEqual field greaterEqualThreshold).eval context =
        .fired .value := by
  exact ⟨directEmptyStringComparison_notFired context field "ABC" empty,
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
