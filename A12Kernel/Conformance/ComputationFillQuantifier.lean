import A12Kernel.Semantics.ComputationFillQuantifier

/-! # Computation field-fill quantifier locks

These examples exercise the seven resolved field-fill scans after path, group, repetition, and filter expansion. They distinguish instantiated empty cells from declared-but-uninstantiated slots and lock the first reached poison without claiming that this module performs expansion.
-/

namespace A12Kernel.Conformance.ComputationFillQuantifier

open A12Kernel

private def malformed : FormalCause := .malformed
private def constrained : FormalCause := .declaredConstraint

private def eval (operator : ComputationFieldFillQuantifier)
    (slots : List ComputationFillSlot) : ComputationConditionResult :=
  operator.eval slots

/- Declared-range operators observe an uninstantiated slot as empty. -/
example : eval .allFieldsFilled [.uninstantiated] = .notTrue := by rfl
example : eval .notAllFieldsFilled [.uninstantiated] = .holds := by rfl

/- Instantiated-range operators ignore the same slot. -/
example : eval .noFieldFilled [.uninstantiated] = .holds := by rfl
example : eval .atLeastOneFieldFilled [.uninstantiated] = .notTrue := by rfl
example : eval .moreThanOneFieldFilled [.uninstantiated] = .notTrue := by rfl
example : eval .moreThanOneFieldFilled [.filled, .empty] = .notTrue := by rfl
example : eval .notExactlyOneFieldFilled [.uninstantiated] = .holds := by rfl
example : eval .fieldsNotCollectivelyFilled [.uninstantiated] = .notTrue := by rfl

/- Every operator ignores poison after its own deciding prefix. -/
example : eval .allFieldsFilled [.empty, .poison malformed] = .notTrue := by rfl
example : eval .notAllFieldsFilled [.empty, .poison malformed] = .holds := by rfl
example : eval .noFieldFilled [.filled, .poison malformed] = .notTrue := by rfl
example : eval .atLeastOneFieldFilled [.filled, .poison malformed] = .holds := by rfl
example : eval .moreThanOneFieldFilled [.filled, .filled, .poison malformed] = .holds := by rfl
example : eval .notExactlyOneFieldFilled [.filled, .filled, .poison malformed] = .holds := by rfl
example : eval .fieldsNotCollectivelyFilled [.empty, .filled, .poison malformed] = .holds := by rfl

/- A poison reached before the decision keeps its exact cause. -/
example : eval .allFieldsFilled [.filled, .poison malformed, .empty] =
    .poison malformed := by rfl
example : eval .noFieldFilled [.empty, .poison constrained, .filled] =
    .poison constrained := by rfl
example : eval .moreThanOneFieldFilled [.filled, .poison malformed, .filled] =
    .poison malformed := by rfl
example : eval .notExactlyOneFieldFilled [.filled, .poison constrained, .filled] =
    .poison constrained := by rfl
example : eval .fieldsNotCollectivelyFilled [.filled, .poison malformed, .empty] =
    .poison malformed := by rfl

/- The mixed operator uses instantiated presence and declared absence. -/
example : eval .fieldsNotCollectivelyFilled [.uninstantiated, .filled, .poison malformed] =
    .holds := by rfl
example : eval .fieldsNotCollectivelyFilled [.filled, .poison malformed, .uninstantiated] =
    .poison malformed := by rfl

/- Zero, exactly one, and at least two filled slots remain distinct. -/
example : eval .notExactlyOneFieldFilled [.empty, .uninstantiated] = .holds := by rfl
example : eval .notExactlyOneFieldFilled [.empty, .filled, .uninstantiated] = .notTrue := by rfl
example : eval .notExactlyOneFieldFilled [.filled, .empty, .filled] = .holds := by rfl

end A12Kernel.Conformance.ComputationFillQuantifier
