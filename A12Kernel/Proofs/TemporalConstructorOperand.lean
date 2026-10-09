import A12Kernel.Elaboration.TemporalConstructorOperand

/-! # The temporal constructor operand gate's laws

The gate is a table lookup, and its content is which class each miss reports. Three results carry it:
a component position admits exactly its own operator, the class of a miss is decided by family
membership with the slotless component excepted, and a constructor with no component slots reports
one class at every position — which is `DateTime`'s whole behaviour rather than a special case.
-/

namespace A12Kernel

/-- A component position admits its own operator and nothing else. -/
theorem constructorOperandRefusal_none_iff (constructor : TemporalConstructor) (position : Nat)
    (operand : TemporalComponent) :
    constructorOperandRefusal constructor position operand = none ↔
      constructor.componentSlots[position]? = some operand := by
  unfold constructorOperandRefusal
  cases hslot : constructor.componentSlots[position]? with
  | none => simp
  | some expected =>
    by_cases heq : operand = expected
    · subst heq; simp
    · have hsym : ¬ (expected = operand) := fun h => heq h.symm
      simp only [heq, beq_iff_eq]
      cases hslotless : slotlessComponent operand <;>
        cases hfamily : operand.isDateFamily == expected.isDateFamily <;>
        simp_all

/-- **A constructor with no component slots reports one class everywhere.** `DateTime` is the whole
extension of that condition, so its behaviour needs no arm of its own: an extraction call at either of
its positions is a kind error, not a position error. -/
theorem constructorOperandRefusal_valueSlots (constructor : TemporalConstructor) (position : Nat)
    (operand : TemporalComponent) (h : constructor.componentSlots = []) :
    constructorOperandRefusal constructor position operand = some .invalidDateForOp := by
  simp [constructorOperandRefusal, h]

/-- The date-kind class arises **only** where the slot table is exhausted, so a component position
never reports it. Together with the law above this makes the class a property of the constructor
rather than of the operand. -/
theorem constructorOperandRefusal_invalidDateForOp_iff (constructor : TemporalConstructor)
    (position : Nat) (operand : TemporalComponent) :
    constructorOperandRefusal constructor position operand = some .invalidDateForOp ↔
      constructor.componentSlots[position]? = none := by
  unfold constructorOperandRefusal
  cases hslot : constructor.componentSlots[position]? with
  | none => simp
  | some expected =>
    cases hop : operand == expected <;>
      cases hslotless : slotlessComponent operand <;>
      cases hfamily : operand.isDateFamily == expected.isDateFamily <;>
      simp_all

/-- **The slotless component is never a wrong-position case.** It shares the date family with three
admitted components, so the family test alone would report the wrong-position class for it; the
measured answer is the not-allowed class, and this law is where that correction lives. -/
theorem constructorOperandRefusal_slotless (constructor : TemporalConstructor) (position : Nat)
    (operand : TemporalComponent) (hslotless : slotlessComponent operand = true)
    (hmiss : constructor.componentSlots[position]? ≠ none) :
    constructorOperandRefusal constructor position operand = some .extractOpNotAllowed := by
  unfold constructorOperandRefusal
  cases hslot : constructor.componentSlots[position]? with
  | none => exact absurd hslot hmiss
  | some expected =>
    have hmem : expected ∈ constructor.componentSlots := List.mem_of_getElem? hslot
    have hne : ¬ (operand = expected) := by
      rintro rfl
      cases constructor <;> simp [TemporalConstructor.componentSlots] at hmem <;>
        rcases hmem with rfl | rfl | rfl <;> simp [slotlessComponent] at hslotless
    simp [hne, hslotless]

/-- Off the slotless component, family membership decides the class outright. This is the readable
form of the split and the one a reimplementer checks. -/
theorem constructorOperandRefusal_family (constructor : TemporalConstructor) (position : Nat)
    (expected operand : TemporalComponent)
    (hslot : constructor.componentSlots[position]? = some expected)
    (hne : operand ≠ expected) (hslotless : slotlessComponent operand = false) :
    constructorOperandRefusal constructor position operand =
      some (if operand.isDateFamily == expected.isDateFamily then .extractOpWrongPosition
            else .extractOpNotAllowed) := by
  unfold constructorOperandRefusal
  simp only [hslot, hne, beq_iff_eq, hslotless, Bool.false_eq_true, if_false]
  cases hfamily : operand.isDateFamily == expected.isDateFamily <;> simp_all

/-- Time admits exactly its canonical prefixes, including the empty prefix. -/
theorem operandCountAdmitted_prefix (supplied : Nat) :
    operandCountAdmitted .time supplied = true ↔ supplied ≤ 3 := by
  simp [operandCountAdmitted]

/-- Date's year is full, split, or supplied by an existing Base Year. -/
theorem operandCountAdmitted_date (supplied : Nat) (hasBaseYear : Bool) :
    operandCountAdmitted .date supplied hasBaseYear = true ↔
      supplied = 3 ∨ supplied = 4 ∨ (supplied = 2 ∧ hasBaseYear = true) := by
  simp [operandCountAdmitted, or_assoc]

/-- The full operand list is always admitted, whichever constructor it is. -/
@[simp] theorem operandCountAdmitted_full (constructor : TemporalConstructor) :
    operandCountAdmitted constructor constructor.arity = true := by
  cases constructor <;> simp [operandCountAdmitted, TemporalConstructor.arity]

/-- Every component constructor's slot list is as long as its arity, so `arity` and the slot table
cannot drift apart. `DateTime` is excluded because its positions are not components. -/
theorem componentSlots_length (constructor : TemporalConstructor)
    (h : constructor.componentSlots ≠ []) :
    constructor.componentSlots.length = constructor.arity := by
  cases constructor <;> simp_all [TemporalConstructor.componentSlots, TemporalConstructor.arity]

end A12Kernel
