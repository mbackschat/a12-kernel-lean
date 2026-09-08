import A12Kernel.Elaboration.ErrorTextParameterAddressing

/-! # Laws of the message parameter's addressing gates

The coordinate law is the reuse statement this family needs: the two classes differ in name and in
nothing else, so a consumer holding one coordinate's behaviour holds the other's, and a theory stating
them separately would be restating one result.

The literal-`1` law is the trap made explicit. It is stated at the maximum where the distinction bites,
because that is the only place the spelling changes the verdict.

The model-kind law records that this family's gate points the opposite way from the `#` parameters',
which is what stops "H-model has more checks" being read into either.
-/

namespace A12Kernel

/-- The two coordinates run one test: whether a specifier is refused does not depend on which coordinate
it addresses, and when it is refused the class is that coordinate's own. -/
theorem coordinateRefusal_class_follows_coordinate (coordinate : FormCoordinate) (declaredMax : Nat)
    (specifier : CoordinateSpecifier) :
    coordinateRefusal coordinate declaredMax specifier =
      (coordinateRefusal .serial declaredMax specifier).map (fun _ => coordinate.refusal) := by
  cases specifier <;> cases coordinate <;> simp [coordinateRefusal, FormCoordinate.refusal] <;>
    split <;> simp <;> split <;> simp

/-- **The trap, stated where it bites.** At a declared maximum of one the literal `1` is admitted while a
numeral of the same value is refused, so the special case is the spelling and not the number. -/
theorem literalOne_is_a_spelling (coordinate : FormCoordinate) :
    coordinateRefusal coordinate 1 .one = none ∧
      coordinateRefusal coordinate 1 (.numeral 1) = some coordinate.refusal := by
  constructor
  · rfl
  · simp [coordinateRefusal]

/-- The literal is admitted at every declared maximum, so no bound reaches it. -/
theorem literalOne_admitted_everywhere (coordinate : FormCoordinate) (declaredMax : Nat) :
    coordinateRefusal coordinate declaredMax .one = none := rfl

/-- A symbolic specifier meets the maximum-of-one check and escapes the bound, so above one it is
admitted whatever value it would denote. -/
theorem symbolic_escapes_the_bound (coordinate : FormCoordinate) (declaredMax : Nat)
    (h : declaredMax ≠ 1) :
    coordinateRefusal coordinate declaredMax .symbolic = none := by
  simp [coordinateRefusal, h]

/-- **The reverse asymmetry.** The star gate is the A12 world's own, where the `#` parameters' gate
forbids that world outright — so neither model kind checks a superset of the other's parameter surface. -/
theorem starGate_is_a12_only (access : ValueAccess) (h : access.referencedWithoutStar = false)
    (hString : access.fieldIsString = false) :
    valueAccessRefusal .a12 access = some .valueParameterOnStarredReference ∧
      valueAccessRefusal .hModel access = none := by
  constructor
  · simp [valueAccessRefusal, h]
  · simp [valueAccessRefusal, hString]

/-- The declaration gate ignores the model kind, so the two gates beside each other differ in exactly
that respect. -/
theorem declarationGate_ignores_model_kind (access : ValueAccess)
    (h : access.referencedWithoutStar = true) :
    valueAccessRefusal .a12 access = valueAccessRefusal .hModel access := by
  simp [valueAccessRefusal, h]

/-- A non-String field never reaches the declaration class, whatever the flag beside it says. -/
theorem nonString_never_skips_validation (kind : ModelKind) (access : ValueAccess)
    (hString : access.fieldIsString = false) (hStar : access.referencedWithoutStar = true) :
    valueAccessRefusal kind access = none := by
  cases kind <;> simp [valueAccessRefusal, hString, hStar]

/-- The relative-path gate refuses exactly the climbs that pass the root group. -/
theorem relativeUpRefusal_iff (ruleGroupLevel upCount : Nat) :
    relativeUpRefusal ruleGroupLevel upCount = some .parameterTooManyParentGroups ↔
      ruleGroupLevel < upCount := by
  simp [relativeUpRefusal]

/-- Climbing exactly to the root group is admitted, which is the boundary the gate sits on. -/
theorem relativeUp_to_root_admitted (level : Nat) : relativeUpRefusal level level = none := by
  simp [relativeUpRefusal]

end A12Kernel
