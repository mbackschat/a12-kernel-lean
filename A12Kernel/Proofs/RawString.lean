import A12Kernel.Elaboration.RawString

/-! # Raw-String authoring laws -/

namespace A12Kernel

/-- A raw declaration cannot manufacture the checked String value capability used by comparisons, lists, computations, repeatable readers, and aggregate sources. -/
theorem rawString_toStringValueField_none (declaration : FlatFieldDecl)
    (raw : declaration.isRawString = true) :
    declaration.toStringValueField? = none := by
  cases kindEq : declaration.policy.kind <;>
    cases modeEq : declaration.stringValueMode <;>
    simp_all [FlatFieldDecl.isRawString, FlatFieldDecl.toStringValueField?]

/-- A raw String's presence field is its String field marked with the raw placeholder, the token a
first-filled member reads; presence predicates read only its id. -/
theorem rawString_toPresenceField (declaration : FlatFieldDecl)
    (raw : declaration.isRawString = true) :
    declaration.toPresenceField = .string { id := declaration.id, rawPlaceholder := true } := by
  cases kindEq : declaration.policy.kind <;>
    simp_all [FlatFieldDecl.isRawString, FlatFieldDecl.toPresenceField]

/-- Eliminated max-length metadata is extensionally absent from the runtime-condition channel. -/
@[simp] theorem rawStringMaximumLength_noRuntime
    (metadata : CheckedRawStringMaximumLength model) :
    (CheckedFlatRuleCondition.rawStringMaximumLength metadata).toRuntime? = none :=
  rfl

/-- The checked metadata boundary retains the exact lexical and signed-32-bit admission domain. -/
theorem checkedRawStringMaximumLength_admissible
    (metadata : CheckedRawStringMaximumLength model) :
    metadata.bound.authoredScale ≤ 0 ∧
      metadata.bound.value.den = 1 ∧
      -2147483648 ≤ metadata.integerBound ∧
      metadata.integerBound ≤ 2147483647 := by
  exact ⟨metadata.decimalPointFree, metadata.integralBound,
    metadata.minimumBound, metadata.maximumBound⟩

end A12Kernel
