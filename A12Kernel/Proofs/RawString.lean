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

/-- Raw mode does not change the field identity used by presence predicates. -/
theorem rawString_toPresenceField (declaration : FlatFieldDecl)
    (raw : declaration.isRawString = true) :
    declaration.toPresenceField = .string { id := declaration.id } := by
  cases kindEq : declaration.policy.kind <;>
    simp_all [FlatFieldDecl.isRawString, FlatFieldDecl.toPresenceField]

/-- Eliminated max-length metadata is extensionally absent from the runtime-condition channel. -/
@[simp] theorem rawStringMaximumLength_noRuntime
    (metadata : CheckedRawStringMaximumLength model) :
    (CheckedFlatRuleCondition.rawStringMaximumLength metadata).toRuntime? = none :=
  rfl

/-- The checked metadata boundary retains the parser's integral-constant restriction. -/
theorem checkedRawStringMaximumLength_integral
    (metadata : CheckedRawStringMaximumLength model) :
    metadata.bound.den = 1 :=
  metadata.integralBound

end A12Kernel
