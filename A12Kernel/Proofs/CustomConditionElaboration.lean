import A12Kernel.Elaboration.CustomCondition

/-! # Checked `CustomCondition` name laws

These laws isolate the role of locale-specific reserved terminals: they reject an otherwise eligible unquoted spelling, while quote-escaped checking is independent of the reserved-terminal predicate.
-/

namespace A12Kernel

/-- A locale terminal cannot enter the unquoted custom-condition name route, regardless of its character shape. -/
theorem checkCustomConditionName_unquoted_reserved
    (isReserved : String → Bool) (value : String)
    (reserved : isReserved value = true) :
    checkCustomConditionName isReserved (.unquoted value) = none := by
  simp [checkCustomConditionName, reserved]

/-- Quote-escaped name checking depends only on the quoted character grammar, not on locale terminal classification. -/
theorem checkCustomConditionName_quoted_independent_of_reserved
    (firstReserved secondReserved : String → Bool) (value : String) :
    checkCustomConditionName firstReserved (.quoted value) =
      checkCustomConditionName secondReserved (.quoted value) := by
  rfl

end A12Kernel
