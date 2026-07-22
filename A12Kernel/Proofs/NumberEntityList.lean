import A12Kernel.Elaboration.NumberEntityList

/-! # Shared checked Number entity-list laws -/

namespace A12Kernel

/-- Every checked Number entity list has either a starred first slot or at least one trailing slot. -/
theorem checkedNumberEntitySource_requiredMultiplicity
    (checked : CheckedNumberEntitySource model) :
    (checked.first.isStar || !checked.rest.isEmpty) = true :=
  checked.requiredMultiplicity

/-- Every checked Number entity list excludes repeated direct non-wildcard fields. -/
theorem checkedNumberEntitySource_uniqueDirectOperands
    (checked : CheckedNumberEntitySource model) :
    firstDuplicateDirectNumberEntityField? checked.operands = none :=
  checked.uniqueDirectOperands

/-- A wildcarded slot contributes no direct-field identity, so duplicate checking continues with the remaining slots unchanged. -/
theorem checkedNumberEntity_star_skipsDirectDuplicateGate
    (source : CheckedStarNumberSource model)
    (remaining : List (CheckedNumberEntityOperand model)) :
    firstDuplicateDirectNumberEntityField? (.star source :: remaining) =
      firstDuplicateDirectNumberEntityField? remaining := by
  rfl

/-- A filtered wildcarded slot has the same absence from the direct-field duplicate gate; its filter remains part of the runtime slot. -/
theorem checkedNumberEntity_starHaving_skipsDirectDuplicateGate
    (source : CheckedStarNumberHavingSource model)
    (remaining : List (CheckedNumberEntityOperand model)) :
    firstDuplicateDirectNumberEntityField? (.starHaving source :: remaining) =
      firstDuplicateDirectNumberEntityField? remaining := by
  rfl

end A12Kernel
