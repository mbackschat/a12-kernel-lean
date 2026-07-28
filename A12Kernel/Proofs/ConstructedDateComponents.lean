import A12Kernel.Elaboration.ConstructedDateComponents

/-! # Checked direct constructed-Date laws -/

namespace A12Kernel

/-- The checked boundary cannot silently select another model-zone account. -/
theorem checkedConstructedDateComponents_profile
    (checked : CheckedConstructedDateComponents model) :
    ModelZone.ConcreteProfile.ofId? model.timeZoneId =
      some checked.profile :=
  checked.profileSelected

end A12Kernel
