import A12Kernel.Elaboration.ConstructedDateComponents

/-! # Checked direct constructed-Date laws -/

namespace A12Kernel

/-- The checked boundary cannot silently select another model-zone account. -/
theorem checkedConstructedDateComponents_utc
    (checked : CheckedConstructedDateComponents model) :
    ModelZone.ConcreteProfile.ofId? model.timeZoneId = some .utc :=
  checked.profileIsUtc

end A12Kernel
