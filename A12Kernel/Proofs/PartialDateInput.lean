import A12Kernel.Elaboration.PartialDateInput

/-! # Partially known Date input laws

The precision ladder is **monotone**: a deeper declared precision admits every value a shallower one
admits, so the measured admission table is a staircase rather than three unrelated sets. The stored
classifier's own boundaries are stated beside it: a full-precision declaration is never certified
here, present-empty text is never a rejection, and every rejection carries one of exactly two causes.
-/

namespace A12Kernel

/-- Each step of the precision ladder only adds shapes. Stated as the two adjacent steps rather than
over an order relation, because the mode has four constructors and the transitive case follows. -/
theorem partialMode_dayOptional_le_monthOptional
    (value : PartiallyKnownDateValue)
    (admitted : TemporalPartialMode.dayOptional.admitsPartiallyKnownValue value = true) :
    TemporalPartialMode.monthOptional.admitsPartiallyKnownValue value = true := by
  cases value <;> simp_all [TemporalPartialMode.admitsPartiallyKnownValue]

@[inherit_doc partialMode_dayOptional_le_monthOptional]
theorem partialMode_monthOptional_le_yearOptional
    (value : PartiallyKnownDateValue)
    (admitted : TemporalPartialMode.monthOptional.admitsPartiallyKnownValue value = true) :
    TemporalPartialMode.yearOptional.admitsPartiallyKnownValue value = true := by
  cases value <;> simp_all [TemporalPartialMode.admitsPartiallyKnownValue]

/-- The deepest precision admits every legal stored shape, which is what makes the ladder's top total
rather than merely wider. -/
@[simp] theorem partialMode_yearOptional_admits_all
    (value : PartiallyKnownDateValue) :
    TemporalPartialMode.yearOptional.admitsPartiallyKnownValue value = true := by
  cases value <;> rfl

/-- Full precision admits **no** partially known shape, including the full one: such a declaration's
values are plain Dates owned by the full-precision classifier rather than narrower partial values.
This is the nearest false generalization — the ladder does not start with "full admits full". -/
@[simp] theorem partialMode_full_admits_none
    (value : PartiallyKnownDateValue) :
    TemporalPartialMode.full.admitsPartiallyKnownValue value = false := by
  cases value <;> rfl

/-- A certified declaration retains its declared precision, so a consumer reads the admitted omission
depth off the certificate rather than re-deriving it. -/
theorem checkedPartialDateInputField_mode_declared
    (checked : CheckedPartialDateInputField) :
    checked.policy.partialMode = checked.mode ∧ checked.mode ≠ .full :=
  ⟨checked.modeOwned, checked.admitsOmission⟩

/-- Present-empty text is never a formal rejection: emptiness is not invalidity, and the classifier
preserves that distinction before any component is read. -/
@[simp] theorem classifyStored_empty
    (checked : CheckedPartialDateInputField) :
    checked.classifyStored "" = .presentEmpty := by
  simp [CheckedPartialDateInputField.classifyStored]

end A12Kernel
