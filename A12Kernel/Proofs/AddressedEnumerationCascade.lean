import A12Kernel.Elaboration.AddressedEnumerationCascade

namespace A12Kernel

/-- Every computation-valid poison cause crosses this dependency edge as the same cause-blind cell. -/
theorem enumerationDependencyCell_poison_causeBlind
    (first second : FormalCause)
    (firstNotRequired : first ≠ .required)
    (secondNotRequired : second ≠ .required) :
    EnumerationDependencyCell.ofResult (.poison first) =
      EnumerationDependencyCell.ofResult (.poison second) := by
  cases first <;> cases second <;>
    simp_all [EnumerationDependencyCell.ofResult]

theorem addressedEnumerationCascade_targetsDistinct
    (cascade : CheckedAddressedEnumerationCascade model) :
    cascade.producer.target.field ≠ cascade.consumer.target.field := by
  intro same
  have reads := cascade.consumerReadsProducer
  have excludes := cascade.consumer.targetNotReferenced
  rw [same] at reads
  simp_all

end A12Kernel
