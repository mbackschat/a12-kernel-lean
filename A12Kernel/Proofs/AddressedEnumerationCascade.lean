import A12Kernel.Elaboration.AddressedEnumerationCascade
import A12Kernel.Proofs.AddressedEnumerationComputation

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

/-- Phase-separated cascade projection cannot invent the ordinary String target-rejection channel. -/
theorem addressedEnumerationCascade_executeResult_hasNoTargetErrors
    (cascade : CheckedAddressedEnumerationCascade model)
    (input : CheckedDocument model)
    (producerResidual consumerResidual : List ResidualMessage)
    (outcomes : AddressedEnumerationCascadeOutcomes)
    (executed : cascade.execute input = .ok outcomes) :
    (cascade.executeResult input producerResidual consumerResidual).map
      (fun view =>
        (view.producer.withErrors, view.consumer.withErrors)) =
      .ok ([], []) := by
  unfold CheckedAddressedEnumerationCascade.executeResult
  rw [executed]
  simp [Functor.map, Except.map,
    addressedEnumerationResults_haveNoTargetErrors]

/-- Combined cascade application delegates to the two established result folds in phase order. -/
theorem addressedEnumerationCascadeRun_applyToChecked_delegates
    (view : AddressedEnumerationCascadeRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    view.applyToChecked destination = (do
      let afterProducer ←
        view.producer.applyTo destination.sourceStringTargetStateAt
      view.consumer.applyTo afterProducer) := by
  rfl

end A12Kernel
