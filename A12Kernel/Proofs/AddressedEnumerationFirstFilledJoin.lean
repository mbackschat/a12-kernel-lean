import A12Kernel.Elaboration.AddressedEnumerationFirstFilledJoin
import A12Kernel.Proofs.AddressedEnumerationComputation

/-! # Two-producer Enumeration `FirstFilledValue` join laws -/

namespace A12Kernel

theorem addressedEnumerationFirstFilledJoin_producerTargetsDistinct
    (join : CheckedAddressedEnumerationFirstFilledJoin model) :
    join.firstProducer.target.field ≠ join.secondProducer.target.field :=
  join.producerTargetsDistinct

theorem addressedEnumerationFirstFilledJoin_consumerSourceOrder
    (join : CheckedAddressedEnumerationFirstFilledJoin model) :
    directEnumerationFirstFilledFieldIds? join.consumer.source = some [
      join.firstProducer.target.field, join.secondProducer.target.field] :=
  join.consumerSourceFields

/-- Phase-separated join projection cannot invent the ordinary String target-rejection channel. -/
theorem addressedEnumerationFirstFilledJoin_executeResult_hasNoTargetErrors
    (join : CheckedAddressedEnumerationFirstFilledJoin model)
    (input : CheckedDocument model)
    (firstResidual secondResidual consumerResidual : List ResidualMessage)
    (outcomes : AddressedEnumerationFirstFilledJoinOutcomes)
    (executed : join.execute input = .ok outcomes) :
    (join.executeResult input firstResidual secondResidual consumerResidual).map
      (fun view => (
        view.firstProducer.withErrors,
        view.secondProducer.withErrors,
        view.consumer.withErrors)) = .ok ([], [], []) := by
  unfold CheckedAddressedEnumerationFirstFilledJoin.executeResult
  rw [executed]
  simp [Functor.map, Except.map,
    addressedEnumerationResults_haveNoTargetErrors]

/-- Combined join application delegates to the three established result folds in phase order. -/
theorem addressedEnumerationFirstFilledJoinRun_applyToChecked_delegates
    (view : AddressedEnumerationFirstFilledJoinRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    view.applyToChecked destination = (do
      let afterFirst ←
        view.firstProducer.applyTo destination.sourceStringTargetStateAt
      let afterSecond ← view.secondProducer.applyTo afterFirst
      view.consumer.applyTo afterSecond) := by
  rfl

end A12Kernel
