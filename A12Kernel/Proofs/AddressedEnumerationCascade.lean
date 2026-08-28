import A12Kernel.Elaboration.AddressedEnumerationCascade
import A12Kernel.Proofs.AddressedEnumerationComputation
import A12Kernel.Proofs.ComputationFormalInput

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

/-- The fixed three-stage certificate keeps every target identity distinct. -/
theorem addressedEnumerationThreeStageCascade_targetsPairwiseDistinct
    (plan : CheckedAddressedEnumerationThreeStageCascade model) :
    plan.first.target.field ≠ plan.second.target.field ∧
      plan.first.target.field ≠ plan.third.target.field ∧
      plan.second.target.field ≠ plan.third.target.field := by
  have firstSecond :
      plan.first.target.field ≠ plan.second.target.field := by
    intro same
    have reads := plan.secondReadsFirst
    have excludes := plan.second.targetNotReferenced
    rw [same] at reads
    simp_all
  have secondThird :
      plan.second.target.field ≠ plan.third.target.field := by
    intro same
    have reads := plan.thirdReadsSecond
    have excludes := plan.third.targetNotReferenced
    rw [same] at reads
    simp_all
  exact ⟨firstSecond, plan.firstAndThirdTargetsDistinct, secondThird⟩

/-- Three-stage execution is exactly two accumulated dependency projections followed by the terminal read. -/
theorem addressedEnumerationThreeStageCascade_execute_delegates
    (plan : CheckedAddressedEnumerationThreeStageCascade model)
    (input : CheckedDocument model) :
    plan.execute input = (do
      let first ← plan.first.execute input
        |>.mapError AddressedEnumerationThreeStageCascadeFault.first
      let firstDependencies ← projectEnumerationDependencyCells first
        |>.mapError fun error =>
          .firstDependency error.target error.cause
      let readAfterFirst :=
        readAfterEnumerationDependencies input firstDependencies
      let second ← plan.second.executeWithRead input readAfterFirst
        |>.mapError AddressedEnumerationThreeStageCascadeFault.second
      let secondDependencies ← projectEnumerationDependencyCells second
        |>.mapError fun error =>
          .secondDependency error.target error.cause
      let readAfterSecond := readAfterEnumerationDependenciesWith
        secondDependencies readAfterFirst
      let third ← plan.third.executeWithRead input readAfterSecond
        |>.mapError AddressedEnumerationThreeStageCascadeFault.third
      pure { first, second, third }) := by
  rfl

/-- Result projection observes the three already-executed outcome phases without recomputation. -/
theorem addressedEnumerationThreeStageCascade_executeResult_projects
    (plan : CheckedAddressedEnumerationThreeStageCascade model)
    (input : CheckedDocument model)
    (firstResidual secondResidual thirdResidual : List ResidualMessage)
    (outcomes : AddressedEnumerationThreeStageCascadeOutcomes)
    (executed : plan.execute input = .ok outcomes) :
    (plan.executeResult input firstResidual secondResidual thirdResidual).map
      (fun view => (view.first, view.second, view.third)) = .ok (
        projectAddressedEnumerationResults input firstResidual outcomes.first,
        projectAddressedEnumerationResults input secondResidual outcomes.second,
        projectAddressedEnumerationResults input thirdResidual outcomes.third) := by
  change plan.executeWithFallbackRead input input.read = .ok outcomes at executed
  unfold CheckedAddressedEnumerationThreeStageCascade.executeResult
    CheckedAddressedEnumerationThreeStageCascade.executeResultWithFallbackRead
  rw [executed]
  rfl

/-- Static Enumeration compatibility excludes target-rejection entries from every phase under any checked fallback view. -/
theorem addressedEnumerationThreeStageCascade_executeResultWithFallbackRead_hasNoTargetErrors
    (plan : CheckedAddressedEnumerationThreeStageCascade model)
    (input : CheckedDocument model)
    (fallbackRead : CellAddr → Except CheckedDocumentError CheckedCell)
    (firstResidual secondResidual thirdResidual : List ResidualMessage)
    (outcomes : AddressedEnumerationThreeStageCascadeOutcomes)
    (executed : plan.executeWithFallbackRead input fallbackRead = .ok outcomes) :
    (plan.executeResultWithFallbackRead input fallbackRead firstResidual
      secondResidual thirdResidual).map
      (fun view =>
        (view.first.withErrors, view.second.withErrors,
          view.third.withErrors)) = .ok ([], [], []) := by
  unfold CheckedAddressedEnumerationThreeStageCascade.executeResultWithFallbackRead
  rw [executed]
  change Except.ok (
    (projectAddressedEnumerationResults input firstResidual
      outcomes.first).withErrors,
    (projectAddressedEnumerationResults input secondResidual
      outcomes.second).withErrors,
    (projectAddressedEnumerationResults input thirdResidual
      outcomes.third).withErrors) = Except.ok ([], [], [])
  rw [addressedEnumerationResults_haveNoTargetErrors,
    addressedEnumerationResults_haveNoTargetErrors,
    addressedEnumerationResults_haveNoTargetErrors]

/-- Immutable three-stage execution specializes the fallback-view target-error exclusion. -/
theorem addressedEnumerationThreeStageCascade_executeResult_hasNoTargetErrors
    (plan : CheckedAddressedEnumerationThreeStageCascade model)
    (input : CheckedDocument model)
    (firstResidual secondResidual thirdResidual : List ResidualMessage)
    (outcomes : AddressedEnumerationThreeStageCascadeOutcomes)
    (executed : plan.execute input = .ok outcomes) :
    (plan.executeResult input firstResidual secondResidual thirdResidual).map
      (fun view =>
        (view.first.withErrors, view.second.withErrors,
          view.third.withErrors)) = .ok ([], [], []) := by
  change plan.executeWithFallbackRead input input.read = .ok outcomes at executed
  exact addressedEnumerationThreeStageCascade_executeResultWithFallbackRead_hasNoTargetErrors
    plan input input.read firstResidual secondResidual thirdResidual outcomes
    executed

/-- Checked three-stage formal inputs remain call-global and are never duplicated into phase residual channels. -/
theorem addressedEnumerationThreeStage_executeResultWithFormalInputs_exact
    (plan : CheckedAddressedEnumerationThreeStageCascade model)
    (input : CheckedDocument model)
    (inputPlan : CheckedComputationFormalInputPlan model)
    (prepared : ComputationFormalInputPreparation model)
    (outcomes : AddressedEnumerationThreeStageCascadeOutcomes)
    (view : AddressedEnumerationThreeStageFormalInputRunView model)
    (planned : plan.formalInputPlan = .ok inputPlan)
    (preparation : inputPlan.prepare input = .ok prepared)
    (executed : plan.executeWithFallbackRead input
      prepared.preliminary.readComputation = .ok outcomes)
    (produced : plan.executeResultWithFormalInputs input = .ok view) :
    view.formalErrorsInOperands = prepared.formalErrorsInOperands ∧
      view.phases.first.formalErrorsInOperands = [] ∧
      view.phases.second.formalErrorsInOperands = [] ∧
      view.phases.third.formalErrorsInOperands = [] := by
  rw [CheckedAddressedEnumerationThreeStageCascade.executeResultWithFormalInputs,
    planned] at produced
  simp only [bind, Except.bind, Except.mapError, preparation] at produced
  rw [CheckedAddressedEnumerationThreeStageCascade.executeResultWithFallbackRead,
    executed] at produced
  simp only [bind, Except.bind, pure, Except.pure,
    Except.ok.injEq] at produced
  subst view
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- A post-preparation three-stage execution failure retains the exact eager inventory beside the unchanged cascade fault. -/
theorem addressedEnumerationThreeStage_executeResultWithFormalInputs_failure_exact
    (plan : CheckedAddressedEnumerationThreeStageCascade model)
    (input : CheckedDocument model)
    (inputPlan : CheckedComputationFormalInputPlan model)
    (prepared : ComputationFormalInputPreparation model)
    (fault : AddressedEnumerationThreeStageCascadeFault)
    (planned : plan.formalInputPlan = .ok inputPlan)
    (preparation : inputPlan.prepare input = .ok prepared)
    (executed : plan.executeResultWithFallbackRead input
      prepared.preliminary.readComputation
      ([] : List ComputationFormalInputFinding) [] [] = .error fault) :
    plan.executeResultWithFormalInputs input =
      .error (.execution prepared.formalErrorsInOperands fault) := by
  rw [CheckedAddressedEnumerationThreeStageCascade.executeResultWithFormalInputs,
    planned]
  simp only [bind, Except.bind, Except.mapError, preparation, executed]

/-- Three-stage application delegates to the three result folds in phase order. -/
theorem addressedEnumerationThreeStageCascadeRun_applyToChecked_delegates
    (view : AddressedEnumerationThreeStageCascadeRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    view.applyToChecked destination = (do
      let afterFirst ←
        view.first.applyTo destination.sourceStringTargetStateAt
      let afterSecond ← view.second.applyTo afterFirst
      view.third.applyTo afterSecond) := by
  rfl

end A12Kernel
