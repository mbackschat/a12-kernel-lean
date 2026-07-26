import A12Kernel.Elaboration.NumericComputation.RunResult

/-! # Number computation result-view laws -/

namespace A12Kernel

/-- Value-less target invalidity is the only rich Number outcome that emits a target message without a computed instance. -/
theorem numericTargetOutcome_emitsValuelessTargetError_iff
    (outcome : NumericTargetOutcome) :
    outcome.emitsValuelessTargetError = true ↔
      ∃ cause, outcome = .invalidNoValue cause := by
  cases outcome with
  | invalidNoValue cause =>
      constructor
      · intro _
        exact ⟨cause, rfl⟩
      · intro _
        rfl
  | noValue | accepted | rejected | inheritedPoison =>
      simp [NumericTargetOutcome.emitsValuelessTargetError]

/-- A value-less Number target failure contributes the stable residual message and makes the public error predicate false even when no eager message was supplied. -/
theorem numericComputationRun_invalidNoValue_residual
    (pointerAt : Target → ComputationErrorPointer)
    (payloadAt : Target → Payload) (target : Target)
    (cause : NumericTargetInvalidity) (source : NumericTargetState) :
    let view := NumericComputationRunView.fromSourceOutcomesWithMessages
      pointerAt payloadAt [] [
        { targetField := target
          outcome := .invalidNoValue cause
          source }
      ]
    view.formalErrorsInOperands = [{
      pointer := pointerAt target
      errorCode := berechnungsWertFehler
      messageType := .value
      payload := payloadAt target
    }] ∧ view.noErrorOccurred = false := by
  simp [NumericComputationRunView.fromSourceOutcomesWithMessages,
    NumericComputationRunView.numericValuelessTargetErrors,
    NumericComputationRunView.computedInstancePointers,
    NumericComputationRunView.fromPartitionedSourceOutcomes,
    NumericComputationRunView.noErrorOccurred,
    NumericTargetOutcome.emitsValuelessTargetError,
    NumericTargetOutcome.hasComputedInstance,
    partitionComputationMessages]

theorem numericComputationRun_shouldClear_iff
    {Target : Type} (entry : SourcedNumericTargetOutcome Target) :
    NumericComputationRunView.shouldClear entry = true ↔
      entry.outcome.hasComputedInstance = false ∧
        entry.source.sourceIdentity.isSome = true := by
  simp [NumericComputationRunView.shouldClear]

private theorem numericComputationRun_changedInstance_successful
    {Target : Type} (entry : SourcedNumericTargetOutcome Target)
    (computed : NumericComputedInstance Target)
    (changed :
      NumericComputationRunView.changedInstance? entry = some computed) :
    NumericComputationRunView.successfulInstance? entry = some computed := by
  cases entry with
  | mk target outcome source =>
      cases outcome <;>
        simp_all [NumericComputationRunView.changedInstance?,
          NumericComputationRunView.successfulInstance?]

/-- Every changed success is the identical address-and-payload member of the complete successful collection. -/
theorem numericComputationRun_withChanges_subset
    {Target : Type}
    (residualMessages : List ResidualMessage)
    (entries : List (SourcedNumericTargetOutcome Target))
    (computed : NumericComputedInstance Target)
    (member : computed ∈
      (NumericComputationRunView.fromPartitionedSourceOutcomes
        residualMessages entries).withChanges) :
    computed ∈
      (NumericComputationRunView.fromPartitionedSourceOutcomes
        residualMessages entries).withoutErrors := by
  change computed ∈ entries.filterMap
    NumericComputationRunView.changedInstance? at member
  change computed ∈ entries.filterMap
    NumericComputationRunView.successfulInstance?
  induction entries with
  | nil => simp at member
  | cons entry remaining inductionHypothesis =>
      cases changed :
        NumericComputationRunView.changedInstance? entry with
      | none =>
          simp [changed] at member
          have tailMember : computed ∈ remaining.filterMap
              NumericComputationRunView.changedInstance? :=
            List.mem_filterMap.mpr member
          have tail := inductionHypothesis tailMember
          cases successful :
              NumericComputationRunView.successfulInstance? entry <;>
            simp [successful, tail]
      | some head =>
          have successful :=
            numericComputationRun_changedInstance_successful
              entry head changed
          simp [changed] at member
          simp [successful]
          exact member.elim
            (fun equal => Or.inl equal)
            (fun tail => Or.inr (List.mem_filterMap.mp
              (inductionHypothesis (List.mem_filterMap.mpr tail))))

theorem numericComputationRun_partitioned_formalErrors_exact
    {Target : Type}
    (residualMessages : List ResidualMessage)
    (entries : List (SourcedNumericTargetOutcome Target)) :
    (NumericComputationRunView.fromPartitionedSourceOutcomes
      residualMessages entries).formalErrorsInOperands = residualMessages := by
  rfl

/-- Independently classified clears change only the clear collection, and permutations of those additions are extensionally equal. -/
theorem numericComputationRun_withAdditionalClears_permutation
    {Target : Type}
    (view : NumericComputationRunView ResidualMessage Target)
    (first second : List Target)
    (permutation : first.Perm second) :
    NumericComputationRunView.ExtensionalEq
      (view.withAdditionalClears first)
      (view.withAdditionalClears second) := by
  exact ⟨
    List.Perm.refl _,
    List.Perm.refl _,
    List.Perm.refl _,
    permutation.append_left view.cleared,
    List.Perm.refl _
  ⟩

theorem numericComputationRun_noErrorOccurred_iff
    {Target : Type}
    (view : NumericComputationRunView ResidualMessage Target) :
    view.noErrorOccurred = true ↔
      view.withErrors = [] ∧ view.formalErrorsInOperands = [] := by
  simp [NumericComputationRunView.noErrorOccurred]

/-- Reordering successfully source-classified outcomes or residual messages cannot change the extensional public result. -/
theorem numericComputationRun_fromPartitionedSourceOutcomes_permutation
    {Target : Type}
    (firstMessages secondMessages : List ResidualMessage)
    (firstEntries secondEntries : List (SourcedNumericTargetOutcome Target))
    (messagesPermutation : firstMessages.Perm secondMessages)
    (entriesPermutation : firstEntries.Perm secondEntries) :
    NumericComputationRunView.ExtensionalEq
      (NumericComputationRunView.fromPartitionedSourceOutcomes
        firstMessages firstEntries)
      (NumericComputationRunView.fromPartitionedSourceOutcomes
        secondMessages secondEntries) := by
  exact ⟨
    entriesPermutation.filterMap _,
    entriesPermutation.filterMap _,
    entriesPermutation.filterMap _,
    (entriesPermutation.filter _).map _,
    messagesPermutation
  ⟩

/-- Reordering supplied messages or source-classified outcomes cannot change the faithful extensional Number result. -/
theorem numericComputationRun_fromSourceOutcomesWithMessages_permutation
    (pointerAt : Target → ComputationErrorPointer)
    (payloadAt : Target → Payload)
    (firstMessages secondMessages : List (ComputationFormalMessage Payload))
    (firstEntries secondEntries : List (SourcedNumericTargetOutcome Target))
    (messagesPermutation : firstMessages.Perm secondMessages)
    (entriesPermutation : firstEntries.Perm secondEntries) :
    NumericComputationRunView.ExtensionalEq
      (NumericComputationRunView.fromSourceOutcomesWithMessages
        pointerAt payloadAt firstMessages firstEntries)
      (NumericComputationRunView.fromSourceOutcomesWithMessages
        pointerAt payloadAt secondMessages secondEntries) := by
  have pointersPermutation :
      (NumericComputationRunView.computedInstancePointers
        pointerAt firstEntries).Perm
      (NumericComputationRunView.computedInstancePointers
        pointerAt secondEntries) := by
    exact entriesPermutation.filterMap _
  have emittedPermutation :
      (NumericComputationRunView.numericValuelessTargetErrors
        pointerAt payloadAt firstEntries).Perm
      (NumericComputationRunView.numericValuelessTargetErrors
        pointerAt payloadAt secondEntries) := by
    exact entriesPermutation.filterMap _
  have allMessagesPermutation :=
    messagesPermutation.append emittedPermutation
  let firstPointers := NumericComputationRunView.computedInstancePointers pointerAt firstEntries
  let secondPointers :=
    NumericComputationRunView.computedInstancePointers pointerAt secondEntries
  have predicateEquality :
      (fun message : ComputationFormalMessage Payload =>
        !firstPointers.contains message.pointer) =
      (fun message : ComputationFormalMessage Payload =>
        !secondPointers.contains message.pointer) := by
    funext message
    rw [pointersPermutation.contains_eq]
  have residualPermutation :
      ((firstMessages ++
          NumericComputationRunView.numericValuelessTargetErrors
            pointerAt payloadAt firstEntries).filter fun message =>
        !firstPointers.contains message.pointer).Perm
      ((secondMessages ++
          NumericComputationRunView.numericValuelessTargetErrors
            pointerAt payloadAt secondEntries).filter fun message =>
        !secondPointers.contains message.pointer) := by
    rw [predicateEquality]
    exact allMessagesPermutation.filter _
  simpa [NumericComputationRunView.fromSourceOutcomesWithMessages,
    partitionComputationMessages, firstPointers, secondPointers] using
    numericComputationRun_fromPartitionedSourceOutcomes_permutation
      _ _ _ _ residualPermutation entriesPermutation

end A12Kernel
