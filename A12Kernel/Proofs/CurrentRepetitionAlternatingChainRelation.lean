import A12Kernel.Elaboration.CurrentRepetitionAlternatingChainRelation

/-! # CurrentRepetition alternating-chain transition laws -/

namespace A12Kernel

/-- Every successful fixed alternating execution is exactly three complete typed transitions whose phases reconstruct the returned rows. -/
theorem currentRepetitionAlternatingChain_execute_transition_trace
    (plan : CheckedCurrentRepetitionAlternatingChain model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (outcomes : CurrentRepetitionAlternatingChainOutcomes)
    (executed : plan.execute patterns input = .ok outcomes) :
    ∃ number string third,
      CurrentRepetitionAlternatingChainTransition plan patterns input
        {} { number := some number } ∧
      CurrentRepetitionAlternatingChainTransition plan patterns input
        { number := some number }
        { number := some number, string := some string } ∧
      CurrentRepetitionAlternatingChainTransition plan patterns input
        { number := some number, string := some string }
        { number := some number, string := some string, third := some third } ∧
      CheckedCurrentRepetitionAlternatingChain.assemblePhases
        number string third = outcomes := by
  unfold CheckedCurrentRepetitionAlternatingChain.execute at executed
  cases numberResult :
      plan.numberToString.executeNumberPhaseWithRead input input.read with
  | error cause =>
      simp [numberResult, Except.mapError, Bind.bind, Except.bind] at executed
  | ok number =>
      cases stringResult :
          plan.numberToString.executeStringPhase patterns input number with
      | error cause =>
          simp [numberResult, stringResult, Except.mapError,
            Bind.bind, Except.bind] at executed
      | ok string =>
          cases thirdResult : plan.executeThirdPhase input string with
          | error cause =>
              simp [numberResult, stringResult, thirdResult, Except.mapError,
                Bind.bind, Except.bind] at executed
          | ok third =>
              simp [numberResult, stringResult, thirdResult, Except.mapError,
                Bind.bind, Except.bind] at executed
              cases executed
              exact ⟨number, string, third,
                .number number numberResult,
                .string number string stringResult,
                .third number string third thirdResult, rfl⟩

/-- Neither dependent family can appear in the initial successful transition. -/
theorem currentRepetitionAlternatingChain_initial_transition_has_no_dependents
    (plan : CheckedCurrentRepetitionAlternatingChain model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (next : CurrentRepetitionAlternatingChainState)
    (transition : CurrentRepetitionAlternatingChainTransition
      plan patterns input {} next) :
    next.string = none ∧ next.third = none := by
  cases transition
  exact ⟨rfl, rfl⟩

/-- A failed fixed alternating chain retains no partial terminal Number
completion at any of its three structural fault positions. -/
theorem currentRepetitionAlternatingChain_failureTrace_has_no_third
    (trace : CurrentRepetitionAlternatingChainFailureTrace
      plan patterns input state fault) :
    state.third = none := by
  cases trace <;> rfl

/-- Every structural failure of the fixed alternating executor occurs before
Number, after the exact Number phase, or after the exact Number and String
prefix. The indexed trace state is the unchanged successful prefix. -/
theorem currentRepetitionAlternatingChain_execute_failure_trace
    (plan : CheckedCurrentRepetitionAlternatingChain model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (fault : CurrentRepetitionAlternatingChainFault)
    (executed : plan.execute patterns input = .error fault) :
    ∃ state,
      CurrentRepetitionAlternatingChainFailureTrace
        plan patterns input state fault := by
  unfold CheckedCurrentRepetitionAlternatingChain.execute at executed
  cases numberResult :
      plan.numberToString.executeNumberPhaseWithRead input input.read with
  | error cause =>
      simp only [numberResult, Except.mapError, Bind.bind, Except.bind]
        at executed
      change Except.error (.numberToString cause) =
        Except.error fault at executed
      cases executed
      exact ⟨{}, .number (.number cause numberResult)⟩
  | ok number =>
      simp only [numberResult, Except.mapError, Bind.bind, Except.bind]
        at executed
      cases stringResult :
          plan.numberToString.executeStringPhase patterns input number with
      | error cause =>
          rw [stringResult] at executed
          change Except.error (.numberToString cause) =
            Except.error fault at executed
          cases executed
          exact ⟨{ number := some number },
            .string (.number number numberResult)
              (.string number cause stringResult)⟩
      | ok string =>
          simp only [stringResult] at executed
          cases thirdResult : plan.executeThirdPhase input string with
          | error cause =>
              rw [thirdResult] at executed
              change Except.error cause = Except.error fault at executed
              cases executed
              exact ⟨{ number := some number, string := some string },
                .third (.number number numberResult)
                  (.string number string stringResult)
                  (.third number string fault thirdResult)⟩
          | ok third =>
              rw [thirdResult] at executed
              change Except.ok
                  (CheckedCurrentRepetitionAlternatingChain.assemblePhases
                    number string third) = Except.error fault at executed
              cases executed

end A12Kernel
