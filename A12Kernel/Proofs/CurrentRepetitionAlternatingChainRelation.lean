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

end A12Kernel
