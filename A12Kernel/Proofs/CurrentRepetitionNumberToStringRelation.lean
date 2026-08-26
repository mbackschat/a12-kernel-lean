import A12Kernel.Elaboration.CurrentRepetitionNumberToStringRelation

/-! # CurrentRepetition Number-to-String transition laws -/

namespace A12Kernel

/-- Every successful fixed execution is exactly one complete Number transition followed by one dependent String transition, and those phases reconstruct the returned typed rows. -/
theorem currentRepetitionNumberToString_executeWithRead_transition_trace
    (plan : CheckedCurrentRepetitionNumberToStringCascade model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (outcomes : CurrentRepetitionNumberToStringOutcomes)
    (executed : plan.executeWithRead patterns input read = .ok outcomes) :
    ∃ number string,
      CurrentRepetitionNumberToStringTransition plan patterns input read
        {} { number := some number } ∧
      CurrentRepetitionNumberToStringTransition plan patterns input read
        { number := some number }
        { number := some number, string := some string } ∧
      CheckedCurrentRepetitionNumberToStringCascade.assemblePhases
        number string = outcomes := by
  unfold CheckedCurrentRepetitionNumberToStringCascade.executeWithRead at executed
  cases numberResult : plan.executeNumberPhaseWithRead input read with
  | error cause =>
      simp [numberResult, Bind.bind, Except.bind] at executed
  | ok number =>
      cases stringResult : plan.executeStringPhase patterns input number with
      | error cause =>
          simp [numberResult, stringResult, Bind.bind, Except.bind] at executed
      | ok string =>
          simp [numberResult, stringResult, Bind.bind, Except.bind] at executed
          cases executed
          exact ⟨number, string, .number number numberResult,
            .string number string stringResult, rfl⟩

/-- The dependent String phase cannot be the first successful transition. -/
theorem currentRepetitionNumberToString_initial_transition_has_no_string
    (plan : CheckedCurrentRepetitionNumberToStringCascade model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (next : CurrentRepetitionNumberToStringState)
    (transition : CurrentRepetitionNumberToStringTransition
      plan patterns input read {} next) :
    next.string = none := by
  cases transition
  rfl

/-- A failed fixed cascade retains no partial String completion, whether it
stopped before Number execution or at the dependent String boundary. -/
theorem currentRepetitionNumberToString_failureTrace_has_no_string
    (plan : CheckedCurrentRepetitionNumberToStringCascade model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (state : CurrentRepetitionNumberToStringState)
    (fault : CurrentRepetitionNumberToStringFault)
    (trace : CurrentRepetitionNumberToStringFailureTrace
      plan patterns input read state fault) :
    state.string = none := by
  cases trace <;> rfl

/-- Every structural failure of the fixed executor is either its initial
Number-phase failure or one String-phase failure after the exact complete Number
phase. The trace's indexed state is the unchanged successful prefix. -/
theorem currentRepetitionNumberToString_executeWithRead_failure_trace
    (plan : CheckedCurrentRepetitionNumberToStringCascade model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (fault : CurrentRepetitionNumberToStringFault)
    (executed : plan.executeWithRead patterns input read = .error fault) :
    ∃ state,
      CurrentRepetitionNumberToStringFailureTrace
        plan patterns input read state fault := by
  unfold CheckedCurrentRepetitionNumberToStringCascade.executeWithRead at executed
  cases numberResult : plan.executeNumberPhaseWithRead input read with
  | error cause =>
      rw [numberResult] at executed
      change Except.error cause = Except.error fault at executed
      cases executed
      exact ⟨{}, .number (.number fault numberResult)⟩
  | ok number =>
      simp only [numberResult, Bind.bind, Except.bind] at executed
      cases stringResult : plan.executeStringPhase patterns input number with
      | error cause =>
          rw [stringResult] at executed
          change Except.error cause = Except.error fault at executed
          cases executed
          exact ⟨{ number := some number },
            .string (.number number numberResult)
              (.string number fault stringResult)⟩
      | ok string =>
          rw [stringResult] at executed
          change Except.ok
              (CheckedCurrentRepetitionNumberToStringCascade.assemblePhases
                number string) = Except.error fault at executed
          cases executed

end A12Kernel
