import A12Kernel.Elaboration.CurrentRepetitionStringToNumberRelation

/-! # CurrentRepetition String-to-Number transition laws -/

namespace A12Kernel

/-- Every successful fixed inverse execution is exactly one complete String transition followed by one dependent Number transition, and those phases reconstruct the returned typed rows. -/
theorem currentRepetitionStringToNumber_execute_transition_trace
    (plan : CheckedCurrentRepetitionStringToNumberCascade model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (outcomes : CurrentRepetitionStringToNumberOutcomes)
    (executed : plan.execute patterns input = .ok outcomes) :
    ∃ string number,
      CurrentRepetitionStringToNumberTransition plan patterns input
        {} { string := some string } ∧
      CurrentRepetitionStringToNumberTransition plan patterns input
        { string := some string }
        { string := some string, number := some number } ∧
      CheckedCurrentRepetitionStringToNumberCascade.assemblePhases
        string number = outcomes := by
  unfold CheckedCurrentRepetitionStringToNumberCascade.execute at executed
  cases stringResult : plan.executeStringPhase patterns input with
  | error cause =>
      simp [stringResult, Bind.bind, Except.bind] at executed
  | ok string =>
      cases numberResult : plan.executeNumberPhase input string with
      | error cause =>
          simp [stringResult, numberResult, Bind.bind, Except.bind] at executed
      | ok number =>
          simp [stringResult, numberResult, Bind.bind, Except.bind] at executed
          cases executed
          exact ⟨string, number, .string string stringResult,
            .number string number numberResult, rfl⟩

/-- The dependent Number phase cannot be the first successful transition. -/
theorem currentRepetitionStringToNumber_initial_transition_has_no_number
    (plan : CheckedCurrentRepetitionStringToNumberCascade model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (next : CurrentRepetitionStringToNumberState)
    (transition : CurrentRepetitionStringToNumberTransition
      plan patterns input {} next) :
    next.number = none := by
  cases transition
  rfl

/-- A failed fixed inverse cascade retains no partial Number completion, whether
it stopped before String execution or at the dependent Number boundary. -/
theorem currentRepetitionStringToNumber_failureTrace_has_no_number
    (trace : CurrentRepetitionStringToNumberFailureTrace
      plan patterns input state fault) :
    state.number = none := by
  cases trace <;> rfl

/-- Every structural failure of the fixed inverse executor is either its initial
String-phase failure or one Number-phase failure after the exact complete String
phase. The trace's indexed state is the unchanged successful prefix. -/
theorem currentRepetitionStringToNumber_execute_failure_trace
    (plan : CheckedCurrentRepetitionStringToNumberCascade model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (fault : CurrentRepetitionStringToNumberFault)
    (executed : plan.execute patterns input = .error fault) :
    ∃ state,
      CurrentRepetitionStringToNumberFailureTrace
        plan patterns input state fault := by
  unfold CheckedCurrentRepetitionStringToNumberCascade.execute at executed
  cases stringResult : plan.executeStringPhase patterns input with
  | error cause =>
      rw [stringResult] at executed
      change Except.error cause = Except.error fault at executed
      cases executed
      exact ⟨{}, .string (.string fault stringResult)⟩
  | ok string =>
      simp only [stringResult, Bind.bind, Except.bind] at executed
      cases numberResult : plan.executeNumberPhase input string with
      | error cause =>
          rw [numberResult] at executed
          change Except.error cause = Except.error fault at executed
          cases executed
          exact ⟨{ string := some string },
            .number (.string string stringResult)
              (.number string fault numberResult)⟩
      | ok number =>
          rw [numberResult] at executed
          change Except.ok
              (CheckedCurrentRepetitionStringToNumberCascade.assemblePhases
                string number) = Except.error fault at executed
          cases executed

end A12Kernel
