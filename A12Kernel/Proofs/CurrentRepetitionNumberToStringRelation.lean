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

end A12Kernel
