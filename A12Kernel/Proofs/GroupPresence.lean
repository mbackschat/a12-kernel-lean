import A12Kernel.Semantics.GroupPresence

/-! # Laws for resolved validation group presence -/

namespace A12Kernel

theorem groupFilled_fired_iff (state : GroupPresenceState) :
    state.groupFilled = .fired .value ↔
      state.relevance ≠ .noneRelevant ∧ state.content = true := by
  cases state with
  | mk content erroneous relevance =>
      cases content <;> cases relevance <;> simp [GroupPresenceState.groupFilled]

theorem groupNotFilled_fired_iff (state : GroupPresenceState) :
    state.groupNotFilled = .fired .omission ↔
      state.relevance = .fullyRelevant ∧ state.content = false ∧ state.erroneous = false := by
  cases state with
  | mk content erroneous relevance =>
      cases content <;> cases erroneous <;> cases relevance <;>
        simp [GroupPresenceState.groupNotFilled]

theorem groupPresence_rowContent_admitted (input : ResolvedGroupPresenceInput)
    (row : input.hasInstantiatedRow = true) : input.derive.content = true := by
  simp [ResolvedGroupPresenceInput.derive, row]

/-- A call-local silent field failure contributes to group error without requiring a fabricated checked-cell finding. -/
theorem groupPresence_silentError_erroneous
    (input : ResolvedGroupPresenceInput)
    (silent : input.silentError = true) :
    input.derive.erroneous = true := by
  simp [ResolvedGroupPresenceInput.derive, silent]

theorem checkedCell_duplicate_preservesGroupAdmission (cell : CheckedCell)
    (parsed : cell.parsed.isSome = true)
    (findings : cell.findings = [.duplicateIndex]) : cell.admitsGroupContent = true := by
  simp [CheckedCell.admitsGroupContent, parsed, findings, FormalCause.preservesGroupAdmission]

theorem checkedCell_rejected_notGroupContent (cause : BaseFormalCause) :
    (formalCheck { kind := .number { scale := 0, signed := false } }
      (.rejected cause)).admitsGroupContent = false := by
  cases cause <;> rfl

theorem groupListPresenceTally_partition
    (states : List GroupListPresenceState) :
    let tally := GroupListPresenceTally.ofStates states
    tally.filled + tally.empty + tally.unavailable = states.length := by
  induction states with
  | nil => rfl
  | cons state rest ih =>
      cases state <;>
        simp [GroupListPresenceTally.ofStates] at * <;>
        omega

theorem groupPresenceTally_partition (states : List GroupPresenceState) :
    let tally := GroupListPresenceTally.ofGroupStates states
    tally.filled + tally.empty + tally.unavailable = states.length := by
  simpa [GroupListPresenceTally.ofGroupStates] using
    groupListPresenceTally_partition
      (states.map GroupPresenceState.asGroupListPresence)

theorem validationFillOutcome_conservative_fired_iff
    (outcome : ValidationFillOutcome) (polarity : Polarity) :
    outcome.asConservativeVerdict = .fired polarity ↔
      outcome = .fired polarity := by
  cases outcome <;> simp [ValidationFillOutcome.asConservativeVerdict]

theorem erroneousHead_makesFilledGroupCountUnknown
    (state : GroupPresenceState) (rest : List GroupPresenceState)
    (erroneous : state.erroneous = true) :
    numberOfFilledGroups (state :: rest) = .unknown := by
  simp [numberOfFilledGroups, erroneous]

theorem relativeRequiredness_uses_positivePresence (state : GroupPresenceState) :
    state.activatesRelativeRequiredness = state.definitelyFilled := rfl

end A12Kernel
