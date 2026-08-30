import A12Kernel.Semantics.GroupPresence

/-! # Laws for resolved group presence in both evaluation arms -/

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

/-- The measured divergence is directional, and this states that direction with no
    hypothesis at all: whenever the validation arm admits a cell as group content, the
    computation arm also counts it present. The converse fails, and that failure is the
    whole content of the inversion — a formally invalid cell is counted here and rejected
    there. Holds on the full domain, including the invalid cells the clean-agreement law
    below says nothing about. -/
theorem admitsGroupContent_le_presentForComputation (cell : CheckedCell)
    (admits : cell.admitsGroupContent = true) :
    (observeCell .computation cell).presentForComputation = true := by
  -- A present parsed value rules out the only absent branch of the phase read, whatever
  -- finding that read selects, so no case analysis on the findings themselves is needed.
  cases hParsed : cell.parsed with
  | none => simp [CheckedCell.admitsGroupContent, hParsed] at admits
  | some value =>
      simp only [observeCell, hParsed]
      split <;> simp_all [CellObservation.presentForComputation]

/-- On a cell carrying no finding the two arms' cell-level presence projections coincide.
    Together with the monotonicity law above this confines the arms' disagreement to cells
    that carry a finding. It says nothing about a cell that carries one, which is exactly
    where the measurement lives. -/
theorem presentForComputation_eq_admitsGroupContent_of_clean (cell : CheckedCell)
    (clean : cell.findings.isEmpty = true) :
    (observeCell .computation cell).presentForComputation =
      cell.admitsGroupContent := by
  cases cell with
  | mk rawPresent parsed findings =>
      cases findings with
      | nil => cases parsed <;> rfl
      | cons _ _ => simp at clean

/-- The list-level form of the clean-region agreement, used to lift it to a whole group. -/
theorem any_presentForComputation_eq_any_admitsGroupContent :
    ∀ cells : List CheckedCell,
      cells.all (fun cell => cell.findings.isEmpty) = true →
      (cells.map (observeCell .computation)).any
          CellObservation.presentForComputation =
        cells.any CheckedCell.admitsGroupContent
  | [], _ => rfl
  | cell :: rest, clean => by
      simp only [List.all_cons, Bool.and_eq_true] at clean
      simp only [List.map_cons, List.any_cons,
        presentForComputation_eq_admitsGroupContent_of_clean cell clean.1,
        any_presentForComputation_eq_any_admitsGroupContent rest clean.2]

/-- In the clean region the two arms' group-level presence projections agree: over
    descendant cells that carry no finding, and with no repeatable row supplying content,
    the computation arm's presence is exactly the validation arm's `content`.

    Scope is deliberately narrow, and the hypotheses are the statement. This says nothing
    about the validation state's `hasInstantiatedRow`, `structuralError`, `silentError`, or
    `relevance` dimensions — the computation projection consumes none of them, and SG13
    records all of them as uncovered by the retained observation. What it does establish,
    with `admitsGroupContent_le_presentForComputation`, is that the arms' descendant-content
    disagreement is confined to cells carrying a finding. -/
theorem groupPresentForComputation_eq_content_of_clean
    (input : ResolvedGroupPresenceInput)
    (rows : input.hasInstantiatedRow = false)
    (clean : input.descendantCells.all (fun cell => cell.findings.isEmpty) = true) :
    groupPresentForComputation
        (input.descendantCells.map (observeCell .computation)) =
      input.derive.content := by
  simp only [ResolvedGroupPresenceInput.derive, rows, Bool.false_or,
    groupPresentForComputation]
  exact any_presentForComputation_eq_any_admitsGroupContent input.descendantCells clean

/-- Splitting an operand list splits its count. This is the law behind "the contributions add":
    a consumer may decompose a mixed list into its fixed and starred parts, or read one operand's
    share off the total, without the operator's fold having to be re-derived per shape. -/
theorem numberOfFilledGroupsForComputationOperands_append
    (left right : List GroupCountOperandReading) :
    numberOfFilledGroupsForComputationOperands (left ++ right) =
      numberOfFilledGroupsForComputationOperands left +
        numberOfFilledGroupsForComputationOperands right := by
  induction left with
  | nil => simp [numberOfFilledGroupsForComputationOperands]
  | cons operand rest ih =>
      simp [numberOfFilledGroupsForComputationOperands, ih, Nat.add_assoc]

/-- The mixed operand fold **generalizes** the established plain multi-group count rather than
    competing with it: over a list of fixed operands the two agree.

    This is the statement that keeps the starred operand from silently restating the fixed one.
    Its direction matters — it constrains the new clause by the measured old one, not the
    reverse — and it says nothing about a list containing a starred operand, whose contribution
    the plain count cannot express at any width. -/
theorem numberOfFilledGroupsForComputationOperands_fixed
    (groups : List (List CellObservation)) :
    numberOfFilledGroupsForComputationOperands
        (groups.map GroupCountOperandReading.fixed) =
      numberOfFilledGroupsForComputation groups := by
  induction groups with
  | nil => rfl
  | cons cells rest ih =>
      simp only [List.map_cons, numberOfFilledGroupsForComputationOperands, ih,
        GroupCountOperandReading.contribution, numberOfFilledGroupsForComputation,
        List.countP_cons]
      cases groupPresentForComputation cells <;> simp [Nat.add_comm]

end A12Kernel
