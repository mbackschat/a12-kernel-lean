import A12Kernel.Semantics.RepetitionNotUnique

/-! # Resolved `RepetitionNotUnique` laws

These laws cover duplicate construction and per-row verdicts after scope selection, path expansion, and key-cell classification. They do not prove checked `@From` resolution, partial relevance, message-pointer projection, or whole-rule lowering.
-/

namespace A12Kernel

@[simp]
theorem repetitionKey_checkedToken_value_exact (value : String) :
    RepetitionKeyComponent.ofCheckedTokenCell {
      rawPresent := true
      parsed := some value
      findings := []
    } = .present (.token value) := by
  rfl

@[simp]
theorem repetitionKey_checkedToken_empty_exact (rawPresent : Bool) :
    RepetitionKeyComponent.ofCheckedTokenCell {
      rawPresent
      parsed := none
      findings := []
    } = .empty := by
  rfl

@[simp]
theorem repetitionKey_checkedToken_rejection_exact (cause : FormalCause) :
    RepetitionKeyComponent.ofCheckedTokenCell {
      rawPresent := true
      parsed := (none : Option String)
      findings := [cause]
    } = .unknown cause := by
  rfl

/-- A custom validator's complete project rejection survives key classification, making the row ineligible without collapsing the cause to a generic invalid-key marker. -/
theorem repetitionKey_registeredCustomRejection_exact
    (rejection : RegisteredCustomRejection) :
    RepetitionKeyComponent.ofCheckedTokenCell {
      rawPresent := true
      parsed := (none : Option String)
      findings := [.registeredCustomValidation rejection]
    } = .unknown (.registeredCustomValidation rejection) := by
  rfl

/-- Numeric key equality is exactly equality after the shared scale-19 normalization. -/
theorem repetitionKey_number_equal_iff_normalized_eq (left right : Rat) :
    RepetitionKeyAtom.equal (.number left) (.number right) = true ↔
      normalizedComparisonValue left = normalizedComparisonValue right := by
  simp [RepetitionKeyAtom.equal, ValueListAtom.equal, NumericComparisonOp.holds]

/-- Duplicate membership is precisely ordered scope membership plus eligibility and typed key equality. -/
theorem mem_repetitionDuplicateCluster_iff
    (rows : List ResolvedRepetitionKeyRow)
    (target candidate : ResolvedRepetitionKeyRow) :
    candidate ∈ repetitionDuplicateCluster rows target ↔
      target.eligible = true ∧
        candidate ∈ rows ∧ candidate.eligible = true ∧ target.sameKey candidate = true := by
  cases eligible : target.eligible <;>
    simp [repetitionDuplicateCluster, eligible]

/-- Equality is reflexive for every admitted key atom. -/
private theorem repetitionKeyAtom_equal_self (atom : RepetitionKeyAtom) :
    atom.equal atom = true := by
  cases atom <;>
    simp [RepetitionKeyAtom.equal, ValueListAtom.equal,
      NumericComparisonOp.holds]

/-- A key whose components are all known equals itself. -/
private theorem repetitionKeyEqual_self_of_known
    (key : List RepetitionKeyComponent)
    (known :
      ∀ component ∈ key, component.isUnknown = false) :
    repetitionKeyEqual key key = true := by
  induction key with
  | nil =>
      rfl
  | cons head rest ih =>
      have headKnown : head.isUnknown = false :=
        known head (by simp)
      have restKnown :
          ∀ component ∈ rest, component.isUnknown = false := by
        intro component componentInRest
        exact known component (by simp [componentInRest])
      cases head with
      | present atom =>
          simp [repetitionKeyEqual, RepetitionKeyComponent.equal,
            repetitionKeyAtom_equal_self, ih restKnown]
      | empty =>
          simp [repetitionKeyEqual, RepetitionKeyComponent.equal, ih restKnown]
      | unknown cause =>
          simp [RepetitionKeyComponent.isUnknown] at headKnown

/-- An eligible target occurs in its own typed-key equivalence class. -/
private theorem repetitionKeyRow_sameKey_self_of_eligible
    (target : ResolvedRepetitionKeyRow)
    (eligible : target.eligible = true) :
    target.sameKey target = true := by
  have eligibility := eligible
  simp [ResolvedRepetitionKeyRow.eligible] at eligibility
  have known :
      ∀ component ∈ target.key, component.isUnknown = false := by
    simpa [ResolvedRepetitionKeyRow.hasUnknown] using eligibility.1
  exact repetitionKeyEqual_self_of_known target.key known

/-- A formally invalid current key is retained as Lean `unknown`, although the kernel's external `FALSE_OR_UNKNOWN` result does not distinguish it from a unique row. -/
theorem repetitionNotUnique_refinedUnknown_iff
    (rows : List ResolvedRepetitionKeyRow)
    (target : ResolvedRepetitionKeyRow) :
    (evalRepetitionNotUniqueRow rows target).verdict = .unknown ↔
      target.hasUnknown = true := by
  cases unknown : target.hasUnknown with
  | false =>
      cases present : target.hasPresent with
      | false =>
          simp [evalRepetitionNotUniqueRow, unknown, present]
      | true =>
          by_cases duplicate :
              2 ≤ (repetitionDuplicateCluster rows target).length <;>
            simp [evalRepetitionNotUniqueRow, unknown, present, duplicate]
  | true =>
      simp [evalRepetitionNotUniqueRow, unknown]

/-- A firing target is eligible for the duplicate relation. -/
private theorem repetitionNotUnique_fired_eligible
    (rows : List ResolvedRepetitionKeyRow)
    (target : ResolvedRepetitionKeyRow)
    (p : Polarity)
    (fired :
      (evalRepetitionNotUniqueRow rows target).verdict = .fired p) :
    target.eligible = true := by
  cases unknown : target.hasUnknown <;>
    cases present : target.hasPresent <;>
      by_cases duplicate : 2 ≤ (repetitionDuplicateCluster rows target).length <;>
        simp [evalRepetitionNotUniqueRow, ResolvedRepetitionKeyRow.eligible,
          unknown, present, duplicate] at fired ⊢

/-- A known all-empty key is skipped. -/
theorem repetitionNotUnique_allEmpty_notFired
    (rows : List ResolvedRepetitionKeyRow)
    (target : ResolvedRepetitionKeyRow)
    (known : target.hasUnknown = false)
    (allEmpty : target.hasPresent = false) :
    evalRepetitionNotUniqueRow rows target =
      { row := target.row, verdict := .notFired, cluster := [] } := by
  simp [evalRepetitionNotUniqueRow, known, allEmpty]

/-- For an eligible current row, firing is equivalent to having at least two members in its complete duplicate cluster, and the polarity is determined solely by whether the key contains a valid empty component. -/
theorem repetitionNotUnique_fired_iff_of_eligible
    (rows : List ResolvedRepetitionKeyRow)
    (target : ResolvedRepetitionKeyRow)
    (p : Polarity)
    (known : target.hasUnknown = false)
    (present : target.hasPresent = true) :
    (evalRepetitionNotUniqueRow rows target).verdict = .fired p ↔
      2 ≤ (repetitionDuplicateCluster rows target).length ∧
        p = if target.hasEmpty then .omission else .value := by
  by_cases duplicate : 2 ≤ (repetitionDuplicateCluster rows target).length
  · have reduced :
        (evalRepetitionNotUniqueRow rows target).verdict =
          .fired (if target.hasEmpty then .omission else .value) := by
      simp [evalRepetitionNotUniqueRow, known, present, duplicate]
    rw [reduced]
    simp only [Verdict.fired.injEq, duplicate, true_and]
    exact eq_comm
  · simp [evalRepetitionNotUniqueRow, known, present, duplicate]

/-- Every firing exposes the complete duplicate cluster in the direct evaluator's scope order. Pointer projection may later use a weaker extensional observation. -/
theorem repetitionNotUnique_fired_cluster
    (rows : List ResolvedRepetitionKeyRow)
    (target : ResolvedRepetitionKeyRow)
    (p : Polarity)
    (fired :
      (evalRepetitionNotUniqueRow rows target).verdict = .fired p) :
    (evalRepetitionNotUniqueRow rows target).cluster =
      (repetitionDuplicateCluster rows target).map (·.row) := by
  cases unknown : target.hasUnknown <;>
    cases present : target.hasPresent <;>
      by_cases duplicate : 2 ≤ (repetitionDuplicateCluster rows target).length <;>
        simp [evalRepetitionNotUniqueRow, unknown, present, duplicate] at fired ⊢

/-- Filtering a well-formed scope preserves uniqueness of complete row identities in every duplicate cluster. -/
theorem repetitionDuplicateCluster_identities_nodup
    (rows : List ResolvedRepetitionKeyRow)
    (target : ResolvedRepetitionKeyRow)
    (wellFormed : ResolvedRepetitionKeyRows.WellFormed rows) :
    ((repetitionDuplicateCluster rows target).map (·.row)).Nodup := by
  unfold ResolvedRepetitionKeyRows.WellFormed at wellFormed
  unfold repetitionDuplicateCluster
  split
  · exact
      (List.filter_sublist.map
        (fun candidate : ResolvedRepetitionKeyRow => candidate.row)).nodup wellFormed
  · simp

/-- Two distinct elements exist in any duplicate-free list whose length is at least two; at least one differs from an arbitrary target. -/
private theorem exists_mem_ne_of_two_le_length_of_nodup
    {values : List Env}
    (target : Env)
    (length : 2 ≤ values.length)
    (nodup : values.Nodup) :
    ∃ value, value ∈ values ∧ value ≠ target := by
  cases values with
  | nil =>
      simp at length
  | cons first rest =>
      cases rest with
      | nil =>
          simp at length
      | cons second tail =>
          have firstNeSecond : first ≠ second := by
            simp only [List.nodup_cons] at nodup
            intro firstEqSecond
            exact nodup.1 (by simp [firstEqSecond])
          by_cases firstEq : first = target
          · refine ⟨second, by simp, ?_⟩
            intro secondEq
            exact firstNeSecond (firstEq.trans secondEq.symm)
          · exact ⟨first, by simp, firstEq⟩

/-- Under the resolved scope obligations, every firing contains the target and at least one genuinely distinct peer. The cluster-membership characterization supplies that peer's scope membership, eligibility, and matching typed key. -/
theorem repetitionNotUnique_firing_has_distinct_peer
    (rows : List ResolvedRepetitionKeyRow)
    (target : ResolvedRepetitionKeyRow)
    (p : Polarity)
    (wellFormed : ResolvedRepetitionKeyRows.WellFormed rows)
    (targetInScope : target ∈ rows)
    (fired :
      (evalRepetitionNotUniqueRow rows target).verdict = .fired p) :
    target ∈ repetitionDuplicateCluster rows target ∧
      ∃ peer, peer ∈ repetitionDuplicateCluster rows target ∧
        peer.row ≠ target.row := by
  have eligible := repetitionNotUnique_fired_eligible rows target p fired
  have targetInCluster :
      target ∈ repetitionDuplicateCluster rows target :=
    (mem_repetitionDuplicateCluster_iff rows target target).2
      ⟨eligible, targetInScope, eligible,
        repetitionKeyRow_sameKey_self_of_eligible target eligible⟩
  have eligibility := eligible
  simp [ResolvedRepetitionKeyRow.eligible] at eligibility
  have clusterLength :
      2 ≤ (repetitionDuplicateCluster rows target).length :=
    ((repetitionNotUnique_fired_iff_of_eligible rows target p
      eligibility.1 eligibility.2).1 fired).1
  have identityNodup :=
    repetitionDuplicateCluster_identities_nodup rows target wellFormed
  obtain ⟨peerIdentity, peerIdentityInCluster, peerIdentityNe⟩ :=
    exists_mem_ne_of_two_le_length_of_nodup
      target.row (by simpa using clusterLength) identityNodup
  simp only [List.mem_map] at peerIdentityInCluster
  obtain ⟨peer, peerInCluster, peerIdentityEq⟩ := peerIdentityInCluster
  have peerIdentityNeTarget : peer.row ≠ target.row := by
    intro peerEq
    exact peerIdentityNe (peerIdentityEq.symm.trans peerEq)
  exact ⟨targetInCluster, peer, peerInCluster, peerIdentityNeTarget⟩

end A12Kernel
