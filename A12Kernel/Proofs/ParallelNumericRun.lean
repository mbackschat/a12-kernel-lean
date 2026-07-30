import A12Kernel.Elaboration.ParallelNumericRun
import A12Kernel.Proofs.ComputationRunPlan
import A12Kernel.Proofs.FieldId
import A12Kernel.Proofs.ParallelNumericAlternativeTable

/-! # Checked parallel Number run-overlay laws -/

namespace A12Kernel

theorem checkedParallelNumericPlan_targetFields_nodup
    (plan : CheckedParallelNumericPlan model) :
    plan.targetFields.Nodup := by
  exact (fieldId_firstDuplicate_none_iff_nodup _).mp
    plan.uniqueTargets

/-- A certified table cannot read the target of any later supplied table. This no-later-read result is the exact cross-table dependency-order guarantee; each table's separate target-exclusion theorem owns self-reference. -/
theorem checkedParallelNumericPlan_references_later_false
    (plan : CheckedParallelNumericPlan model)
    (earlier later :
      List (CheckedParallelNumericAlternativeTable model))
    (consumer producer : CheckedParallelNumericAlternativeTable model)
    (split : plan.tables = earlier ++ consumer :: later)
    (member : producer ∈ later) :
    consumer.referencesField producer.targetField = false := by
  have ordered :
      firstForwardComputationDependency?
        (·.targetField) (·.referencesField ·) plan.tables = none := by
    simpa [firstForwardParallelNumericDependency?] using
      plan.dependenciesOrdered
  rw [split] at ordered
  have suffix :=
    firstForwardComputationDependency_none_suffix
      (·.targetField) (·.referencesField ·)
      earlier (consumer :: later) ordered
  exact firstForwardComputationDependency_none_head
    (·.targetField) (·.referencesField ·)
    consumer later suffix producer member

theorem parallelNumericPlan_read_pending
    (plan : CheckedParallelNumericPlan model)
    (state : ParallelNumericRunState) (input : CheckedDocument model)
    (address : CellAddr) (target : address.field ∈ plan.targetFields)
    (pending : state.find? address = none) :
    plan.readPolicy state input address =
      .ok (NumericDependencyCell.ofObservation .empty).checked := by
  simp [CheckedParallelNumericPlan.readPolicy, target, pending]

theorem parallelNumericPlan_read_completed
    (plan : CheckedParallelNumericPlan model)
    (state : ParallelNumericRunState) (input : CheckedDocument model)
    (address : CellAddr) (completion : ParallelNumericDirectOutcome)
    (target : address.field ∈ plan.targetFields)
    (found : state.find? address = some completion) :
    plan.readPolicy state input address =
      .ok (NumericDependencyCell.ofOutcome completion.outcome).checked := by
  simp [CheckedParallelNumericPlan.readPolicy, target, found]

theorem parallelNumericPlan_read_input
    (plan : CheckedParallelNumericPlan model)
    (state : ParallelNumericRunState) (input : CheckedDocument model)
    (address : CellAddr) (ordinary : address.field ∉ plan.targetFields) :
    plan.readPolicy state input address = input.read address := by
  simp [CheckedParallelNumericPlan.readPolicy, ordinary]

/-- Successful execution of a prefix composes exactly with any remaining supplied suffix. -/
theorem parallelNumericPlan_executeTables_append
    (plan : CheckedParallelNumericPlan model)
    (preliminary : CheckedIndexPreliminary model)
    (left right :
      List (CheckedParallelNumericAlternativeTable model))
    (state mid : ParallelNumericRunState)
    (first :
      plan.executeTables preliminary left state = .ok mid) :
    plan.executeTables preliminary (left ++ right) state =
      plan.executeTables preliminary right mid := by
  induction left generalizing state mid with
  | nil =>
      simp [CheckedParallelNumericPlan.executeTables] at first
      subst mid
      rfl
  | cons table remaining ih =>
      cases executed :
          table.executeWithRead preliminary
            (plan.readPolicy state preliminary.base) with
      | error error =>
          simp [CheckedParallelNumericPlan.executeTables, executed] at first
      | ok outcomes =>
          simp only [CheckedParallelNumericPlan.executeTables, executed,
            List.cons_append] at first ⊢
          exact ih _ _ first

/-- Appending successful table outcomes preserves ownership by the supplied plan target fields. -/
theorem parallelNumericPlan_executeTables_owns_target_fields
    (plan : CheckedParallelNumericPlan model)
    (preliminary : CheckedIndexPreliminary model)
    (tables : List (CheckedParallelNumericAlternativeTable model))
    (state final : ParallelNumericRunState)
    (tablesOwned :
      ∀ table ∈ tables,
        table.targetField ∈ plan.targetFields)
    (stateOwned :
      ∀ outcome ∈ state.completed,
        outcome.address.field ∈ plan.targetFields)
    (executed :
      plan.executeTables preliminary tables state = .ok final) :
    ∀ outcome ∈ final.completed,
      outcome.address.field ∈ plan.targetFields := by
  induction tables generalizing state final with
  | nil =>
      change Except.ok state = Except.ok final at executed
      cases executed
      exact stateOwned
  | cons table remaining ih =>
      cases tableResult :
          table.executeWithRead preliminary
            (plan.readPolicy state preliminary.base) with
      | error error =>
          simp [CheckedParallelNumericPlan.executeTables,
            tableResult] at executed
      | ok outcomes =>
          apply ih
            { completed := state.completed ++ outcomes }
            final
          · intro candidate member
            exact tablesOwned candidate
              (List.mem_cons_of_mem table member)
          · intro outcome member
            rcases List.mem_append.mp member with member | member
            · exact stateOwned outcome member
            · have tableField :=
                parallelNumericAlternativeTable_executeWithRead_owns_target
                  table preliminary
                  (plan.readPolicy state preliminary.base)
                  outcomes tableResult outcome member
              rw [tableField]
              exact tablesOwned table (by simp)
          · simpa [CheckedParallelNumericPlan.executeTables,
              tableResult] using executed

private theorem parallelNumericPlan_executeTables_addresses_nodup
    (plan : CheckedParallelNumericPlan model)
    (preliminary : CheckedIndexPreliminary model)
    (tables : List (CheckedParallelNumericAlternativeTable model))
    (state final : ParallelNumericRunState)
    (tableTargetsNodup :
      (tables.map (·.targetField)).Nodup)
    (stateAddressesNodup :
      (state.completed.map (·.address)).Nodup)
    (stateDisjoint :
      ∀ outcome ∈ state.completed,
        outcome.address.field ∉ tables.map (·.targetField))
    (executed :
      plan.executeTables preliminary tables state = .ok final) :
    (final.completed.map (·.address)).Nodup := by
  induction tables generalizing state final with
  | nil =>
      change Except.ok state = Except.ok final at executed
      cases executed
      exact stateAddressesNodup
  | cons table remaining inductionHypothesis =>
      cases tableResult :
          table.executeWithRead preliminary
            (plan.readPolicy state preliminary.base) with
      | error error =>
          simp [CheckedParallelNumericPlan.executeTables,
            tableResult] at executed
      | ok outcomes =>
          have outcomesNodup :=
            parallelNumericAlternativeTable_executeWithRead_addresses_nodup
              table preliminary
              (plan.readPolicy state preliminary.base)
              outcomes tableResult
          have appendedNodup :
              ((state.completed ++ outcomes).map (·.address)).Nodup := by
            rw [List.map_append, List.nodup_append]
            exact ⟨stateAddressesNodup, outcomesNodup, by
              intro prior priorMember current currentMember equal
              rcases List.mem_map.mp priorMember with
                ⟨priorOutcome, priorOutcomeMember, rfl⟩
              rcases List.mem_map.mp currentMember with
                ⟨currentOutcome, currentOutcomeMember, rfl⟩
              have priorFieldNotCurrent :
                  priorOutcome.address.field ≠ table.targetField := by
                intro fieldEqual
                apply stateDisjoint priorOutcome priorOutcomeMember
                exact List.mem_cons.mpr (Or.inl fieldEqual)
              have currentOwned :=
                parallelNumericAlternativeTable_executeWithRead_owns_target
                  table preliminary
                  (plan.readPolicy state preliminary.base)
                  outcomes tableResult currentOutcome
                  currentOutcomeMember
              apply priorFieldNotCurrent
              rw [← currentOwned]
              exact congrArg CellAddr.field equal⟩
          apply inductionHypothesis
            { completed := state.completed ++ outcomes }
            final
          · exact (List.nodup_cons.mp tableTargetsNodup).2
          · exact appendedNodup
          · intro outcome member
            rcases List.mem_append.mp member with
              priorMember | currentMember
            · intro targetMember
              apply stateDisjoint outcome priorMember
              exact List.mem_cons_of_mem table.targetField targetMember
            · have currentOwned :=
                parallelNumericAlternativeTable_executeWithRead_owns_target
                  table preliminary
                  (plan.readPolicy state preliminary.base)
                  outcomes tableResult outcome currentMember
              rw [currentOwned]
              exact (List.nodup_cons.mp tableTargetsNodup).1
          · simpa [CheckedParallelNumericPlan.executeTables,
              tableResult] using executed

/-- A successful finite run emits outcomes only for fields owned by its checked tables. -/
theorem parallelNumericPlan_execute_owns_target_fields
    (plan : CheckedParallelNumericPlan model)
    (preliminary : CheckedIndexPreliminary model)
    (outcomes : List ParallelNumericDirectOutcome)
    (executed : plan.execute preliminary = .ok outcomes) :
    ∀ outcome ∈ outcomes,
      outcome.address.field ∈ plan.targetFields := by
  unfold CheckedParallelNumericPlan.execute at executed
  cases stateResult :
      plan.executeTables preliminary plan.tables {} with
  | error error =>
      rw [stateResult] at executed
      contradiction
  | ok final =>
      rw [stateResult] at executed
      cases executed
      apply parallelNumericPlan_executeTables_owns_target_fields
        plan preliminary plan.tables {} final
      · intro table member
        change table.targetField ∈
          plan.tables.map (·.targetField)
        exact List.mem_map_of_mem member
      · simp
      · exact stateResult

/-- A successful finite run emits each exact target address at most once. -/
theorem parallelNumericPlan_execute_addresses_nodup
    (plan : CheckedParallelNumericPlan model)
    (preliminary : CheckedIndexPreliminary model)
    (outcomes : List ParallelNumericDirectOutcome)
    (executed : plan.execute preliminary = .ok outcomes) :
    (outcomes.map (·.address)).Nodup := by
  unfold CheckedParallelNumericPlan.execute at executed
  cases stateResult :
      plan.executeTables preliminary plan.tables {} with
  | error error =>
      rw [stateResult] at executed
      contradiction
  | ok final =>
      rw [stateResult] at executed
      cases executed
      apply parallelNumericPlan_executeTables_addresses_nodup
        plan preliminary plan.tables {} final
      · exact checkedParallelNumericPlan_targetFields_nodup plan
      · simp
      · simp
      · exact stateResult

/-- Whole-run result construction delegates the successful addressed outcomes to the existing repeatable Number classifier. -/
theorem parallelNumericPlan_executeResult_classifies
    (plan : CheckedParallelNumericPlan model)
    (preliminary : CheckedIndexPreliminary model)
    (payloadAt : CellAddr → Payload)
    (supplied : List (ComputationFormalMessage Payload))
    (outcomes : List ParallelNumericDirectOutcome)
    (view :
      NumericComputationRunView (ComputationFormalMessage Payload) CellAddr)
    (executed : plan.execute preliminary = .ok outcomes)
    (classified :
      classifyParallelNumericOutcomes preliminary plan.operandRoutes
        payloadAt supplied outcomes = .ok view) :
    plan.executeResult preliminary payloadAt supplied = .ok view := by
  simp [CheckedParallelNumericPlan.executeResult, executed, classified]

end A12Kernel
