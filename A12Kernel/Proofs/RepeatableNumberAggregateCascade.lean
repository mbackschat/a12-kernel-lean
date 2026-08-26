import A12Kernel.Elaboration.RepeatableNumberAggregateCascade
import A12Kernel.Proofs.NumericComputationRunRelation

/-! # Repeatable Number to aggregate cascade laws -/

namespace A12Kernel

/-- Analyze preserves the row computation and later aggregate dependency in supplied order. -/
@[simp]
theorem checkedRepeatableNumberAggregateCascade_analyze
    (plan : CheckedRepeatableNumberAggregateCascade model) :
    plan.analyze = {
      producer := plan.row.kind
      consumer := plan.consumer.kind
      operation := plan.operation
      repeatableScope :=
        plan.row.targetDeclaration.repeatableScope
      fieldDependencies := [
        (plan.row.targetField, plan.row.sourceFields),
        (plan.total.operation.core.target.id,
          plan.consumer.fieldDependencies)]
    } := by
  rfl

/-- Analyze extends the checked row-to-aggregate prefix with exactly one deduplicated scalar field edge. -/
@[simp]
theorem checkedRepeatableNumberAggregateScalarCascade_analyze
    (plan : CheckedRepeatableNumberAggregateScalarCascade model) :
    plan.analyze = {
      cascade := plan.cascade.analyze
      scalarOperation := plan.scalarOperation
      fieldDependencies := plan.cascade.analyze.fieldDependencies ++ [
        (plan.scalar.operation.core.target.id,
          [plan.leftDeclaration.id, plan.rightDeclaration.id].eraseDups)]
    } := by
  rfl

/-- Analyze retains the supplied scalar target order and every computed-target edge against the aggregate-prefixed candidate order. -/
@[simp]
theorem checkedRepeatableNumberAggregateRunCascade_analyze
    (plan : CheckedRepeatableNumberAggregateRunCascade model) :
    plan.analyze =
      let candidates :=
        plan.cascade.total.operation.core.target.id :: plan.run.targetFields
      {
        cascade := plan.cascade.analyze
        scalarTargets := plan.run.targetFields
        computedDependencies := plan.run.tables.map fun table =>
          (table.targetField,
            candidates.filter fun field => table.referencesField field)
      } := by
  rfl

private theorem repeatableNumberAggregateRunCascade_aggregateTarget_not_runTarget
    (plan : CheckedRepeatableNumberAggregateRunCascade model) :
    plan.cascade.total.operation.core.target.id ∉ plan.run.targetFields := by
  intro member
  have distinct := List.all_eq_true.mp plan.distinctTargets
    plan.cascade.total.operation.core.target.id member
  simp at distinct

/-- Every successful aggregate-seeded finite Number execution has an exact
suffix trace whose labels exclude the retained aggregate seed. -/
theorem repeatableNumberAggregateRunCascade_execute_trace
    (plan : CheckedRepeatableNumberAggregateRunCascade model)
    (world : World)
    (input : CheckedDocument model)
    (outcomes : RepeatableNumberAggregateRunCascadeOutcomes)
    (executed : plan.execute world input = .ok outcomes) :
    ∃ final,
      NumericComputationRunTrace plan.run world input
        { completed := [{
            targetField := plan.cascade.total.operation.core.target.id
            outcome := outcomes.cascade.aggregate.outcome
          }] }
        outcomes.scalars final := by
  unfold CheckedRepeatableNumberAggregateRunCascade.execute at executed
  cases cascadeResult : plan.cascade.execute world input with
  | error cause =>
      simp [cascadeResult, Except.mapError, Bind.bind, Except.bind] at executed
  | ok cascade =>
      cases suffixResult : plan.run.executeTables world input plan.run.tables {
          completed := [{
            targetField := plan.cascade.total.operation.core.target.id
            outcome := cascade.aggregate.outcome
          }]
        } with
      | error cause =>
          simp [cascadeResult, suffixResult, Except.mapError,
            Bind.bind, Except.bind] at executed
      | ok final =>
          simp [cascadeResult, suffixResult, Except.mapError,
            Bind.bind, Except.bind] at executed
          cases executed
          have seedDisjoint :
              ∀ target ∈ [plan.cascade.total.operation.core.target.id],
                target ∉ plan.run.targetFields := by
            intro target member
            simp only [List.mem_singleton] at member
            subst target
            exact
              repeatableNumberAggregateRunCascade_aggregateTarget_not_runTarget
                plan
          obtain ⟨labels, trace, appended⟩ :=
            numericComputationRun_executeTables_seeded_trace
              plan.run world input
              [plan.cascade.total.operation.core.target.id]
              [] plan.run.tables {
                completed := [{
                  targetField := plan.cascade.total.operation.core.target.id
                  outcome := cascade.aggregate.outcome
                }]
              } final seedDisjoint (by simp)
              (by simp [NumericComputationRunState.targetFields]) suffixResult
          have labelsFinal : labels = final.outcomes.drop 1 := by
            have dropped := congrArg (List.drop 1) appended
            simpa [NumericComputationRunState.outcomes] using dropped
          exact ⟨final, by simpa [labelsFinal] using trace⟩

end A12Kernel
