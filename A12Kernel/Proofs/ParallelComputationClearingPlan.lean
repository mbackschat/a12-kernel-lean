import A12Kernel.Elaboration.ParallelComputationClearing
import A12Kernel.Proofs.CheckedIndexColumn

/-! # Checked parallel-computation clearing-plan laws -/

namespace A12Kernel

theorem checkedParallelNumericTargetRoute_wellFormed
    (route : CheckedParallelNumericTargetRoute model) :
    route.WellFormed :=
  ⟨checkedParallelIndexGroups_wellFormed route.groups,
    route.targetResolved, route.sourceResolved, route.targetNumber,
    route.targetPolicyOwned, route.targetGroup, route.sourceGroup,
    route.targetScope, route.sourceScope⟩

theorem checkedParallelNumericClearingPlan_wellFormed
    (plan : CheckedParallelNumericClearingPlan model) :
    plan.WellFormed :=
  ⟨checkedParallelIndexGroups_wellFormed plan.groups,
    plan.targetResolved, plan.operandResolved, plan.targetNumber,
    plan.operandNumber, plan.targetPolicyOwned, plan.targetGroup,
    plan.operandGroup, plan.targetScope, plan.operandScope⟩

theorem parallelNumericTargetRouteEnvironments_cells_irrelevant
    (route : CheckedParallelNumericTargetRoute model)
    (left right : CheckedDocument model)
    (rows :
      left.source.instantiatedRows =
        right.source.instantiatedRows) :
    route.targetEnvironments left =
      route.targetEnvironments right := by
  simp [CheckedParallelNumericTargetRoute.targetEnvironments,
    CheckedDocument.actualRowEnvironments, rows]

/-- Target-instance enumeration depends on checked physical row topology, never on placed target-cell payloads. -/
theorem parallelNumericTargetEnvironments_cells_irrelevant
    (plan : CheckedParallelNumericClearingPlan model)
    (left right : CheckedDocument model)
    (rows :
      left.source.instantiatedRows =
        right.source.instantiatedRows) :
    plan.targetEnvironments left =
      plan.targetEnvironments right := by
  exact parallelNumericTargetRouteEnvironments_cells_irrelevant
    plan.asTargetRoute left right rows

theorem parallelNumericTargetRouteInvalidIndexMarks_noTargets
    (route : CheckedParallelNumericTargetRoute model)
    (preliminary : CheckedIndexPreliminary model)
    (side : ParallelComputationIndexSide)
    (empty :
      route.targetEnvironments preliminary.base = .ok []) :
    route.invalidIndexMarks preliminary side = .ok [] := by
  unfold CheckedParallelNumericTargetRoute.invalidIndexMarks
  rw [empty]
  rfl

/-- With no existing target instance, no index column is consulted and no post-loop mark exists. -/
theorem parallelNumericInvalidIndexMarks_noTargets
    (plan : CheckedParallelNumericClearingPlan model)
    (preliminary : CheckedIndexPreliminary model)
    (side : ParallelComputationIndexSide)
    (empty :
      plan.targetEnvironments preliminary.base = .ok []) :
    plan.invalidIndexMarks preliminary side = .ok [] := by
  apply parallelNumericTargetRouteInvalidIndexMarks_noTargets
  exact empty

theorem parallelNumericTargetRouteClearing_noMarks
    (route : CheckedParallelNumericTargetRoute model)
    (preliminary : CheckedIndexPreliminary model)
    (targetClean :
      route.invalidIndexMarks preliminary .target = .ok [])
    (operandClean :
      route.invalidIndexMarks preliminary .operand = .ok []) :
    route.clearedSourceTargets preliminary =
      .ok ParallelNumericClearingView.empty := by
  unfold CheckedParallelNumericTargetRoute.clearedSourceTargets
  rw [targetClean, operandClean]
  rfl

/-- Clean columns cannot produce a public clear, regardless of target row topology or source payloads. -/
theorem parallelNumericClearing_noMarks
    (plan : CheckedParallelNumericClearingPlan model)
    (preliminary : CheckedIndexPreliminary model)
    (targetClean :
      plan.invalidIndexMarks preliminary .target = .ok [])
    (operandClean :
      plan.invalidIndexMarks preliminary .operand = .ok []) :
    plan.clearedSourceTargets preliminary =
      .ok ParallelNumericClearingView.empty := by
  apply parallelNumericTargetRouteClearing_noMarks
  · exact targetClean
  · exact operandClean

@[simp] theorem parallelNumericClearingMark_targetScope
    (plan : CheckedParallelNumericClearingPlan model)
    (side : ParallelComputationIndexSide) :
    (plan.markPlanFor side).targetScope =
      plan.targetDeclaration.repeatableScope := by
  cases side <;> rfl

end A12Kernel
