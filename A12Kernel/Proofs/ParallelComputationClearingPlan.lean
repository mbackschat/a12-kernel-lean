import A12Kernel.Elaboration.ParallelComputationClearing
import A12Kernel.Proofs.CheckedDocument
import A12Kernel.Proofs.CheckedIndexColumn
import A12Kernel.Proofs.ComputationRunPlan

/-! # Checked parallel-computation clearing-plan laws -/

namespace A12Kernel

theorem checkedParallelNumericTargetRoute_wellFormed
    (route : CheckedParallelNumericTargetRoute model) :
    route.WellFormed :=
  ⟨checkedParallelIndexGroups_wellFormed route.groups,
    route.targetResolved, route.sourceResolved, route.targetNumber,
    route.targetPolicyOwned, route.targetGroup, route.sourceGroup,
    route.targetScope, route.targetScopeUnique, route.sourceScope⟩

theorem checkedParallelNumericClearingPlan_wellFormed
    (plan : CheckedParallelNumericClearingPlan model) :
    plan.WellFormed :=
  ⟨checkedParallelIndexGroups_wellFormed plan.groups,
    plan.targetResolved, plan.operandResolved, plan.targetNumber,
    plan.operandNumber, plan.targetPolicyOwned, plan.targetGroup,
    plan.operandGroup, plan.targetScope, plan.targetScopeUnique,
    plan.operandScope⟩

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

/-- A step that answers `none` at every element of a list makes the whole `mapM` a constant `none`
list. Stated here because the clearing law below is its only consumer. -/
private theorem exceptMapM_const_none {α β ε : Type} {f : α → Except ε (Option β)} :
    ∀ {l : List α}, (∀ a ∈ l, f a = .ok none) → l.mapM f = .ok (l.map fun _ => none)
  | [], _ => rfl
  | a :: rest, h => by
      rw [List.mapM_cons, h a (List.mem_cons_self ..),
        exceptMapM_const_none (fun b member => h b (List.mem_cons_of_mem a member))]
      rfl

/-- Every successful coverage entry retains the checked route's target field. -/
theorem parallelNumericTargetRoute_coverageWithMarks_owns_target
    (route : CheckedParallelNumericTargetRoute model)
    (preliminary : CheckedIndexPreliminary model)
    (targetMarks :
      List (ParallelComputationMark (route.markPlanFor .target)))
    (operandMarks :
      List (ParallelComputationMark (route.markPlanFor .operand)))
    (coverage : List ParallelNumericTargetCoverage)
    (covered :
      route.targetCoverageWithMarks preliminary targetMarks operandMarks =
        .ok coverage) :
    ∀ target ∈ coverage,
      target.address.field = route.targetField := by
  unfold CheckedParallelNumericTargetRoute.targetCoverageWithMarks at covered
  cases environments :
      route.targetEnvironments preliminary.base with
  | error error =>
      simp [environments, Except.mapError, Bind.bind,
        Except.bind] at covered
  | ok targetEnvironments =>
      have mapped :
          targetEnvironments.mapM (fun environment => do
            let path ←
              environment.pathForScope
                  route.targetDeclaration.repeatableScope
                |>.mapError
                  ParallelNumericTargetCoverageError.targetEnvironment
            let coveredByTarget ←
              (route.markPlanFor .target).coversAny
                  environment targetMarks
                |>.mapError
                  ParallelNumericTargetCoverageError.targetEnvironment
            let coveredByOperand ←
              (route.markPlanFor .operand).coversAny
                  environment operandMarks
                |>.mapError
                  ParallelNumericTargetCoverageError.targetEnvironment
            pure ({
              environment
              address := { field := route.targetField, path }
              indexInvalid := coveredByTarget || coveredByOperand
              overLimit :=
                preliminary.base.environmentOverLimit
                  route.targetDeclaration.repeatableScope environment
            } : ParallelNumericTargetCoverage)) = .ok coverage := by
        simpa [environments, Except.mapError, Bind.bind,
          Except.bind] using covered
      apply exceptMapM_all_of_step (mapped := mapped)
      intro environment _ target executed
      cases path :
          environment.pathForScope
            route.targetDeclaration.repeatableScope with
      | error error =>
          simp [path, Except.mapError, Bind.bind, Except.bind]
            at executed
      | ok addressPath =>
          cases targetCovered :
              (route.markPlanFor .target).coversAny
                environment targetMarks with
          | error error =>
              simp [path, targetCovered, Except.mapError,
                Bind.bind, Except.bind] at executed
          | ok coveredByTarget =>
              cases operandCovered :
                  (route.markPlanFor .operand).coversAny
                    environment operandMarks with
              | error error =>
                  simp [path, targetCovered, operandCovered,
                    Except.mapError, Bind.bind, Except.bind] at executed
              | ok coveredByOperand =>
                  simp [path, targetCovered, operandCovered,
                    Except.mapError, Bind.bind, Pure.pure,
                    Except.bind] at executed
                  cases executed
                  rfl

/-- Successful route coverage contains each exact target address at most once. -/
theorem parallelNumericTargetRoute_coverageWithMarks_addresses_nodup
    (route : CheckedParallelNumericTargetRoute model)
    (preliminary : CheckedIndexPreliminary model)
    (targetMarks :
      List (ParallelComputationMark (route.markPlanFor .target)))
    (operandMarks :
      List (ParallelComputationMark (route.markPlanFor .operand)))
    (coverage : List ParallelNumericTargetCoverage)
    (covered :
      route.targetCoverageWithMarks preliminary targetMarks operandMarks =
        .ok coverage) :
    (coverage.map (·.address)).Nodup := by
  unfold CheckedParallelNumericTargetRoute.targetCoverageWithMarks at covered
  cases environmentsResult :
      route.targetEnvironments preliminary.base with
  | error error =>
      simp [environmentsResult, Except.mapError, Bind.bind,
        Except.bind] at covered
  | ok environments =>
      rw [environmentsResult] at covered
      simp only [Except.mapError, Bind.bind, Except.bind] at covered
      let action :
          Env →
            Except ParallelNumericTargetCoverageError
              ParallelNumericTargetCoverage := fun environment => do
        let path ←
          environment.pathForScope
              route.targetDeclaration.repeatableScope
            |>.mapError
              ParallelNumericTargetCoverageError.targetEnvironment
        let coveredByTarget ←
          (route.markPlanFor .target).coversAny
              environment targetMarks
            |>.mapError
              ParallelNumericTargetCoverageError.targetEnvironment
        let coveredByOperand ←
          (route.markPlanFor .operand).coversAny
              environment operandMarks
            |>.mapError
              ParallelNumericTargetCoverageError.targetEnvironment
        pure {
          environment
          address := { field := route.targetField, path }
          indexInvalid := coveredByTarget || coveredByOperand
          overLimit :=
            preliminary.base.environmentOverLimit
              route.targetDeclaration.repeatableScope environment
        }
      have mapped : environments.mapM action = .ok coverage := by
        change
          environments.mapM (fun environment => do
            let path ←
              environment.pathForScope
                  route.targetDeclaration.repeatableScope
                |>.mapError
                  ParallelNumericTargetCoverageError.targetEnvironment
            let coveredByTarget ←
              (route.markPlanFor .target).coversAny
                  environment targetMarks
                |>.mapError
                  ParallelNumericTargetCoverageError.targetEnvironment
            let coveredByOperand ←
              (route.markPlanFor .operand).coversAny
                  environment operandMarks
                |>.mapError
                  ParallelNumericTargetCoverageError.targetEnvironment
            pure ({
              environment
              address := { field := route.targetField, path }
              indexInvalid := coveredByTarget || coveredByOperand
              overLimit :=
                preliminary.base.environmentOverLimit
                  route.targetDeclaration.repeatableScope environment
            } : ParallelNumericTargetCoverage)) =
              .ok coverage
        exact covered
      have actionProperties :
          ∀ environment ∈ environments, ∀ target,
            action environment = .ok target →
              target.environment = environment ∧
                environment.pathForScope
                    route.targetDeclaration.repeatableScope =
                  .ok target.address.path := by
        intro environment member target executed
        unfold action at executed
        cases pathResult :
            environment.pathForScope
              route.targetDeclaration.repeatableScope with
        | error error =>
            simp [pathResult, Except.mapError, Bind.bind,
              Except.bind] at executed
        | ok path =>
            cases targetResult :
                (route.markPlanFor .target).coversAny
                  environment targetMarks with
            | error error =>
                simp [pathResult, targetResult, Except.mapError,
                  Bind.bind, Except.bind] at executed
            | ok targetCovered =>
                cases operandResult :
                    (route.markPlanFor .operand).coversAny
                      environment operandMarks with
                | error error =>
                    simp [pathResult, targetResult, operandResult,
                      Except.mapError, Bind.bind, Except.bind] at executed
                | ok operandCovered =>
                    simp [pathResult, targetResult, operandResult,
                      Except.mapError, Bind.bind, Except.bind,
                      Pure.pure, Except.pure] at executed
                    cases executed
                    exact ⟨rfl, by simp_all⟩
      have environmentProjection :
          coverage.map (·.environment) = environments := by
        have projection := exceptMapM_map_eq_of_step
          action id (·.environment) environments coverage
          (by
            intro environment member target executed
            exact (actionProperties environment member
              target executed).1)
          mapped
        simpa using projection
      have pathsOwned :
          ∀ target ∈ coverage,
            target.environment.pathForScope
                route.targetDeclaration.repeatableScope =
              .ok target.address.path := by
        apply exceptMapM_all_of_step
          action
          (fun target =>
            target.environment.pathForScope
                route.targetDeclaration.repeatableScope =
              .ok target.address.path)
          environments coverage
        · intro environment member target executed
          have properties :=
            actionProperties environment member target executed
          rw [properties.1]
          exact properties.2
        · exact mapped
      have coverageEnvironmentsNodup :
          (coverage.map (·.environment)).Nodup := by
        rw [environmentProjection]
        exact checkedDocument_actualRowEnvironments_nodup
          preliminary.base
          route.targetDeclaration.repeatableScope
          environments environmentsResult
      rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
      rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
        at coverageEnvironmentsNodup
      refine List.Pairwise.imp_of_mem ?_ coverageEnvironmentsNodup
      intro left right leftMember rightMember environmentsDifferent
        addressesEqual
      apply environmentsDifferent
      have leftEnvironmentMember :
          left.environment ∈ environments := by
        rw [← environmentProjection]
        exact List.mem_map.mpr ⟨left, leftMember, rfl⟩
      have rightEnvironmentMember :
          right.environment ∈ environments := by
        rw [← environmentProjection]
        exact List.mem_map.mpr ⟨right, rightMember, rfl⟩
      have leftLevels :=
        checkedDocument_actualRowEnvironment_scope
          preliminary.base
          route.targetDeclaration.repeatableScope
          environments environmentsResult
          left.environment leftEnvironmentMember
      have rightLevels :=
        checkedDocument_actualRowEnvironment_scope
          preliminary.base
          route.targetDeclaration.repeatableScope
          environments environmentsResult
          right.environment rightEnvironmentMember
      have addressPathsEqual :
          left.address.path = right.address.path :=
        congrArg CellAddr.path addressesEqual
      have leftPath :=
        env_pathForScope_complete_nodup
          left.environment
          route.targetDeclaration.repeatableScope
          left.address.path leftLevels route.targetScopeUnique
          (pathsOwned left leftMember)
      have rightPath :=
        env_pathForScope_complete_nodup
          right.environment
          route.targetDeclaration.repeatableScope
          right.address.path rightLevels route.targetScopeUnique
          (pathsOwned right rightMember)
      have valuesEqual :
          left.environment.map Prod.snd =
            right.environment.map Prod.snd := by
        rw [← leftPath, ← rightPath]
        exact addressPathsEqual
      calc
        left.environment =
            List.zip (left.environment.map Prod.fst)
              (left.environment.map Prod.snd) := by
          simpa [List.unzip_eq_map] using
            (List.zip_unzip left.environment).symm
        _ = List.zip (right.environment.map Prod.fst)
              (right.environment.map Prod.snd) := by
          rw [leftLevels, rightLevels, valuesEqual]
        _ = right.environment := by
          simpa [List.unzip_eq_map] using
            List.zip_unzip right.environment

/-- Deriving the marks internally cannot change the route-owned target field of successful coverage. -/
theorem parallelNumericTargetRoute_coverage_owns_target
    (route : CheckedParallelNumericTargetRoute model)
    (preliminary : CheckedIndexPreliminary model)
    (coverage : List ParallelNumericTargetCoverage)
    (covered : route.targetCoverage preliminary = .ok coverage) :
    ∀ target ∈ coverage,
      target.address.field = route.targetField := by
  unfold CheckedParallelNumericTargetRoute.targetCoverage at covered
  cases targetMarksResult :
      route.invalidIndexMarks preliminary .target with
  | error error =>
      simp [targetMarksResult, Except.mapError, Bind.bind, Except.bind]
        at covered
  | ok actualTargetMarks =>
      cases operandMarksResult :
          route.invalidIndexMarks preliminary .operand with
      | error error =>
          simp [targetMarksResult, operandMarksResult, Except.mapError,
            Bind.bind, Except.bind] at covered
      | ok actualOperandMarks =>
          apply parallelNumericTargetRoute_coverageWithMarks_owns_target
            route preliminary actualTargetMarks actualOperandMarks coverage
          simpa [targetMarksResult, operandMarksResult, Except.mapError,
            Bind.bind, Except.bind] using covered

/-- Internally deriving the mark sets preserves exact target-address uniqueness. -/
theorem parallelNumericTargetRoute_coverage_addresses_nodup
    (route : CheckedParallelNumericTargetRoute model)
    (preliminary : CheckedIndexPreliminary model)
    (coverage : List ParallelNumericTargetCoverage)
    (covered : route.targetCoverage preliminary = .ok coverage) :
    (coverage.map (·.address)).Nodup := by
  unfold CheckedParallelNumericTargetRoute.targetCoverage at covered
  cases targetMarksResult :
      route.invalidIndexMarks preliminary .target with
  | error error =>
      simp [targetMarksResult, Except.mapError, Bind.bind, Except.bind]
        at covered
  | ok targetMarks =>
      cases operandMarksResult :
          route.invalidIndexMarks preliminary .operand with
      | error error =>
          simp [targetMarksResult, operandMarksResult, Except.mapError,
            Bind.bind, Except.bind] at covered
      | ok operandMarks =>
          apply
            parallelNumericTargetRoute_coverageWithMarks_addresses_nodup
              route preliminary targetMarks operandMarks coverage
          simpa [targetMarksResult, operandMarksResult, Except.mapError,
            Bind.bind, Except.bind] using covered

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

/-- Clean index columns clear nothing **on an in-capacity target inventory**. The capacity
condition is not decoration: an over-limit row is cleared in a document whose every index column is
clean, so the earlier unconditional reading of this law was false and is corrected here rather than
narrowed by a hypothesis that happens to hold ([`SPEC-2026-08-31-08`](../../docs/A12-DMKITS-SPEC-SYNC-LEDGER.md)). -/
theorem parallelNumericTargetRouteClearing_noMarks
    (route : CheckedParallelNumericTargetRoute model)
    (preliminary : CheckedIndexPreliminary model)
    (targetClean :
      route.invalidIndexMarks preliminary .target = .ok [])
    (operandClean :
      route.invalidIndexMarks preliminary .operand = .ok [])
    (environments : List Env)
    (rows : route.targetEnvironments preliminary.base = .ok environments)
    (coverage : List ParallelNumericTargetCoverage)
    (covered :
      route.targetCoverageWithMarks preliminary [] [] = .ok coverage)
    (inCapacity : ∀ environment ∈ environments,
      preliminary.base.environmentOverLimit
        route.targetDeclaration.repeatableScope environment = false) :
    route.clearedSourceTargets preliminary =
      .ok ParallelNumericClearingView.empty := by
  have mapped :
      environments.mapM (fun environment => do
        let path ←
          Except.mapError ParallelNumericTargetCoverageError.targetEnvironment
            (environment.pathForScope route.targetDeclaration.repeatableScope)
        let coveredByTarget ←
          Except.mapError ParallelNumericTargetCoverageError.targetEnvironment
            ((route.markPlanFor .target).coversAny environment [])
        let coveredByOperand ←
          Except.mapError ParallelNumericTargetCoverageError.targetEnvironment
            ((route.markPlanFor .operand).coversAny environment [])
        pure ({
          environment
          address := { field := route.targetField, path }
          indexInvalid := coveredByTarget || coveredByOperand
          overLimit :=
            preliminary.base.environmentOverLimit
              route.targetDeclaration.repeatableScope environment
        } : ParallelNumericTargetCoverage)) = .ok coverage := by
    unfold CheckedParallelNumericTargetRoute.targetCoverageWithMarks at covered
    rw [rows] at covered
    simpa [Except.mapError, Bind.bind, Except.bind] using covered
  have quiet :
      ∀ target ∈ coverage,
        target.indexInvalid = false ∧ target.overLimit = false := by
    apply exceptMapM_all_of_step (mapped := mapped)
    intro environment member target executed
    cases path :
        environment.pathForScope
          route.targetDeclaration.repeatableScope with
    | error error =>
        simp [path, Except.mapError, Bind.bind, Except.bind] at executed
    | ok addressPath =>
        simp [path, ParallelComputationMarkPlan.coversAny,
          Except.mapError, Bind.bind, Pure.pure, Except.bind] at executed
        cases executed
        exact ⟨rfl, inCapacity environment member⟩
  have candidates :
      coverage.mapM
          (CheckedParallelNumericTargetRoute.clearCandidate preliminary.base) =
        .ok (coverage.map fun _ => none) :=
    exceptMapM_const_none (fun target member => by
      have properties := quiet target member
      simp [CheckedParallelNumericTargetRoute.clearCandidate,
        properties.1, properties.2, Pure.pure, Except.pure])
  unfold CheckedParallelNumericTargetRoute.clearedSourceTargets
  rw [targetClean, operandClean]
  simp only [Except.mapError, Bind.bind, Except.bind]
  rw [covered]
  simp [candidates, ParallelNumericClearingView.empty, Pure.pure, Except.pure]

/-- The same law at the checked plan. Source payloads are still irrelevant; target row topology is **not**, because a row beyond the declared repeatability clears with no mark anywhere. -/
theorem parallelNumericClearing_noMarks
    (plan : CheckedParallelNumericClearingPlan model)
    (preliminary : CheckedIndexPreliminary model)
    (targetClean :
      plan.invalidIndexMarks preliminary .target = .ok [])
    (operandClean :
      plan.invalidIndexMarks preliminary .operand = .ok [])
    (environments : List Env)
    (rows : plan.targetEnvironments preliminary.base = .ok environments)
    (coverage : List ParallelNumericTargetCoverage)
    (covered :
      plan.asTargetRoute.targetCoverageWithMarks preliminary [] [] = .ok coverage)
    (inCapacity : ∀ environment ∈ environments,
      preliminary.base.environmentOverLimit
        plan.targetDeclaration.repeatableScope environment = false) :
    plan.clearedSourceTargets preliminary =
      .ok ParallelNumericClearingView.empty :=
  parallelNumericTargetRouteClearing_noMarks plan.asTargetRoute preliminary
    targetClean operandClean environments rows coverage covered inCapacity

@[simp] theorem parallelNumericClearingMark_targetScope
    (plan : CheckedParallelNumericClearingPlan model)
    (side : ParallelComputationIndexSide) :
    (plan.markPlanFor side).targetScope =
      plan.targetDeclaration.repeatableScope := by
  cases side <;> rfl

end A12Kernel
