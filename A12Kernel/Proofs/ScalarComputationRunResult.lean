import A12Kernel.Elaboration.ScalarComputationRunResult

/-! # Family-preserving mixed result laws

The partition laws show that no outcome is lost or routed to the wrong family. The result law then fixes delegation to the two established family owners.
-/

namespace A12Kernel

/-- Every tagged outcome contributes to exactly one family partition. -/
theorem scalarComputationOutcomePartitions_count
    (outcomes : List ScalarComputationOutcome) :
    let partitioned := ScalarComputationOutcomePartitions.ofOutcomes outcomes
    partitioned.string.length + partitioned.number.length + partitioned.document.length =
      outcomes.length := by
  induction outcomes with
  | nil =>
      simp [ScalarComputationOutcomePartitions.ofOutcomes]
  | cons outcome remaining inductionHypothesis =>
      dsimp at inductionHypothesis
      cases outcome <;>
        simp only [ScalarComputationOutcomePartitions.ofOutcomes,
          List.length_cons]
      all_goals omega

/-- String membership is preserved exactly by the String partition. -/
theorem scalarComputationOutcomePartitions_string_mem_iff
    (outcomes : List ScalarComputationOutcome)
    (target : FieldId) (outcome : StringTargetOutcome) :
    (target, outcome) ∈
        (ScalarComputationOutcomePartitions.ofOutcomes outcomes).string ↔
      ScalarComputationOutcome.string target outcome ∈ outcomes := by
  induction outcomes with
  | nil =>
      simp [ScalarComputationOutcomePartitions.ofOutcomes]
  | cons head remaining inductionHypothesis =>
      cases head <;>
        simp [ScalarComputationOutcomePartitions.ofOutcomes,
          inductionHypothesis]

/-- Number membership is preserved exactly by the Number partition. -/
theorem scalarComputationOutcomePartitions_number_mem_iff
    (outcomes : List ScalarComputationOutcome)
    (target : FieldId) (outcome : NumericTargetOutcome) :
    (target, outcome) ∈
        (ScalarComputationOutcomePartitions.ofOutcomes outcomes).number ↔
      ScalarComputationOutcome.number target outcome ∈ outcomes := by
  induction outcomes with
  | nil =>
      simp [ScalarComputationOutcomePartitions.ofOutcomes]
  | cons head remaining inductionHypothesis =>
      cases head <;>
        simp [ScalarComputationOutcomePartitions.ofOutcomes,
          inductionHypothesis]

/-- Whole-document membership is preserved exactly by the whole-document partition. -/
theorem scalarComputationOutcomePartitions_document_mem_iff
    (outcomes : List ScalarComputationOutcome)
    (target : FieldId) (outcome : DocumentTargetOutcome) :
    (target, outcome) ∈
        (ScalarComputationOutcomePartitions.ofOutcomes outcomes).document ↔
      ScalarComputationOutcome.document target outcome ∈ outcomes := by
  induction outcomes with
  | nil =>
      simp [ScalarComputationOutcomePartitions.ofOutcomes]
  | cons head remaining inductionHypothesis =>
      cases head <;>
        simp [ScalarComputationOutcomePartitions.ofOutcomes,
          inductionHypothesis]

private theorem scalarComputationRun_executeSteps_noDocument
    (run : CheckedScalarComputationRun model)
    (world : World)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (steps : List (CheckedScalarComputationStep model))
    (state final : ScalarComputationRunState)
    (noDocumentStep : ∀ step ∈ steps, ∀ document, step ≠ .document document)
    (noDocumentYet : ∀ completion ∈ state.completed, ∀ target outcome cell,
      completion ≠ .document target outcome cell)
    (executed : run.executeSteps world patterns input steps state = .ok final) :
    ∀ completion ∈ final.completed, ∀ target outcome cell,
      completion ≠ .document target outcome cell := by
  induction steps generalizing state with
  | nil =>
      simp only [CheckedScalarComputationRun.executeSteps] at executed
      cases executed
      exact noDocumentYet
  | cons step remaining inductionHypothesis =>
      cases evaluation : run.evaluateStep world patterns input state step with
      | error cause =>
          rw [CheckedScalarComputationRun.executeSteps, evaluation] at executed
          cases executed
      | ok completion =>
          rw [CheckedScalarComputationRun.executeSteps, evaluation] at executed
          refine inductionHypothesis { completed := state.completed ++ [completion] }
            (fun step member => noDocumentStep step (List.mem_cons_of_mem _ member)) ?_ executed
          intro candidate member target outcome cell
          rcases List.mem_append.mp member with earlier | added
          · exact noDocumentYet candidate earlier target outcome cell
          · simp only [List.mem_singleton] at added
            subst added
            cases step with
            | string table =>
                cases result : table.evaluateCompletion patterns (run.stringContext state input) (run.numberContext world state input)
                    (some ((run.documentFor state input).resolveSemanticIndexColumnWith (run.documentFor state input).read)) <;>
                  simp [CheckedScalarComputationRun.evaluateStep, result] at evaluation
                subst evaluation
                simp
            | number table =>
                cases result : table.evaluateCompletion (run.numberContext world state input) <;>
                  simp [CheckedScalarComputationRun.evaluateStep, result] at evaluation
                subst evaluation
                simp
            | document document =>
                exact absurd rfl (noDocumentStep (.document document) (by simp) document)

/-- A run with no whole-document step computes no whole-document outcome, which discharges the routing
law's `noDocument` hypothesis for every String-and-Number run. -/
theorem scalarComputationRun_execute_noDocument
    (run : CheckedScalarComputationRun model)
    (world : World)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (outcomes : List ScalarComputationOutcome)
    (noDocumentStep : ∀ step ∈ run.steps, ∀ document, step ≠ .document document)
    (executed : run.execute world patterns input = .ok outcomes) :
    (ScalarComputationOutcomePartitions.ofOutcomes outcomes).document = [] := by
  cases result : run.executeSteps world patterns input run.steps {} with
  | error cause =>
      rw [CheckedScalarComputationRun.execute, result] at executed
      cases executed
  | ok final =>
      rw [CheckedScalarComputationRun.execute, result] at executed
      cases executed
      have noDocument := scalarComputationRun_executeSteps_noDocument run world patterns input
        run.steps {} final noDocumentStep (by simp) result
      rw [List.eq_nil_iff_forall_not_mem]
      intro ⟨target, outcome⟩ member
      rw [scalarComputationOutcomePartitions_document_mem_iff] at member
      simp only [ScalarComputationRunState.outcomes, List.mem_map] at member
      obtain ⟨completion, completed, projected⟩ := member
      cases completion with
      | string completion => simp [ScalarComputationCompletion.outcome] at projected
      | number completion => simp [ScalarComputationCompletion.outcome] at projected
      | document target' outcome' cell =>
          exact noDocument _ completed target' outcome' cell rfl

/-- Successful mixed result projection delegates the exact constructor partitions to the two existing family owners. -/
theorem scalarComputationRun_executeResult_routesFamilies
    (run : CheckedScalarComputationRun model)
    (world : World)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (numberPayloadAt : FieldId → NumberPayload)
    (numberMessages : List (ComputationFormalMessage NumberPayload))
    (stringResidualMessages : List StringResidual)
    (outcomes : List ScalarComputationOutcome)
    (number :
      NumericComputationRunView
        (ComputationFormalMessage NumberPayload))
    (executed : run.execute world patterns input = .ok outcomes)
    (noDocument : (ScalarComputationOutcomePartitions.ofOutcomes outcomes).document = [])
    (numberProjected :
      NumericComputationRunView.fromOutcomes input numberPayloadAt
        numberMessages
        (ScalarComputationOutcomePartitions.ofOutcomes outcomes).number =
          .ok number) :
    run.executeResult world patterns input numberPayloadAt
        numberMessages stringResidualMessages =
      .ok {
        string := StringComputationRunView.fromOutcomes input
          stringResidualMessages
          (ScalarComputationOutcomePartitions.ofOutcomes outcomes).string
        number
      } := by
  unfold CheckedScalarComputationRun.executeResult
  rw [executed]
  simp [noDocument, numberProjected, Except.mapError, bind, Except.bind, pure, Except.pure]

end A12Kernel
