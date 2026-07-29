import A12Kernel.Elaboration.StringComputationRun

/-! # Checked String-computation run laws

These laws expose the three branches of the run's read policy. They state stripping and overlay behavior only; schedule relations and public result projections belong to later capsules.
-/

namespace A12Kernel

theorem stringComputationRun_read_pending
    (run : CheckedStringComputationRun model)
    (state : StringComputationRunState) (input : CheckedDocument model)
    (field : FieldId)
    (target : field ∈ run.targetFields)
    (pending : state.find? field = none) :
    (run.readPolicy state input).read field =
      StringDependencyCell.empty.checked := by
  simp [CheckedStringComputationRun.readPolicy, target, pending]

theorem stringComputationRun_read_completed
    (run : CheckedStringComputationRun model)
    (state : StringComputationRunState) (input : CheckedDocument model)
    (field : FieldId) (completion : StringComputationRunCompletion)
    (target : field ∈ run.targetFields)
    (found : state.find? field = some completion) :
    (run.readPolicy state input).read field =
      completion.dependencyCell.checked := by
  simp [CheckedStringComputationRun.readPolicy, target, found]

theorem stringComputationRun_read_input
    (run : CheckedStringComputationRun model)
    (state : StringComputationRunState) (input : CheckedDocument model)
    (field : FieldId)
    (ordinary : field ∉ run.targetFields) :
    (run.readPolicy state input).read field =
      input.stringComputationContext.read field := by
  simp [CheckedStringComputationRun.readPolicy, ordinary]

end A12Kernel
