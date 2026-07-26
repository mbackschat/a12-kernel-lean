import A12Kernel.Elaboration.ParallelNumericRun

/-! # Checked parallel Number run-overlay laws -/

namespace A12Kernel

theorem parallelNumericRun_read_pending
    (run : CheckedParallelNumericRun model)
    (state : ParallelNumericRunState) (input : CheckedDocument model)
    (address : CellAddr) (target : address.field ∈ run.targetFields)
    (pending : state.find? address = none) :
    run.readPolicy state input address =
      .ok (NumericDependencyCell.ofObservation .empty).checked := by
  simp [CheckedParallelNumericRun.readPolicy, target, pending]

theorem parallelNumericRun_read_completed
    (run : CheckedParallelNumericRun model)
    (state : ParallelNumericRunState) (input : CheckedDocument model)
    (address : CellAddr) (completion : ParallelNumericDirectOutcome)
    (target : address.field ∈ run.targetFields)
    (found : state.find? address = some completion) :
    run.readPolicy state input address =
      .ok (NumericDependencyCell.ofOutcome completion.outcome).checked := by
  simp [CheckedParallelNumericRun.readPolicy, target, found]

theorem parallelNumericRun_read_input
    (run : CheckedParallelNumericRun model)
    (state : ParallelNumericRunState) (input : CheckedDocument model)
    (address : CellAddr) (ordinary : address.field ∉ run.targetFields) :
    run.readPolicy state input address = input.read address := by
  simp [CheckedParallelNumericRun.readPolicy, ordinary]

end A12Kernel
