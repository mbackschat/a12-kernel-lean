import A12Kernel.Elaboration.ParallelNumericDirectRunResult
import A12Kernel.Proofs.NumericComputationRunResult

/-! # Isolated direct parallel Number-result laws -/

namespace A12Kernel

/-- Every successful merge certifies that no outcome-classified target is also claimed by its post-loop index-clearing producer. `executeResult` reaches its public view only through this gate. -/
theorem parallelNumericDirect_addIndexClears_noClassifiedIndexClear
    (classified view :
      NumericComputationRunView ResidualMessage CellAddr)
    (indexClears : List CellAddr)
    (success :
      addParallelNumericDirectIndexClears classified indexClears =
        .ok view) :
    parallelNumericDirectClassifiedIndexClear?
      classified indexClears = none := by
  unfold addParallelNumericDirectIndexClears at success
  cases overlap :
      parallelNumericDirectClassifiedIndexClear? classified indexClears with
  | some address =>
      simp [overlap] at success
  | none =>
      rfl

end A12Kernel
