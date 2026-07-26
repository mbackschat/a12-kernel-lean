import A12Kernel.Elaboration.ParallelNumericRun
import A12Kernel.Conformance.ParallelNumericAlternativeTable

/-! # Parallel Number run-plan and overlay locks -/

namespace A12Kernel.Conformance.ParallelNumericRun

open A12Kernel
open A12Kernel.Conformance.ParallelNumericThreeGroupOperands

private def row? (target : FieldId) (operand : SurfaceFieldPath)
    (guard : ComputationCondition) :=
  (checkIsolatedParallelNumericExpressionRunWithGuard
    model ["Plan"] target operand (.atom (.field operand))
      (some guard)).toOption

private def table? (target : FieldId) (operand : SurfaceFieldPath)
    (guardField : FieldId) :
    Option (CheckedParallelNumericAlternativeTable model) := do
  let first ← row? target operand (.fieldFilled guardField)
  let second ← row? target operand (.fieldNotFilled guardField)
  (certifyParallelNumericAlternativeTable [first, second]).toOption

private def run? : Option (CheckedParallelNumericRun model) := do
  let producer ← table? 4 offsetPath 6
  let consumer ← table? 2 inputPath 4
  (certifyParallelNumericRun producer consumer).toOption

private def checkedDocument? (cells : List ClassifiedCellInput) :=
  (preliminaryFor cells).map (·.base)

private def read? (state : ParallelNumericRunState)
    (cells : List ClassifiedCellInput) (address : CellAddr) :
    Option CheckedCell := do
  let run ← run?
  let document ← checkedDocument? cells
  (run.readPolicy state document address).toOption

private def accepted (field : FieldId) (path : List Nat)
    (value : Int) : ParallelNumericDirectOutcome := {
  address := { field, path }
  outcome := .accepted { unscaled := value, scale := 0 }
}

/- The checked direction is producer first; duplicate or reversed roles fail structurally. -/
example :
    (do
      let producer ← table? 4 offsetPath 6
      match certifyParallelNumericRun producer producer with
      | .error error => some error
      | .ok _ => none) = some (.duplicateTarget 4) ∧
    (do
      let producer ← table? 4 offsetPath 6
      let consumer ← table? 2 inputPath 4
      match certifyParallelNumericRun consumer producer with
      | .error error => some error
      | .ok _ => none) =
        some (.producerReadsConsumer 2 4) ∧
    (do
      let producer ← table? 4 offsetPath 6
      let independent ← table? 2 offsetPath 6
      match certifyParallelNumericRun producer independent with
      | .error error => some error
      | .ok _ => none) =
        some (.consumerDoesNotReadProducer 2 4) := by
  native_decide

/- Pending computed addresses hide stale input, and completion is exact to one repetition address. -/
example :
    let stale := (cleanCells.filter fun cell => cell.address.field != 4) ++ [
      numberCell 4 [1] { unscaled := 99, scale := 0 },
      numberCell 4 [2] { unscaled := 98, scale := 0 }
    ]
    (read? {} stale { field := 4, path := [1] }).map
        (observeCell .computation) = some CellObservation.empty ∧
      (read? { completed := [accepted 4 [1] 30] }
        stale { field := 4, path := [1] }).map
          (observeCell .computation) =
        some (CellObservation.value (.num 30)) ∧
      (read? { completed := [accepted 4 [1] 30] }
        stale { field := 4, path := [2] }).map
          (observeCell .computation) =
        some CellObservation.empty := by
  native_decide

/- Invalid producer classes collapse to cause-blind dependency poison, while an ordinary input delegates unchanged. -/
example :
    let invalid : ParallelNumericDirectOutcome := {
      address := { field := 4, path := [1] }
      outcome := .invalidNoValue .calculationValue
    }
    (read? { completed := [invalid] }
      cleanCells { field := 4, path := [1] }).map
        (observeCell .computation) =
        some (CellObservation.poison .computedDependency) ∧
      (read? {} cleanCells { field := 6, path := [1] }).map
        (observeCell .computation) =
        some (CellObservation.value (.num 1)) := by
  native_decide

end A12Kernel.Conformance.ParallelNumericRun
