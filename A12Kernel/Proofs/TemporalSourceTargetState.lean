import A12Kernel.Elaboration.TemporalComputationResult

/-! # Nonrepeatable temporal source target-state laws -/

namespace A12Kernel

theorem sourceNonemptyStoredTargetState_absent
    (input : CheckedDocument model) (field : FieldId)
    (makeStored : (text : String) → text ≠ "" → Stored)
    (absent : input.source.cells.find? (fun cell =>
      cell.address == ({ field, path := [] } : CellAddr)) = none) :
    input.sourceNonemptyStoredTargetState field makeStored = .absent := by
  simp [CheckedDocument.sourceNonemptyStoredTargetState, absent]

theorem sourceNonemptyStoredTargetState_empty
    (input : CheckedDocument model) (field : FieldId)
    (makeStored : (text : String) → text ≠ "" → Stored)
    (cell : ClassifiedCellInput)
    (found : input.source.cells.find? (fun candidate =>
      candidate.address == ({ field, path := [] } : CellAddr)) = some cell)
    (empty : cell.stored = "") :
    input.sourceNonemptyStoredTargetState field makeStored = .presentEmpty := by
  simp [CheckedDocument.sourceNonemptyStoredTargetState, found, empty]

theorem sourceNonemptyStoredTargetState_nonempty
    (input : CheckedDocument model) (field : FieldId)
    (makeStored : (text : String) → text ≠ "" → Stored)
    (cell : ClassifiedCellInput)
    (found : input.source.cells.find? (fun candidate =>
      candidate.address == ({ field, path := [] } : CellAddr)) = some cell)
    (nonempty : cell.stored ≠ "") :
    input.sourceNonemptyStoredTargetState field makeStored =
      .presentValue (makeStored cell.stored nonempty) := by
  simp [CheckedDocument.sourceNonemptyStoredTargetState, found, nonempty]

theorem sourceDateRangeTargetState_nonempty
    (input : CheckedDocument model) (field : FieldId)
    (cell : ClassifiedCellInput)
    (found : input.source.cells.find? (fun candidate =>
      candidate.address == ({ field, path := [] } : CellAddr)) = some cell)
    (nonempty : cell.stored ≠ "") :
    input.sourceDateRangeTargetState field =
      .presentValue ({ text := cell.stored, nonempty } : StoredDateRange) := by
  simpa [CheckedDocument.sourceDateRangeTargetState] using
    sourceNonemptyStoredTargetState_nonempty input field
      (fun text proof => ({ text, nonempty := proof } : StoredDateRange))
      cell found nonempty

end A12Kernel
