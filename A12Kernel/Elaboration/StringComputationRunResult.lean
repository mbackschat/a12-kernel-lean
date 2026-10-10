import A12Kernel.Elaboration.StringComputationRun
import A12Kernel.Semantics.StringComputationRunResult

/-! # Checked-document and execution adapters for String result classification -/

namespace A12Kernel

namespace CheckedDocument

/-- Recover the exact source placement and stored text for one addressed String target. Target-policy validity is irrelevant to source-relative change and clearing classification. -/
def sourceStringTargetStateAt (input : CheckedDocument model)
    (address : CellAddr) : StringTargetState :=
  match input.source.cells.find? fun cell =>
      cell.address == address with
  | none => .absent
  | some cell =>
      if empty : cell.stored = "" then
        .presentEmpty
      else
        .presentValue { text := cell.stored, nonempty := empty }

/-- Nonrepeatable compatibility projection through the exact addressed owner. -/
def sourceStringTargetState (input : CheckedDocument model)
    (field : FieldId) : StringTargetState :=
  input.sourceStringTargetStateAt { field, path := [] }

end CheckedDocument

namespace StringComputationRunView

/-- Build the extensional String result from rich run outcomes. The separately supplied residual messages are retained unchanged; this function does not claim how pointer partitioning or eager formal checking constructs them. -/
def fromOutcomes (input : CheckedDocument model)
    (residualMessages : List ResidualMessage)
    (outcomes : List (FieldId × StringTargetOutcome)) :
    StringComputationRunView ResidualMessage :=
  fromSourcedOutcomes residualMessages (outcomes.map fun entry => {
    targetField := entry.1
    outcome := entry.2
    source := input.sourceStringTargetState entry.1
  })

end StringComputationRunView

namespace CheckedStringComputationRun

/-- Execute the checked run and classify its rich outcomes relative to that same immutable source document. -/
def executeResult (run : CheckedStringComputationRun model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (residualMessages : List ResidualMessage) :
    Except StringComputationRunFault (StringComputationRunView ResidualMessage) := do
  let outcomes ← run.execute patterns input
  pure (StringComputationRunView.fromOutcomes input residualMessages outcomes)

end CheckedStringComputationRun

end A12Kernel
