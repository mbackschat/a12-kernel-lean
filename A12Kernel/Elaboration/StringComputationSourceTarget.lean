import A12Kernel.Elaboration.CheckedDocument
import A12Kernel.Semantics.StringApplication

/-! # String source-state projection from a checked document -/

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

end A12Kernel
