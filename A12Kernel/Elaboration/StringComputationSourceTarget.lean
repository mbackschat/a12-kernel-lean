import A12Kernel.Elaboration.CheckedDocument
import A12Kernel.Semantics.StringApplication

/-! # String source-state projection from a checked document -/

namespace A12Kernel

namespace CheckedDocument

/-- Recover the exact source placement and identity for one addressed String-shaped target. Temporal declarations retain unconverted ingress identity (spec/09 §3.3); ordinary String, Custom and Enumeration retain token identity. Target-policy validity is irrelevant to source-relative change and clearing classification. -/
def sourceStringTargetStateAt (input : CheckedDocument model)
    (address : CellAddr) : StringTargetState :=
  match input.source.cells.find? fun cell =>
      cell.address == address with
  | none => .absent
  | some cell =>
      if empty : cell.stored = "" then
        .presentEmpty
      else
        let value : StoredString := { text := cell.stored, nonempty := empty }
        match model.lookupUniqueId address.field with
        | .ok declaration =>
            match declaration.policy.kind, cell.sourceRepresentation with
            | .temporal _ _, .unconvertedText => .presentUnconverted value
            | _, _ => .presentValue value
        | .error _ => .presentValue value

/-- Nonrepeatable compatibility projection through the exact addressed owner. -/
def sourceStringTargetState (input : CheckedDocument model)
    (field : FieldId) : StringTargetState :=
  input.sourceStringTargetStateAt { field, path := [] }

end CheckedDocument

end A12Kernel
