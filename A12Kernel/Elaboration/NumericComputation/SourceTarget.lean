import A12Kernel.Elaboration.CheckedDocument
import A12Kernel.Semantics.NumericApplication

/-! # Checked Number source targets

This boundary projects one exact Number target from the immutable checked document into the typed source state used by result classification. The addressed entry point accepts model-legal scalar or repeatable addresses; the original scalar entry point still rejects repeatable declarations. The checked placement retains whether the exact source was String-valued or decimal-valued because their equality against computed output differs even when their displayed text agrees.
-/

namespace A12Kernel

inductive NumericSourceTargetError where
  | field (cause : ResolveError)
  | document (cause : CheckedDocumentError)
  | nonNumericTarget (field : FieldId)
  | repeatableTarget (field : FieldId)
  deriving Repr, DecidableEq

namespace CheckedDocument

private def numericTargetStateFromSource
    (checked : CheckedDocument model) (address : CellAddr) :
    Except NumericSourceTargetError NumericTargetState :=
  match checked.checkedCells.find? fun cell => cell.address == address with
  | none => pure .absent
  | some cell =>
      match cell.numericInput with
      | some input => pure (.presentValue input.sourceIdentity)
      | none => pure .presentEmpty

/-- Project one exact model-legal Number target address without reparsing or duplicating the document. Missing row topology and typed provenance remain structural. -/
def numericTargetStateAt (checked : CheckedDocument model)
    (address : CellAddr) :
    Except NumericSourceTargetError NumericTargetState := do
  let declaration ←
    (model.lookupUniqueId address.field).mapError .field
  match declaration.policy.kind with
  | .number _ => pure ()
  | _ => throw (.nonNumericTarget address.field)
  let _ ← checked.read address |>.mapError .document
  checked.numericTargetStateFromSource address

/-- Project one scalar Number target without reparsing or duplicating the document. -/
def numericTargetState (checked : CheckedDocument model)
    (field : FieldId) :
    Except NumericSourceTargetError NumericTargetState := do
  let declaration ←
    (model.lookupUniqueId field).mapError .field
  match declaration.policy.kind with
  | .number _ => pure ()
  | _ => throw (.nonNumericTarget field)
  if !declaration.repeatableScope.isEmpty then
    throw (.repeatableTarget field)
  checked.numericTargetStateFromSource { field, path := [] }

end CheckedDocument

end A12Kernel
