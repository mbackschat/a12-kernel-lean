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

/-- Project exact Number placement state at an already-resolved address. This does not validate field kind or row topology; checked consumers use it only after their own model-owned address gate. -/
def numericTargetPlacementStateAt
    (checked : CheckedDocument model) (address : CellAddr) :
    NumericTargetState :=
  match checked.checkedCells.find? fun cell => cell.address == address with
  | none => .absent
  | some cell =>
      match cell.numericInput with
      | some input => .presentValue input.sourceIdentity
      | none => .presentEmpty

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
  pure (checked.numericTargetPlacementStateAt address)

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
  pure (checked.numericTargetPlacementStateAt { field, path := [] })

end CheckedDocument

end A12Kernel
