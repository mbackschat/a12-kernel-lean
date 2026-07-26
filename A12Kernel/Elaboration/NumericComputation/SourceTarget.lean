import A12Kernel.Elaboration.CheckedDocument
import A12Kernel.Semantics.NumericApplication

/-! # Checked Number source targets

This boundary projects one nonrepeatable Number target from the immutable checked document into the exact typed identity used by computation-result equality. The input annotation is required because stored text alone cannot distinguish a V2 `String` from a `BigDecimal`, or a negative-scale `BigDecimal` from its plain rendering.
-/

namespace A12Kernel

inductive NumericSourceTargetError where
  | field (cause : ResolveError)
  | nonNumericTarget (field : FieldId)
  | repeatableTarget (field : FieldId)
  | missingIdentity (field : FieldId)
  deriving Repr, DecidableEq

namespace CheckedDocument

/-- Project one scalar Number target without reparsing or duplicating the document. Missing typed provenance on a filled cell is structural, never semantic empty or poison. -/
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
  match checked.source.cells.find? fun cell =>
      cell.address == { field, path := [] } with
  | none => pure .absent
  | some cell =>
      if cell.stored.isEmpty then
        pure .presentEmpty
      else
        match cell.numericSourceIdentity with
        | some identity => pure (.presentValue identity)
        | none => throw (.missingIdentity field)

end CheckedDocument

end A12Kernel
