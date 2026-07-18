import A12Kernel.Evidence.StringComputationProjection
import A12Kernel.Evidence.StringComputationReplay
import A12Kernel.Evidence.StringTargetValidationReplay
import A12Kernel.Reference.StrictJson

/-! # One-time old/compact String-evidence agreement

This transitional checker proves that the compact 13+9 typed cases are exactly the semantic projection of the two legacy input projections. `EvidenceMain` separately runs both complete legacy binders, so agreement here joins their retained kernel observations to the new lane. Delete this module with the legacy stacks after recording the agreement revision.
-/

namespace A12Kernel.Evidence.StringComputationMigrationTest

open Lean
open A12Kernel
open A12Kernel.Evidence.StringComputationProjection

private def readJson (path : System.FilePath) : IO Json := do
  let input ← IO.FS.readFile path
  match A12Kernel.Reference.StrictJson.parseEvidence input with
  | .ok json => pure json
  | .error error => throw (IO.userError s!"{path}: invalid strict JSON: {repr error}")

private def ioOrThrow (context : String) : Except String α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{context}: {error}")

private def stored (value context : String) : Except String StoredString :=
  if nonempty : value ≠ "" then pure { text := value, nonempty }
  else throw s!"{context}: empty stored String"

private def delta (context : String) : List String → Except String (Option StringDelta)
  | [] => pure none
  | [signature] =>
      match signature.splitOn "|" with
      | ["/Shipment[1]/Target", "VALUE", value] => do
          pure <| some (.value (← stored value context))
      | ["/Shipment[1]/Target", "CLEARED"] => pure (some .cleared)
      | ["/Shipment[1]/Target", "ERRORED", attempted, "stringZuKurz"] => do
          pure <| some (.errored (← stored attempted context) .tooShort)
      | ["/Shipment[1]/Target", "ERRORED", attempted, "stringZuLang"] => do
          pure <| some (.errored (← stored attempted context) .tooLong)
      | _ => throw s!"{context}: unsupported signature '{signature}'"
  | signatures => throw s!"{context}: expected one target delta, found {repr signatures}"

private def computationOperation :
    A12Kernel.Evidence.StringComputation.ExprSpec → Except String Operation
  | .field 1 => pure .copy
  | .concat (.field 1) (.literal "-X") => pure .suffix
  | .concat (.field 1) (.field 2) => pure .appendFields
  | expression => throw s!"unsupported legacy String expression {repr expression}"

private def computationCell
    (case : A12Kernel.Evidence.StringComputation.CaseSpec)
    (field : FieldId) : Except String (Option String) :=
  match case.cells.filter (·.fieldId == field) with
  | [] => pure none
  | [cell] =>
      match cell.state with
      | .empty => pure none
      | .string value => pure (some value)
  | _ => throw s!"{case.id}: duplicate legacy cell {field}"

private def computationPrior
    (case : A12Kernel.Evidence.StringComputation.CaseSpec) :
    Except String StringTargetState :=
  match case.priorTarget with
  | .empty => pure .absent
  | .string value => do
      pure (.presentValue (← stored value case.id))

private def migrateComputation
    (bundle : A12Kernel.Evidence.StringComputation.Bundle) :
    Except String (List Case) :=
  bundle.cases.mapM fun case => do
    let model ← bundle.modelFor case
    pure {
      id := case.id
      mode := .deltaOnly
      input := {
        operation := ← computationOperation model.expression
        source := ← computationCell case 1
        other := ← computationCell case 2
        prior := ← computationPrior case
        rowHasContent := case.hasContent
        policy := .unconstrained }
      observed := {
        outcome := none
        delta := ← delta case.id (← case.replay model)
        applied := none } }

private def targetOperation :
    A12Kernel.Evidence.StringTargetValidation.OperationSpec → Except String Operation
  | .copy => pure .copy
  | .padded " " " " => pure .padded
  | operation => throw s!"unsupported legacy target operation {repr operation}"

private def targetPrior
    (case : A12Kernel.Evidence.StringTargetValidation.CaseSpec) :
    Except String StringTargetState :=
  match case.priorTarget with
  | .absent => pure .absent
  | .string value => do
      pure (.presentValue (← stored value case.id))

private def migrateTarget
    (bundle : A12Kernel.Evidence.StringTargetValidation.Bundle) :
    Except String (List Case) :=
  bundle.cases.mapM fun case => do
    let model ← bundle.modelFor case
    let replay ← case.replay model bundle.targetPointer
    pure {
      id := case.id
      mode := .targetChecked
      input := {
        operation := ← targetOperation model.operation
        source := some case.source
        other := none
        prior := ← targetPrior case
        rowHasContent := true
        policy := ← model.policy.toCore }
      observed := {
        outcome := some replay.outcome
        delta := ← delta case.id replay.delta
        applied := some replay.appliedState } }

def checkArtifacts (root : System.FilePath) : IO Nat := do
  let compact ← A12Kernel.Evidence.StringComputationProjection.loadCases root
  let oldComputation ← ioOrThrow "legacy String computation projection" <|
    A12Kernel.Evidence.StringComputation.Bundle.fromJson
      (← readJson (root / "string-computation-projection.json"))
  ioOrThrow "legacy String computation projection" oldComputation.validate
  let oldTarget ← ioOrThrow "legacy String target projection" <|
    A12Kernel.Evidence.StringTargetValidation.Bundle.fromJson
      (← readJson (root / "string-target-validation-projection.json"))
  ioOrThrow "legacy String target projection" oldTarget.validate
  let migrated ← ioOrThrow "legacy String semantic projection" <| do
    pure ((← migrateComputation oldComputation) ++ (← migrateTarget oldTarget))
  if migrated != compact then
    throw (IO.userError "legacy and compact String typed cases differ")
  pure migrated.length

end A12Kernel.Evidence.StringComputationMigrationTest
