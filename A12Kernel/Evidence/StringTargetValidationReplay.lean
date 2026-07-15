import A12Kernel.Basic
import A12Kernel.Evidence.StringTargetValidationSchema
import A12Kernel.Semantics.StringComputation

/-! # A12Kernel.Evidence.StringTargetValidationReplay — pure nine-case target replay

This lane replays the closed String expression, positive length policy, payloadful delta, and value-only post-application view. Exact absent-versus-present-empty application state remains an external observation bound by the IO gate because the current core intentionally collapses those states.
-/

namespace A12Kernel.Evidence.StringTargetValidation

open A12Kernel

private def hasDuplicate [BEq α] : List α → Bool
  | [] => false
  | value :: rest => rest.contains value || hasDuplicate rest

private def lowercaseHexOfLength (length : Nat) (value : String) : Bool :=
  value.length == length && value.toList.all fun character =>
    character.isDigit || ('a' ≤ character && character ≤ 'f')

private def portableRelative (reference : String) : Bool :=
  !reference.isEmpty && !reference.startsWith "/" && !(reference.splitOn "/").contains ".."

private def conservativeEvidenceText (value : String) : Bool :=
  value.toList.all fun character =>
    let code := character.toNat
    0x20 ≤ code && code ≤ 0x7e && character != '|'

private def conservativeStringLiteral (value : String) : Bool :=
  conservativeEvidenceText value &&
    value.toList.all fun character => character != '"' && character != '\\'

def OperationSpec.render : OperationSpec → String
  | .copy => "[Source]"
  | .padded before after => s!"\"{before}\" + [Source] + \"{after}\""

def OperationSpec.toCore : OperationSpec → StringExpr
  | .copy => .field 1
  | .padded before after =>
      .concat (.concat (.literal before) (.field 1)) (.literal after)

def LengthPolicySpec.toCore : LengthPolicySpec → Except String StringTargetLengthPolicy
  | .minimum bound =>
      if positive : 0 < bound then pure (.minimum { value := bound, positive })
      else throw "a projected minimum String length must be positive"
  | .maximum bound =>
      if positive : 0 < bound then pure (.maximum { value := bound, positive })
      else throw "a projected maximum String length must be positive"

def PriorTargetSpec.toCore : PriorTargetSpec → Except String PriorStringTarget
  | .absent => pure .empty
  | .string value =>
      if nonempty : value ≠ "" then pure (.filled { text := value, nonempty })
      else throw "a prior stored String cannot be empty"

structure ReplayResult where
  outcome : StringTargetOutcome
  delta : List String
  appliedValue : Option String
  deriving Repr, DecidableEq

private def errorCode : StringTargetError → String
  | .tooShort => "stringZuKurz"
  | .tooLong => "stringZuLang"

private def deltaSignature (targetPointer : String) : Option StringDelta → List String
  | none => []
  | some (.value stored) => [s!"{targetPointer}|VALUE|{stored.text}"]
  | some .cleared => [s!"{targetPointer}|CLEARED"]
  | some (.errored attempted cause) =>
      [s!"{targetPointer}|ERRORED|{attempted.text}|{errorCode cause}"]

private def CaseSpec.context (case : CaseSpec) : StringComputationContext where
  read fieldId :=
    let raw : RawCell := if fieldId == 1 then .parsed (.str case.source) else .empty
    formalCheck { kind := .string } raw

def Bundle.modelFor (bundle : Bundle) (case : CaseSpec) : Except String ModelSpec :=
  match bundle.models.filter (·.id == case.modelId) with
  | [model] => pure model
  | [] => throw s!"{case.id}: unknown model '{case.modelId}'"
  | _ => throw s!"{case.id}: duplicate model '{case.modelId}'"

def CaseSpec.replay (case : CaseSpec) (model : ModelSpec)
    (targetPointer : String) : Except String ReplayResult := do
  let store ← match model.operation.toCore.evaluate case.context with
    | .ok result => pure result
    | .error (.fieldKindMismatch fieldId) =>
        throw s!"{case.id}: projected field {fieldId} failed its String kind invariant"
  let policy ← model.policy.toCore
  let prior ← case.priorTarget.toCore
  let outcome ← match policy.check store with
    | .supported result => pure result
    | .unsupported .unsupportedLineBreak =>
        throw s!"{case.id}: projected text requires the unsupported target line-break clause"
  pure {
    outcome
    delta := deltaSignature targetPointer (outcome.projectDelta prior)
    appliedValue := outcome.appliedValue.map (·.text) }

private def OperationSpec.validate (modelId : String) : OperationSpec → Except String Unit
  | .copy => pure ()
  | .padded before after => do
      if before.isEmpty || after.isEmpty ||
          !conservativeStringLiteral before || !conservativeStringLiteral after then
        throw s!"{modelId}: projected padding must be nonempty conservative ASCII"

private def ModelSpec.validate (model : ModelSpec) : Except String Unit := do
  if model.id.isEmpty || !portableRelative model.modelRef ||
      !lowercaseHexOfLength 64 model.modelSha256 then
    throw s!"{model.id}: invalid projected model identity"
  model.operation.validate model.id
  discard <| model.policy.toCore

private def CaseSpec.validate (bundle : Bundle) (case : CaseSpec) : Except String Unit := do
  if case.id.isEmpty || !portableRelative case.caseRef ||
      !lowercaseHexOfLength 64 case.caseSha256 then
    throw s!"{case.id}: invalid projected case identity"
  if case.source.isEmpty || !conservativeEvidenceText case.source then
    throw s!"{case.id}: the closed target-validation capture requires nonempty printable ASCII source text without the signature delimiter"
  match case.priorTarget with
  | .absent => pure ()
  | .string value =>
      if !conservativeEvidenceText value then
        throw s!"{case.id}: the prior target is outside the closed printable ASCII transport alphabet"
  discard <| case.priorTarget.toCore
  discard <| bundle.modelFor case

def Bundle.validate (bundle : Bundle) : Except String Unit := do
  if bundle.schemaVersion != 1 then
    throw s!"unsupported String target-validation evidence schema {bundle.schemaVersion}"
  if bundle.kernelVersion != A12Kernel.kernelVersion then
    throw s!"String target-validation evidence targets kernel {bundle.kernelVersion}"
  if !portableRelative bundle.captureRef ||
      !lowercaseHexOfLength 64 bundle.captureSha256 ||
      !lowercaseHexOfLength 40 bundle.sourceRevision ||
      bundle.targetPointer != "/Shipment[1]/Target" then
    throw "invalid String target-validation capture identity or target pointer"
  if bundle.models.length != 4 || bundle.cases.length != 9 then
    throw "String target-validation projection must retain exactly four models and nine cases"
  if hasDuplicate (bundle.models.map (·.id)) ||
      hasDuplicate (bundle.models.map (·.modelRef)) ||
      hasDuplicate (bundle.cases.map (·.id)) ||
      hasDuplicate (bundle.cases.map (·.caseRef)) then
    throw "duplicate String target-validation model or case identity"
  bundle.models.forM ModelSpec.validate
  bundle.cases.forM (·.validate bundle)
  for model in bundle.models do
    if !(bundle.cases.any (·.modelId == model.id)) then
      throw s!"{model.id}: projected target-validation model has no case"

example : (LengthPolicySpec.minimum 0).toCore.isOk = false := by
  native_decide

example : (PriorTargetSpec.string "").toCore.isOk = false := by
  native_decide

example : conservativeEvidenceText "A|B" = false := by native_decide
example : conservativeEvidenceText "A\nB" = false := by native_decide
example : conservativeEvidenceText "A😀B" = false := by native_decide

end A12Kernel.Evidence.StringTargetValidation
