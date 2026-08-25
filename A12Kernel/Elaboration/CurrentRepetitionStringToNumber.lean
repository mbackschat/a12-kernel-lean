import A12Kernel.Elaboration.CurrentRepetitionComputation
import A12Kernel.Elaboration.AddressedFieldValueAsString
import A12Kernel.Elaboration.AddressedFieldValueAsNumber
import A12Kernel.Semantics.StringCascade

/-! # CurrentRepetition String-to-Number cascade -/

namespace A12Kernel

/-- Fail-closed admission errors for one maintained inverse cross-family repeatable cascade. -/
inductive CurrentRepetitionStringToNumberElabError where
  | source (cause : CurrentRepetitionSourceElabError)
  | string (cause : AddressedFieldValueAsStringElabError)
  | number (cause : AddressedFieldValueAsNumberElabError)
  | groupMismatch (source declaring : GroupPath)
  | stringScope (actual : List RepeatableLevel)
  | numberScope (actual : List RepeatableLevel)
  | dependency (expected actual : FieldId)
  | reverseDependency (field : FieldId)
  deriving Repr, DecidableEq

/-- One checked `CurrentRepetition(group) > 0` guarded `FieldValueAsString` producer followed by same-row `FieldValueAsNumber` over that String target. The shape is finite and carries no generic condition tree or scheduler. -/
structure CheckedCurrentRepetitionStringToNumberCascade (model : FlatModel) where
  private mk ::
  source : CheckedCurrentRepetitionSource model
  string : CheckedAddressedFieldValueAsString model
  number : CheckedAddressedFieldValueAsNumber model
  groupMatches : source.path = string.declaringGroup
  stringScope :
    string.targetDeclaration.repeatableScope = source.completeScope
  numberScope :
    number.placement.targetDeclaration.repeatableScope = source.completeScope
  dependency :
    number.placement.sourceDeclaration.id = string.targetField
  noReverseDependency :
    string.sourceDeclaration.id ≠ number.placement.targetField

/-- Check only the exact complete-scope inverse cascade and its authored dependency edge. -/
def checkCurrentRepetitionStringToNumberCascade
    (model : FlatModel) (declaringGroup : GroupPath)
    (group : SurfaceGroupPath)
    (stringTarget : FieldId) (stringSource : SurfaceFieldPath)
    (numberTarget : FieldId) (numberSource : SurfaceTextFieldOperand) :
    Except CurrentRepetitionStringToNumberElabError
      (CheckedCurrentRepetitionStringToNumberCascade model) := do
  let source ← checkCurrentRepetitionSource model declaringGroup group
    |>.mapError .source
  let string ←
    checkAddressedFieldValueAsString model declaringGroup stringTarget stringSource
      |>.mapError .string
  let number ←
    checkAddressedFieldValueAsNumber model declaringGroup numberTarget numberSource
      |>.mapError .number
  if hGroup : source.path = string.declaringGroup then
    if hStringScope : string.targetDeclaration.repeatableScope =
        source.completeScope then
      if hNumberScope : number.placement.targetDeclaration.repeatableScope =
          source.completeScope then
        if hDependency : number.placement.sourceDeclaration.id =
            string.targetField then
          if hReverse : string.sourceDeclaration.id =
              number.placement.targetField then
            throw (.reverseDependency number.placement.targetField)
          else
            pure {
              source
              string
              number
              groupMatches := hGroup
              stringScope := hStringScope
              numberScope := hNumberScope
              dependency := hDependency
              noReverseDependency := hReverse
            }
        else
          throw (.dependency string.targetField
            number.placement.sourceDeclaration.id)
      else throw (.numberScope number.placement.targetDeclaration.repeatableScope)
    else throw (.stringScope string.targetDeclaration.repeatableScope)
  else throw (.groupMismatch source.path string.declaringGroup)

/-- Exact typed outcomes for one selected row. -/
structure CurrentRepetitionStringToNumberRowOutcomes where
  coordinate : Nat
  string : SourcedStringTargetOutcome CellAddr
  number : SourcedNumericTargetOutcome CellAddr
  deriving Repr, DecidableEq

/-- Exact typed outcomes in physical row encounter order. -/
structure CurrentRepetitionStringToNumberOutcomes where
  rows : List CurrentRepetitionStringToNumberRowOutcomes
  deriving Repr, DecidableEq

/-- Structural, dependency-projection, or typed leaf failures of the bounded executor. -/
inductive CurrentRepetitionStringToNumberFault where
  | rows (cause : ActualRowEnvironmentError)
  | rowCardinality (actual : Nat)
  | coordinate (cause : EnvBindingError)
  | guardNotTrue (coordinate : Nat)
  | string (cause : AddressedFieldValueAsStringFault)
  | dependency (cause : StringDependencyFault)
  | number (cause : AddressedFieldValueAsNumberFault)
  | outcomeCardinality (target : FieldId) (actual : Nat)
  deriving Repr, DecidableEq

namespace CheckedCurrentRepetitionStringToNumberCascade

/-- Keep the structural coordinate separate from both real field edges. -/
def analyze (plan : CheckedCurrentRepetitionStringToNumberCascade model) :
    CurrentRepetitionCascadeAnalysis := {
  structuralGroup := plan.source.path
  scope := plan.source.completeScope
  fieldDependencies := [
    (plan.string.targetField, [plan.string.sourceDeclaration.id]),
    (plan.number.placement.targetField,
      [plan.number.placement.sourceDeclaration.id])]
}

/-- Evaluate the sole admitted guard through the shared checked coordinate owner. -/
def evaluatePositiveGuardAt
    (plan : CheckedCurrentRepetitionStringToNumberCascade model)
    (environment : Env) : Except EnvBindingError (Nat × Bool) :=
  plan.source.evaluatePositiveGuardAt environment

private def dependencyCells
    (strings : List (SourcedStringTargetOutcome CellAddr)) :
    Except StringDependencyFault (List (CellAddr × CheckedCell)) :=
  strings.mapM fun outcome => do
    let dependency ← StringDependencyCell.ofOutcome outcome.outcome
    pure (outcome.targetField, dependency.checked)

private def readAfterString (input : CheckedDocument model)
    (dependencies : List (CellAddr × CheckedCell))
    (address : CellAddr) : Except CheckedDocumentError CheckedCell :=
  match dependencies.find? fun dependency => dependency.1 == address with
  | some dependency => .ok dependency.2
  | none => input.read address

/-- Execute the fixed positive guard at every instantiated row, then expose each completed String outcome only to the Number conversion at that exact address. -/
def execute (plan : CheckedCurrentRepetitionStringToNumberCascade model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model) :
    Except CurrentRepetitionStringToNumberFault
      CurrentRepetitionStringToNumberOutcomes := do
  let environments ← plan.string.targetEnvironments input |>.mapError .rows
  if environments.isEmpty then throw (.rowCardinality 0)
  let coordinates ← environments.mapM fun environment => do
    let guard ← plan.evaluatePositiveGuardAt environment
      |>.mapError .coordinate
    if !guard.2 then throw (.guardNotTrue guard.1)
    pure guard.1
  let stringOutcomes ← plan.string.execute patterns input |>.mapError .string
  if stringOutcomes.length != environments.length then
    throw (.outcomeCardinality plan.string.targetField stringOutcomes.length)
  let dependencies ← dependencyCells stringOutcomes |>.mapError .dependency
  let numberOutcomes ← plan.number.executeWithRead input
      (readAfterString input dependencies) |>.mapError .number
  if numberOutcomes.length != environments.length then
    throw (.outcomeCardinality plan.number.placement.targetField
      numberOutcomes.length)
  pure {
    rows := (coordinates.zip (stringOutcomes.zip numberOutcomes)).map fun
      | (coordinate, string, number) => { coordinate, string, number }
  }

end CheckedCurrentRepetitionStringToNumberCascade

end A12Kernel
