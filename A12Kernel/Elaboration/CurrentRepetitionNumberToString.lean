import A12Kernel.Elaboration.CurrentRepetitionComputation
import A12Kernel.Elaboration.AddressedFieldValueAsString
import A12Kernel.Semantics.HeterogeneousComputationDependency

/-! # CurrentRepetition Number-to-String cascade -/

namespace A12Kernel

/-- Fail-closed admission errors for one maintained cross-family repeatable cascade. -/
inductive CurrentRepetitionNumberToStringElabError where
  | source (cause : CurrentRepetitionSourceElabError)
  | number (cause : AddressedNumberFieldElabError)
  | string (cause : AddressedFieldValueAsStringElabError)
  | groupMismatch (source declaring : GroupPath)
  | numberScope (actual : List RepeatableLevel)
  | stringScope (actual : List RepeatableLevel)
  | dependency (expected actual : FieldId)
  deriving Repr, DecidableEq

/-- One checked `CurrentRepetition(group) > 0` guarded Number copy followed by same-row `FieldValueAsString` over that Number target. The shape is finite and carries no generic condition tree or scheduler. -/
structure CheckedCurrentRepetitionNumberToStringCascade (model : FlatModel) where
  private mk ::
  source : CheckedCurrentRepetitionSource model
  number : CheckedAddressedNumberField model
  string : CheckedAddressedFieldValueAsString model
  groupMatches : source.path = number.placement.declaringGroup
  numberScope :
    number.placement.targetDeclaration.repeatableScope = source.completeScope
  stringScope :
    string.targetDeclaration.repeatableScope = source.completeScope
  dependency :
    string.sourceDeclaration.id = number.placement.targetField

/-- Check only the exact complete-scope cross-family cascade and its authored dependency edge. -/
def checkCurrentRepetitionNumberToStringCascade
    (model : FlatModel) (declaringGroup : GroupPath)
    (group : SurfaceGroupPath)
    (numberTarget : FieldId) (numberSource : SurfaceFieldPath)
    (stringTarget : FieldId) (stringSource : SurfaceFieldPath) :
    Except CurrentRepetitionNumberToStringElabError
      (CheckedCurrentRepetitionNumberToStringCascade model) := do
  let source ← checkCurrentRepetitionSource model declaringGroup group
    |>.mapError .source
  let number ←
    checkAddressedNumberField model declaringGroup numberTarget numberSource
      |>.mapError .number
  let string ←
    checkAddressedFieldValueAsString model declaringGroup stringTarget stringSource
      |>.mapError .string
  if hGroup : source.path = number.placement.declaringGroup then
    if hNumberScope : number.placement.targetDeclaration.repeatableScope =
        source.completeScope then
      if hStringScope : string.targetDeclaration.repeatableScope =
          source.completeScope then
        if hDependency : string.sourceDeclaration.id =
            number.placement.targetField then
          pure {
            source
            number
            string
            groupMatches := hGroup
            numberScope := hNumberScope
            stringScope := hStringScope
            dependency := hDependency
          }
        else
          throw (.dependency number.placement.targetField
            string.sourceDeclaration.id)
      else throw (.stringScope string.targetDeclaration.repeatableScope)
    else throw (.numberScope number.placement.targetDeclaration.repeatableScope)
  else throw (.groupMismatch source.path number.placement.declaringGroup)

/-- Exact typed outcomes for one selected row. -/
structure CurrentRepetitionNumberToStringRowOutcomes where
  coordinate : Nat
  number : SourcedNumericTargetOutcome CellAddr
  string : SourcedStringTargetOutcome CellAddr
  deriving Repr, DecidableEq

/-- Exact typed outcomes in physical row encounter order. -/
structure CurrentRepetitionNumberToStringOutcomes where
  rows : List CurrentRepetitionNumberToStringRowOutcomes
  deriving Repr, DecidableEq

/-- The complete structural coordinates and Number outcomes produced before the dependent String phase begins. -/
structure CurrentRepetitionNumberToStringNumberPhase where
  private mk ::
  coordinates : List Nat
  outcomes : List (SourcedNumericTargetOutcome CellAddr)
  deriving Repr, DecidableEq

/-- Structural or typed leaf failures of the bounded executor. An absent target row remains explicit insufficient information. -/
inductive CurrentRepetitionNumberToStringFault where
  | rows (cause : ActualRowEnvironmentError)
  | rowCardinality (actual : Nat)
  | coordinate (cause : EnvBindingError)
  | guardNotTrue (coordinate : Nat)
  | number (cause : AddressedNumberFieldFault)
  | string (cause : AddressedFieldValueAsStringFault)
  | outcomeCardinality (target : FieldId) (actual : Nat)
  deriving Repr, DecidableEq

namespace CheckedCurrentRepetitionNumberToStringCascade

/-- Keep the structural coordinate separate from both real field edges. -/
def analyze (plan : CheckedCurrentRepetitionNumberToStringCascade model) :
    CurrentRepetitionCascadeAnalysis := {
  structuralGroup := plan.source.path
  scope := plan.source.completeScope
  fieldDependencies := [
    (plan.number.placement.targetField,
      [plan.number.placement.sourceDeclaration.id]),
    (plan.string.targetField, [plan.string.sourceDeclaration.id])]
}

/-- Evaluate the sole admitted guard through the shared checked coordinate owner. -/
def evaluatePositiveGuardAt
    (plan : CheckedCurrentRepetitionNumberToStringCascade model)
    (environment : Env) : Except EnvBindingError (Nat × Bool) :=
  plan.source.evaluatePositiveGuardAt environment

private def readAfterNumber (input : CheckedDocument model)
    (numbers : List (SourcedNumericTargetOutcome CellAddr))
    (address : CellAddr) : Except CheckedDocumentError CheckedCell :=
  match numbers.find? fun outcome => outcome.targetField == address with
  | some outcome => .ok (StringDependencyCell.ofNumericOutcome outcome.outcome).checked
  | none => CheckedAddressedFieldValueAsString.readSource input address

/-- Execute the row/guard checks and complete every Number target before exposing any completion to the String consumer. -/
def executeNumberPhaseWithRead
    (plan : CheckedCurrentRepetitionNumberToStringCascade model)
    (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell) :
    Except CurrentRepetitionNumberToStringFault
      CurrentRepetitionNumberToStringNumberPhase := do
  let environments ← plan.number.placement.targetEnvironments input
    |>.mapError .rows
  if environments.isEmpty then throw (.rowCardinality 0)
  let coordinates ← environments.mapM fun environment => do
    let guard ← plan.evaluatePositiveGuardAt environment
      |>.mapError .coordinate
    if !guard.2 then throw (.guardNotTrue guard.1)
    pure guard.1
  let outcomes ← plan.number.executeWithRead input read |>.mapError .number
  if outcomes.length != environments.length then
    throw (.outcomeCardinality plan.number.placement.targetField
      outcomes.length)
  pure { coordinates, outcomes }

/-- Consume the complete Number phase at exact addresses and retain the dependent String outcomes separately. -/
def executeStringPhase
    (plan : CheckedCurrentRepetitionNumberToStringCascade model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (number : CurrentRepetitionNumberToStringNumberPhase) :
    Except CurrentRepetitionNumberToStringFault
      (List (SourcedStringTargetOutcome CellAddr)) := do
  let outcomes ← plan.string.executeWithRead patterns input
      (readAfterNumber input number.outcomes) |>.mapError .string
  if outcomes.length != number.coordinates.length then
    throw (.outcomeCardinality plan.string.targetField outcomes.length)
  pure outcomes

/-- Assemble completed typed phases without collapsing either family or the structural coordinate. -/
def assemblePhases
    (number : CurrentRepetitionNumberToStringNumberPhase)
    (string : List (SourcedStringTargetOutcome CellAddr)) :
    CurrentRepetitionNumberToStringOutcomes := {
  rows := (number.coordinates.zip (number.outcomes.zip string)).map fun
    | (coordinate, number, string) => { coordinate, number, string }
}

/-- Execute the fixed positive guard through a caller-supplied initial Number read, then expose each completed Number outcome only to the String conversion at that exact address. Target-row enumeration, String source projection, and prior-target classification remain owned by the immutable checked document. -/
def executeWithRead (plan : CheckedCurrentRepetitionNumberToStringCascade model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell) :
    Except CurrentRepetitionNumberToStringFault
      CurrentRepetitionNumberToStringOutcomes := do
  let number ← plan.executeNumberPhaseWithRead input read
  let string ← plan.executeStringPhase patterns input number
  pure (assemblePhases number string)

/-- Preserve the immutable-document entry point when no earlier completion feeds the Number source. -/
def execute (plan : CheckedCurrentRepetitionNumberToStringCascade model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model) :
    Except CurrentRepetitionNumberToStringFault
      CurrentRepetitionNumberToStringOutcomes :=
  plan.executeWithRead patterns input input.read

end CheckedCurrentRepetitionNumberToStringCascade

end A12Kernel
