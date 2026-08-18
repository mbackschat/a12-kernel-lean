import A12Kernel.Elaboration.CurrentRepetition
import A12Kernel.Elaboration.AddressedNumberField
import A12Kernel.Semantics.NumericDependency

/-! # Exact one-row CurrentRepetition Number cascade -/

namespace A12Kernel

/-- Fail-closed admission errors for the maintained one-row, one-level computation shape. -/
inductive CurrentRepetitionNumberCascadeElabError where
  | source (cause : CurrentRepetitionSourceElabError)
  | first (cause : AddressedNumberFieldElabError)
  | second (cause : AddressedNumberFieldElabError)
  | groupMismatch (source declaring : GroupPath)
  | sourceScope (actual : List RepeatableLevel)
  | firstScope (actual : List RepeatableLevel)
  | secondScope (actual : List RepeatableLevel)
  | dependency (expected actual : FieldId)
  | reverseDependency (field : FieldId)
  deriving Repr, DecidableEq

/-- One checked `CurrentRepetition(group) > 0` guarded direct copy followed by one exact row-local direct copy of its target. The shape is intentionally finite and carries no general condition tree or scheduler. -/
structure CheckedCurrentRepetitionNumberCascade (model : FlatModel) where
  private mk ::
  source : CheckedCurrentRepetitionSource model
  first : CheckedAddressedNumberField model
  second : CheckedAddressedNumberField model
  groupMatches : source.path = first.placement.declaringGroup
  sourceScope :
    model.repeatableScopeForGroupPath source.path = [source.group.level]
  firstScope :
    first.placement.targetDeclaration.repeatableScope = [source.group.level]
  secondScope :
    second.placement.targetDeclaration.repeatableScope = [source.group.level]
  dependency :
    second.placement.sourceDeclaration.id = first.placement.targetField
  noReverseDependency :
    first.placement.sourceDeclaration.id ≠ second.placement.targetField

/-- Check only the exact maintained cascade, including its one-level source and authored dependency edge. -/
def checkCurrentRepetitionNumberCascade
    (model : FlatModel) (declaringGroup : GroupPath)
    (group : SurfaceGroupPath)
    (firstTarget : FieldId) (firstSource : SurfaceFieldPath)
    (secondTarget : FieldId) (secondSource : SurfaceFieldPath) :
    Except CurrentRepetitionNumberCascadeElabError
      (CheckedCurrentRepetitionNumberCascade model) := do
  let source ← checkCurrentRepetitionSource model declaringGroup group
    |>.mapError .source
  let first ← checkAddressedNumberField model declaringGroup firstTarget firstSource
    |>.mapError .first
  let second ← checkAddressedNumberField model declaringGroup secondTarget secondSource
    |>.mapError .second
  if hGroup : source.path = first.placement.declaringGroup then
    if hSourceScope : model.repeatableScopeForGroupPath source.path =
        [source.group.level] then
      if hFirstScope : first.placement.targetDeclaration.repeatableScope =
          [source.group.level] then
        if hSecondScope : second.placement.targetDeclaration.repeatableScope =
            [source.group.level] then
          if hDependency : second.placement.sourceDeclaration.id =
              first.placement.targetField then
            if hReverse : first.placement.sourceDeclaration.id =
                second.placement.targetField then
              throw (.reverseDependency second.placement.targetField)
            else
              pure {
                source
                first
                second
                groupMatches := hGroup
                sourceScope := hSourceScope
                firstScope := hFirstScope
                secondScope := hSecondScope
                dependency := hDependency
                noReverseDependency := hReverse
              }
          else
            throw (.dependency first.placement.targetField
              second.placement.sourceDeclaration.id)
        else throw (.secondScope second.placement.targetDeclaration.repeatableScope)
      else throw (.firstScope first.placement.targetDeclaration.repeatableScope)
    else throw (.sourceScope (model.repeatableScopeForGroupPath source.path))
  else throw (.groupMismatch source.path first.placement.declaringGroup)

/-- The consumer-visible structural source and real field edges. Keeping these channels separate prevents group expansion from inventing computation cycles. -/
structure CurrentRepetitionNumberCascadeAnalysis where
  structuralGroup : GroupPath
  scope : List RepeatableLevel
  fieldDependencies : List (FieldId × List FieldId)
  deriving Repr, DecidableEq

/-- Exact rich outcomes in the only admitted execution order. -/
structure CurrentRepetitionNumberCascadeOutcomes where
  first : SourcedNumericTargetOutcome CellAddr
  second : SourcedNumericTargetOutcome CellAddr
  deriving Repr, DecidableEq

/-- Structural or leaf failures of the bounded executor. Multiple rows are explicit insufficient information. -/
inductive CurrentRepetitionNumberCascadeFault where
  | rows (cause : ActualRowEnvironmentError)
  | rowCardinality (actual : Nat)
  | coordinate (cause : EnvBindingError)
  | guardNotTrue (coordinate : Nat)
  | first (cause : AddressedNumberFieldFault)
  | second (cause : AddressedNumberFieldFault)
  | outcomeCardinality (target : FieldId) (actual : Nat)
  deriving Repr, DecidableEq

namespace CheckedCurrentRepetitionNumberCascade

def analyze (plan : CheckedCurrentRepetitionNumberCascade model) :
    CurrentRepetitionNumberCascadeAnalysis := {
  structuralGroup := plan.source.path
  scope := [plan.source.group.level]
  fieldDependencies := [
    (plan.first.placement.targetField,
      [plan.first.placement.sourceDeclaration.id]),
    (plan.second.placement.targetField,
      [plan.second.placement.sourceDeclaration.id])]
}

/-- Evaluate the sole admitted computation guard without adding a second condition tree. The coordinate remains available to structural-failure diagnostics. -/
def evaluatePositiveGuardAt
    (plan : CheckedCurrentRepetitionNumberCascade model)
    (environment : Env) : Except EnvBindingError (Nat × Bool) := do
  let coordinate ← plan.source.coordinateAt environment
  pure (coordinate, NumericComparisonOp.greater.holds coordinate 0)

private def readAfterFirst (input : CheckedDocument model)
    (first : SourcedNumericTargetOutcome CellAddr)
    (address : CellAddr) : Except CheckedDocumentError CheckedCell :=
  if address == first.targetField then
    .ok (NumericDependencyCell.ofOutcome first.outcome).checked
  else
    input.read address

/-- Execute the fixed positive structural guard, then expose the first exact addressed outcome only to the second direct copy. -/
def execute (plan : CheckedCurrentRepetitionNumberCascade model)
    (input : CheckedDocument model) :
    Except CurrentRepetitionNumberCascadeFault
      CurrentRepetitionNumberCascadeOutcomes := do
  let environments ← plan.first.placement.targetEnvironments input
    |>.mapError .rows
  let environment ← match environments with
    | [environment] => pure environment
    | rows => throw (.rowCardinality rows.length)
  let guard ← plan.evaluatePositiveGuardAt environment |>.mapError .coordinate
  if !guard.2 then throw (.guardNotTrue guard.1)
  let firstOutcomes ← plan.first.execute input |>.mapError .first
  let first ← match firstOutcomes with
    | [outcome] => pure outcome
    | outcomes =>
        throw (.outcomeCardinality plan.first.placement.targetField outcomes.length)
  let secondOutcomes ← plan.second.executeWithRead input
      (readAfterFirst input first) |>.mapError .second
  let second ← match secondOutcomes with
    | [outcome] => pure outcome
    | outcomes =>
        throw (.outcomeCardinality plan.second.placement.targetField outcomes.length)
  pure { first, second }

end CheckedCurrentRepetitionNumberCascade

end A12Kernel
