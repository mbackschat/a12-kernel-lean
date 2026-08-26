import A12Kernel.Elaboration.CurrentRepetitionNumberToString
import A12Kernel.Elaboration.AddressedFieldValueAsNumber
import A12Kernel.Semantics.StringCascade

/-! # CurrentRepetition alternating Number/String chain -/

namespace A12Kernel

/-- Fail-closed admission errors for one fixed three-computation repeatable chain. -/
inductive CurrentRepetitionAlternatingChainElabError where
  | numberToString (cause : CurrentRepetitionNumberToStringElabError)
  | third (cause : AddressedFieldValueAsNumberElabError)
  | thirdScope (actual : List RepeatableLevel)
  | dependency (expected actual : FieldId)
  | cycle (field : FieldId)
  | reverseDependency (field : FieldId)
  deriving Repr, DecidableEq

/-- The checked Number-to-String prefix followed by one String-to-Number step at each exact row address. This is a fixed chain, not a general scheduler. -/
structure CheckedCurrentRepetitionAlternatingChain (model : FlatModel) where
  private mk ::
  numberToString : CheckedCurrentRepetitionNumberToStringCascade model
  third : CheckedAddressedFieldValueAsNumber model
  thirdScope :
    third.placement.targetDeclaration.repeatableScope =
      numberToString.source.completeScope
  dependency :
    third.placement.sourceDeclaration.id = numberToString.string.targetField
  noCycle :
    numberToString.number.placement.sourceDeclaration.id ≠
      third.placement.targetField
  noReverseDependency :
    numberToString.string.sourceDeclaration.id ≠ third.placement.targetField

/-- Compose the checked Number-to-String prefix with only the third edge and possible Number back-edges. -/
def checkCurrentRepetitionAlternatingChain
    (model : FlatModel) (declaringGroup : GroupPath)
    (group : SurfaceGroupPath)
    (firstTarget : FieldId) (firstSource : SurfaceFieldPath)
    (secondTarget : FieldId) (secondSource : SurfaceFieldPath)
    (thirdTarget : FieldId) (thirdSource : SurfaceTextFieldOperand) :
    Except CurrentRepetitionAlternatingChainElabError
      (CheckedCurrentRepetitionAlternatingChain model) := do
  let numberToString ← checkCurrentRepetitionNumberToStringCascade model
      declaringGroup group firstTarget firstSource secondTarget secondSource
    |>.mapError .numberToString
  let third ← checkAddressedFieldValueAsNumber model
      declaringGroup thirdTarget thirdSource
    |>.mapError .third
  if hThirdScope : third.placement.targetDeclaration.repeatableScope =
      numberToString.source.completeScope then
    if hDependency : third.placement.sourceDeclaration.id =
        numberToString.string.targetField then
      if hCycle : numberToString.number.placement.sourceDeclaration.id =
          third.placement.targetField then
        throw (.cycle third.placement.targetField)
      else if hReverse : numberToString.string.sourceDeclaration.id =
          third.placement.targetField then
        throw (.reverseDependency third.placement.targetField)
      else
        pure {
          numberToString
          third
          thirdScope := hThirdScope
          dependency := hDependency
          noCycle := hCycle
          noReverseDependency := hReverse
        }
    else throw (.dependency numberToString.string.targetField
      third.placement.sourceDeclaration.id)
  else throw (.thirdScope third.placement.targetDeclaration.repeatableScope)

/-- Exact typed outcomes for one selected row. -/
structure CurrentRepetitionAlternatingChainRowOutcomes where
  coordinate : Nat
  first : SourcedNumericTargetOutcome CellAddr
  second : SourcedStringTargetOutcome CellAddr
  third : SourcedNumericTargetOutcome CellAddr
  deriving Repr, DecidableEq

/-- Exact typed outcomes in physical row encounter order. -/
structure CurrentRepetitionAlternatingChainOutcomes where
  rows : List CurrentRepetitionAlternatingChainRowOutcomes
  deriving Repr, DecidableEq

/-- Prefix, dependency-projection, third-leaf, or cardinality failure of the fixed executor. -/
inductive CurrentRepetitionAlternatingChainFault where
  | numberToString (cause : CurrentRepetitionNumberToStringFault)
  | dependency (cause : StringDependencyFault)
  | third (cause : AddressedFieldValueAsNumberFault)
  | outcomeCardinality (target : FieldId) (actual : Nat)
  deriving Repr, DecidableEq

namespace CheckedCurrentRepetitionAlternatingChain

/-- Keep the structural coordinate separate from all three field edges. -/
def analyze (plan : CheckedCurrentRepetitionAlternatingChain model) :
    CurrentRepetitionCascadeAnalysis := {
  structuralGroup := plan.numberToString.source.path
  scope := plan.numberToString.source.completeScope
  fieldDependencies := [
    (plan.numberToString.number.placement.targetField,
      [plan.numberToString.number.placement.sourceDeclaration.id]),
    (plan.numberToString.string.targetField,
      [plan.numberToString.string.sourceDeclaration.id]),
    (plan.third.placement.targetField,
      [plan.third.placement.sourceDeclaration.id])]
}

private def dependencyCells
    (outcomes : List (SourcedStringTargetOutcome CellAddr)) :
    Except StringDependencyFault (List (CellAddr × CheckedCell)) :=
  outcomes.mapM fun outcome => do
    let dependency ← StringDependencyCell.ofOutcome outcome.outcome
    pure (outcome.targetField, dependency.checked)

private def readAfterSecond (input : CheckedDocument model)
    (dependencies : List (CellAddr × CheckedCell))
    (address : CellAddr) : Except CheckedDocumentError CheckedCell :=
  match dependencies.find? fun dependency => dependency.1 == address with
  | some dependency => .ok dependency.2
  | none => input.read address

/-- Consume the complete String phase at exact addresses and retain the third Number outcomes separately. Dependency conversion stays at this boundary. -/
def executeThirdPhase (plan : CheckedCurrentRepetitionAlternatingChain model)
    (input : CheckedDocument model)
    (string : List (SourcedStringTargetOutcome CellAddr)) :
    Except CurrentRepetitionAlternatingChainFault
      (List (SourcedNumericTargetOutcome CellAddr)) := do
  let dependencies ← dependencyCells string
    |>.mapError .dependency
  let thirdOutcomes ← plan.third.executeWithRead input
      (readAfterSecond input dependencies) |>.mapError .third
  if thirdOutcomes.length != string.length then
    throw (.outcomeCardinality plan.third.placement.targetField
      thirdOutcomes.length)
  pure thirdOutcomes

/-- Assemble the three completed typed phases without collapsing their structural coordinate or family boundaries. -/
def assemblePhases
    (number : CurrentRepetitionNumberToStringNumberPhase)
    (string : List (SourcedStringTargetOutcome CellAddr))
    (third : List (SourcedNumericTargetOutcome CellAddr)) :
    CurrentRepetitionAlternatingChainOutcomes :=
  let firstTwo :=
    CheckedCurrentRepetitionNumberToStringCascade.assemblePhases number string
  {
    rows := (firstTwo.rows.zip third).map fun
      | (row, third) => {
          coordinate := row.coordinate
          first := row.number
          second := row.string
          third
        }
  }

/-- Execute all addressed Number targets, then all dependent String targets, then expose each completed String only to the third Number step at its exact address. -/
def execute (plan : CheckedCurrentRepetitionAlternatingChain model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model) :
    Except CurrentRepetitionAlternatingChainFault
      CurrentRepetitionAlternatingChainOutcomes := do
  let number ← plan.numberToString.executeNumberPhaseWithRead input input.read
    |>.mapError .numberToString
  let string ← plan.numberToString.executeStringPhase patterns input number
    |>.mapError .numberToString
  let third ← plan.executeThirdPhase input string
  pure (assemblePhases number string third)

/-- Execute the fixed alternating chain and project its already-sourced exact outcomes through the existing family-preserving String/Number carrier. The Number child retains both Number phases and each child remains independently applicable. Its collections are extensional, so the row-wise pairing makes no mixed-document, public phase-order, or scheduling claim. -/
def executeResult (plan : CheckedCurrentRepetitionAlternatingChain model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (numberPayloadAt : CellAddr → NumberPayload)
    (numberMessages : List (ComputationFormalMessage NumberPayload))
    (stringResidualMessages : List StringResidual) :
    Except CurrentRepetitionAlternatingChainFault
      (StringNumberComputationRunView
        StringResidual NumberPayload CellAddr) := do
  let outcomes ← plan.execute patterns input
  pure {
    string := StringComputationRunView.fromSourcedOutcomes
      stringResidualMessages (outcomes.rows.map (·.second))
    number := NumericComputationRunView.fromSourceOutcomesWithMessages
      MessagePointer.ofCellAddr numberPayloadAt numberMessages
      (outcomes.rows.flatMap fun row => [row.first, row.third])
  }

end CheckedCurrentRepetitionAlternatingChain

end A12Kernel
