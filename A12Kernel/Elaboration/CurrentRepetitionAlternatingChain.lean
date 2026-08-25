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

/-- Execute the completed Number-to-String prefix, then expose each String completion only to the third step at its exact dependent address. -/
def execute (plan : CheckedCurrentRepetitionAlternatingChain model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model) :
    Except CurrentRepetitionAlternatingChainFault
      CurrentRepetitionAlternatingChainOutcomes := do
  let prefixOutcomes ← plan.numberToString.execute patterns input
    |>.mapError .numberToString
  let dependencies ← dependencyCells
      (prefixOutcomes.rows.map fun row => row.string)
    |>.mapError .dependency
  let thirdOutcomes ← plan.third.executeWithRead input
      (readAfterSecond input dependencies) |>.mapError .third
  if thirdOutcomes.length != prefixOutcomes.rows.length then
    throw (.outcomeCardinality plan.third.placement.targetField
      thirdOutcomes.length)
  pure {
    rows := (prefixOutcomes.rows.zip thirdOutcomes).map fun
      | (firstTwo, third) => {
          coordinate := firstTwo.coordinate
          first := firstTwo.number
          second := firstTwo.string
          third
        }
  }

end CheckedCurrentRepetitionAlternatingChain

end A12Kernel
