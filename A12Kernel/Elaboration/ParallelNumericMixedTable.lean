import A12Kernel.Elaboration.ParallelNumericAlternativeTable
import A12Kernel.Elaboration.NumericComputation.Table

namespace A12Kernel

/-- A combined declaration table retains each operation's checked addressing contract; an
ordinary starred source must not become a key-joined source merely by sharing a target (spec/09 §5). -/
inductive CheckedParallelNumericMember (model : FlatModel) (target : FieldId) where
  | joined (alternative : CheckedParallelNumericAlternative model target)
  | bound (policy : NumericTargetPolicy)
      (alternative : CheckedNumericComputationAlternative model target policy)

namespace CheckedParallelNumericMember

def precondition : CheckedParallelNumericMember model target → Option (CheckedComputationCondition model)
  | .joined alternative => alternative.precondition
  | .bound _ alternative => alternative.precondition

def joinedOperation? : CheckedParallelNumericMember model target → Option (CheckedIsolatedParallelNumericDirectRun model)
  | .joined alternative => some alternative.operation
  | .bound _ _ => none

def referencesField (member : CheckedParallelNumericMember model target) (field : FieldId) : Bool :=
  match member with
  | .joined alternative => alternative.operation.referencesField field || alternative.operation.referencesIndexField field
  | .bound _ alternative => alternative.precondition.any (·.referencesField field) ||
      alternative.operation.operation.core.expression.anyAtom (CheckedNumericComputationAtom.references model field)

def requiresProducer (member : CheckedParallelNumericMember model target)
    (producerProtected : ResolvedGroupReference → Bool) (field : FieldId) : Bool :=
  match member with
  | .joined alternative =>
      alternative.operation.expression.anyAtom (NumericComputationAtom.referencesField model field) ||
        alternative.operation.referencesIndexField field ||
        alternative.precondition.any (·.requiresProducer target field producerProtected)
  | .bound _ alternative =>
      alternative.operation.operation.core.expression.anyAtom
        (CheckedNumericComputationAtom.requiresProducer model target field producerProtected) ||
        alternative.precondition.any (·.requiresProducer target field producerProtected)

def evaluateSelected (member : CheckedParallelNumericMember model target)
    (context : NumericComputationEvaluationContext) :
    Except CheckedIsolatedParallelNumericDirectRun.ExecutionError NumericTargetOutcome := do
  match member with
  | .joined alternative => alternative.operation.evaluateSelected context.scalar
  | .bound _ alternative =>
      match ← alternative.operation.evaluateIn context |>.mapError .numeric with
      | .supported outcome => pure outcome
      | .unsupported fault => throw (.unsupportedTarget fault)

end CheckedParallelNumericMember

/-- All declarations for a target share index participation and one first-selection decision,
while each selected operation keeps its ordinary or joined evaluator (spec/09 §§3.1, 5). -/
structure CheckedMixedParallelNumericTable (model : FlatModel) where
  targetField : FieldId
  primary : CheckedParallelNumericTargetRoute model
  primaryMatches : primary.targetField = targetField
  members : List (CheckedParallelNumericMember model targetField)

namespace CheckedMixedParallelNumericTable

def operations (table : CheckedMixedParallelNumericTable model) : List (CheckedIsolatedParallelNumericDirectRun model) :=
  table.members.filterMap (·.joinedOperation?)

def operandRoutes (table : CheckedMixedParallelNumericTable model) : List (CheckedParallelNumericTargetRoute model) :=
  table.operations.foldl (fun routes operation => operation.operandRoutes.foldl
    (fun routes route => if routes.any (·.groups.rightGroup.path == route.groups.rightGroup.path)
      then routes else routes ++ [route]) routes) [table.primary]

def executeTarget (table : CheckedMixedParallelNumericTable model)
    (preliminary : CheckedIndexPreliminary model) (document : CheckedDocument model)
    (target : ParallelNumericTargetCoverage) :
    Except CheckedIsolatedParallelNumericDirectRun.ExecutionError ParallelNumericDirectOutcome := do
  let column ← preliminary.resolveIndexColumn table.primary.groups.leftGroup target.environment
    |>.mapError (CheckedIsolatedParallelNumericDirectRun.ExecutionError.indexColumn .target)
  let some entry := column.entries.find? (·.environment == target.environment)
    | throw (.missingTargetIndex target.address)
  let key := entry.key
  let cells ← table.operations.mapM fun operation =>
    operation.operandCellsWith preliminary document.read target.environment key
  let bound := document.computationContextAt target.environment
  let scalar := { bound with read := fun field =>
    match cells.flatten.find? (·.1 == field) with
    | some (_, cell) => cell
    | none => bound.read field }
  let reads := document.computationFillContext
  let context : NumericComputationEvaluationContext := {
    scalar, document := reads.document, outer := target.environment
    filterRead := reads.read, filterStoredText := reads.storedText, filterNumberText := reads.numberText
    starRead := reads.read, starStoredText := reads.storedText
    indexColumn? := some (document.resolveSemanticIndexColumnWith document.read) }
  let alternatives := table.members.map fun member =>
    ({ precondition := member.precondition, operation := member } :
      CheckedComputationAlternative model (CheckedParallelNumericMember model table.targetField))
  let outcome ← match CheckedComputationAlternative.selectFirstCheckedIn alternatives context with
    | .error error => if error.isValueFailure then pure (.invalidNoValue .calculationValue) else throw (.guard error)
    | .ok .noMatch => pure .noValue
    | .ok (.poison cause) => pure (.inheritedPoison cause)
    | .ok (.selected member) => member.evaluateSelected context
  pure { address := target.address, outcome }

end CheckedMixedParallelNumericTable
end A12Kernel
