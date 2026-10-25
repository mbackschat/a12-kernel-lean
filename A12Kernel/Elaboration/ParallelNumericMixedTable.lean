import A12Kernel.Elaboration.ParallelNumericAlternativeTable
import A12Kernel.Elaboration.NumericComputation.Table

namespace A12Kernel

/-- A combined declaration table retains each operation's checked addressing contract; an
ordinary starred source must not become a key-joined source merely by sharing a target (spec/09 §5).

A `bound` member is a separate declaration that reads no partner field. Under the target's key
join it never stores a value. Leading the table, it clears the target at every row whatever its
guard (k22-cross-declaration-2026-10-24, `Out05`, `Out11`, `Out15`). Behind a joined lead the scan
passes over it unread: a holding guard selects nothing, a malformed read poisons nothing, and a later
joined declaration still computes (k22-joined-declaration-order-2026-10-25, `W02`, `W06`). Its
checked alternative is kept for dependencies and index participation only. -/
inductive CheckedParallelNumericMember (model : FlatModel) (target : FieldId) where
  | joined (alternative : CheckedParallelNumericAlternative model target)
  | bound (policy : NumericTargetPolicy)
      (alternative : CheckedNumericComputationAlternative model target policy)

namespace CheckedParallelNumericMember

def protectionView : CheckedParallelNumericMember model target → Option ComputationProtectionView
  | .joined alternative => alternative.precondition.map (·.protectionView)
  | .bound _ alternative => alternative.precondition.map (·.protectionView)

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
      alternative.operation.expression.anyAtom (·.requiresProducer target field producerProtected) ||
        alternative.operation.referencesIndexField field ||
        alternative.precondition.any (·.requiresProducer target field producerProtected)
  | .bound _ alternative =>
      alternative.operation.operation.core.expression.anyAtom
        (CheckedNumericComputationAtom.requiresProducer model target field producerProtected) ||
        alternative.precondition.any (·.requiresProducer target field producerProtected)

end CheckedParallelNumericMember

/-- All declarations for a target share index participation and one first-selection decision
over the joined members; a selected joined operation keeps its joined evaluator, and a bound member
decides the outcome only by leading (spec/09 §§3.1, 5). -/
structure CheckedMixedParallelNumericTable (model : FlatModel) where
  targetField : FieldId
  primary : CheckedParallelNumericTargetRoute model
  primaryMatches : primary.targetField = targetField
  members : List (CheckedParallelNumericMember model targetField)

namespace CheckedMixedParallelNumericTable

def operations (table : CheckedMixedParallelNumericTable model) : List (CheckedIsolatedParallelNumericDirectRun model) :=
  table.members.filterMap (·.joinedOperation?)

/-- Whether a declaration reading no partner field comes first, which clears every target row. -/
def leadsUnjoined (table : CheckedMixedParallelNumericTable model) : Bool :=
  match table.members with
  | .bound .. :: _ => true
  | _ => false

/-- The joined members in declaration order, the alternatives a scan behind a joined lead selects from. -/
def joinedAlternatives (table : CheckedMixedParallelNumericTable model) :
    List (ComputationAlternative (CheckedIsolatedParallelNumericDirectRun model) (ParallelNumericGuard model)) :=
  table.members.filterMap fun
    | .joined alternative => some { precondition := alternative.precondition, operation := alternative.operation }
    | .bound .. => none

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
  let ordinary := document.parallelGuardContextAt target.environment
  let bound := ordinary.scalar
  let scalar := { bound with read := fun field =>
    match cells.flatten.find? (·.1 == field) with
    | some (_, cell) => cell
    | none => bound.read field }
  let partners ← CheckedIsolatedParallelNumericDirectRun.partnerEnvironments (table.operandRoutes.map (·.join)) preliminary
    target.environment key
  let context : ParallelNumericGuardContext := {
    joinedRead := scalar.read, ordinary := { ordinary with scalar }
    partnerAt := fun group => (partners.lookup group).map document.parallelGuardContextAt }
  let outcome ← if table.leadsUnjoined then pure .noValue else
    match ComputationAlternative.selectFirstWith (·.eval context) table.joinedAlternatives with
    | .error error => if error.isValueFailure then pure (.invalidNoValue .calculationValue) else throw (.guard error)
    | .ok .noMatch => pure .noValue
    | .ok (.poison cause) => pure (.inheritedPoison cause)
    | .ok (.selected operation) => operation.evaluateSelected context
  pure { address := target.address, outcome }

end CheckedMixedParallelNumericTable
end A12Kernel
