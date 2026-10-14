import A12Kernel.Elaboration.ParallelNumericDirectRun
import A12Kernel.Elaboration.RowComputationTable

/-! # Key-joined String and temporal targets

A computation into a String or temporal field of an indexed repeatable group may read the partner row
its key matches in a parallel group, as a joined Number computation does (spec/09 §5). Each target row
is evaluated once with that partner row bound beside it: a copy of a partner field takes the partner's
value, and an unmatched key or an empty partner field clears the target
([joined-carrier checkpoint](../../docs/sources/model-structure-and-declaration-probes.md#src-joined-carrier-admission),
rows `t01`–`t03`).

The operation is certified against the instance view of the target's joined groups, where each joined
group is a fixed group, so the ordinary String and temporal elaborators accept a partner field as a
fixed read. It evaluates over one context that reads each partner field at the partner row and every
other field at the target row. Guards are the joined Number carrier's guards, and the target rows,
their keys and their partner rows come from the same key joins.

An invalid-index or over-limit row clears without a guard or operand read, the joined Number
carrier's disposition. For these target kinds that is an assumption: the retained capture has neither
row, and the gap register keeps the evidence item.
-/

namespace A12Kernel

/-- A String or temporal operation certified against an instance view. Both evaluate over one
supplied read context, which is what lets a joined instance place each read. -/
inductive ParallelJoinedRowOperation (view : FlatModel) where
  | string (operation : CheckedRowStringExpression view)
  | temporal (operation : CheckedTemporalExpressionComputation view)

namespace ParallelJoinedRowOperation

def target : ParallelJoinedRowOperation view → FieldId
  | .string operation => operation.targetField
  | .temporal operation => operation.target

def family : ParallelJoinedRowOperation view → DocumentTargetFamily
  | .string _ => .string
  | .temporal operation => operation.family

/-- Field identities are the model's, since the instance view keeps every field. -/
def referencesWith (field : FieldId) (filterReads : CorrelatedHaving → Bool) :
    ParallelJoinedRowOperation view → Bool
  | .string operation => operation.expression.referencesField field
  | .temporal operation => operation.expression.referencesWith field filterReads

def evaluateIn (matchers : StringTargetMatchers) (context : ScalarComputationContext) :
    ParallelJoinedRowOperation view → Except RowComputationTableFault (DocumentTargetOutcome × CheckedCell)
  | .string operation => do
      let some matcher := matchers operation.targetField
        | throw (.targetPatternUnavailable operation.targetField)
      operation.evaluateIn matcher context context
  | .temporal operation => operation.run context |>.mapError .readBack

end ParallelJoinedRowOperation

abbrev ParallelJoinedRowAlternative (model : FlatModel) (joined : List GroupPath) :=
  ComputationAlternative (ParallelJoinedRowOperation (model.parallelInstanceView joined)) (ParallelNumericGuard model)

/-- A checked first-selected table of joined String or temporal alternatives into one target. Every
read outside the target row has a key join to its group, the first of which owns the target rows. -/
structure CheckedParallelJoinedRowStep (model : FlatModel) where
  private mk ::
  joined : List GroupPath
  primary : CheckedParallelTargetJoin model
  additional : List (CheckedParallelTargetJoin model)
  family : DocumentTargetFamily
  alternatives : List (ParallelJoinedRowAlternative model joined)
  sameTarget : alternatives.all (·.operation.target == primary.targetField) = true
  sameFamily : alternatives.all (·.operation.family == family) = true
  targetsCoherent : additional.all (·.targetDeclaration == primary.targetDeclaration) = true
  excludesTarget : alternatives.all (fun alternative =>
    !alternative.operation.referencesWith primary.targetField (·.forbidsTarget primary.targetField) &&
      !alternative.precondition.any (·.forbidsTarget primary.targetField)) = true
  guardsAdmitted : alternatives.all (fun alternative =>
    parallelNumericDirectGuardAdmitted (primary :: additional) alternative.precondition) = true
  scopesAvailable : (primary :: additional).all (·.scopeAvailable) = true

inductive ParallelJoinedRowStepError where
  | empty
  | noJoinedRead
  | route (error : ParallelComputationPlanError)
  | targetMismatch
  | familyMismatch
  | targetReference
  | guardNotJoined
  | operandFrameOutsideTarget
  deriving Repr, DecidableEq

inductive ParallelJoinedRowStepFault where
  | preliminary (cause : CheckedIndexPreliminaryError)
  | execution (cause : CheckedIsolatedParallelNumericDirectRun.ExecutionError)
  | guard (cause : CheckedComputationConditionError)
  | operation (cause : RowComputationTableFault)
  deriving Repr, DecidableEq

namespace CheckedParallelJoinedRowStep

def targetField (step : CheckedParallelJoinedRowStep model) : FieldId := step.primary.targetField

def joins (step : CheckedParallelJoinedRowStep model) : List (CheckedParallelTargetJoin model) :=
  step.primary :: step.additional

/-- Index columns participate statically even when a guard prevents every read (spec/07 §2). -/
def referencesIndexField (step : CheckedParallelJoinedRowStep model) (field : FieldId) : Bool :=
  step.joins.any fun join =>
    join.groups.leftIndexDeclaration.id == field || join.groups.rightIndexDeclaration.id == field

def referencesField (step : CheckedParallelJoinedRowStep model) (field : FieldId) : Bool :=
  step.alternatives.any (fun alternative =>
    alternative.precondition.any (·.referencesField field) ||
      alternative.operation.referencesWith field (·.referencesField field)) ||
    step.referencesIndexField field

def requiresProducer (step : CheckedParallelJoinedRowStep model)
    (producerProtected : FieldId → ResolvedGroupReference → Bool) (field : FieldId) : Bool :=
  step.alternatives.any (fun alternative =>
    alternative.precondition.any (·.requiresProducer step.targetField field (producerProtected field)) ||
      alternative.operation.referencesWith field
        (·.requiresProducer step.targetField field (producerProtected field))) ||
    step.referencesIndexField field

def protectionConditions (step : CheckedParallelJoinedRowStep model) : List (Option ComputationProtectionView) :=
  step.alternatives.map (·.precondition.map (·.protectionView))

/-- The reads of one joined instance: a field of a joined partner group at the row `partners` binds
for it, read empty when it binds none, and every other field at the target row. -/
def instanceContext (step : CheckedParallelJoinedRowStep model) (document : CheckedDocument model)
    (world : World) (partners : List (GroupPath × Env)) (target : Env) : ScalarComputationContext :=
  let base := (document.indexedComputationContextAt target).withWorld world
  let placed := fun field => match model.lookupUniqueId field with
    | .ok declaration => (step.joins.find? (·.groups.rightGroup.path.isPrefixOf declaration.groupPath)).map
        fun join => partners.lookup join.groups.rightGroup.path
    | .error _ => none
  { base with
    read := fun field => match placed field with
      | some (some partner) => (document.computationContextAt partner).read field
      | some none => DocumentComputationReadBack.empty
      | none => base.read field
    storedText := fun field => match placed field with
      | some (some partner) => (document.computationContextAt partner).storedText field
      | some none => none
      | none => base.storedText field
    numberText := fun field => match placed field with
      | some (some partner) => (document.computationContextAt partner).numberText field
      | some none => none
      | none => base.numberText field }

/-- Run every target row the primary join enumerates, reading `document`, which carries the plan's
completed targets. -/
def execute (step : CheckedParallelJoinedRowStep model) (world : World) (matchers : StringTargetMatchers)
    (document : CheckedDocument model) :
    Except ParallelJoinedRowStepFault (List (CellAddr × DocumentTargetOutcome × CheckedCell)) := do
  let selected := model.fields.filterMap fun declaration =>
    if step.referencesField declaration.id then some declaration.id else none
  let preliminary ← (document.applySelectedFullIndexPreliminary selected).mapError .preliminary
  let targets ← (CheckedIsolatedParallelNumericDirectRun.targetCoverage step.primary step.additional
    preliminary).mapError .execution
  targets.mapM fun target => do
    if target.indexInvalid || target.overLimit then
      return (target.address, step.family.noValue, DocumentComputationReadBack.empty)
    let key ← (CheckedIsolatedParallelNumericDirectRun.joinTargetKeyFor step.primary preliminary
      target.environment target.address).mapError .execution
    let partners ← (CheckedIsolatedParallelNumericDirectRun.partnerEnvironments step.joins preliminary
      target.environment key).mapError .execution
    let context := step.instanceContext document world partners target.environment
    let guardContext : ParallelNumericGuardContext := {
      joinedRead := context.read, ordinary := document.parallelGuardContextAt target.environment
      partnerAt := fun group => (partners.lookup group).map document.parallelGuardContextAt }
    match ComputationAlternative.selectFirstWith (·.eval guardContext) step.alternatives with
    | .error error =>
        if error.isValueFailure then
          pure (target.address, .valueError step.family, DocumentComputationReadBack.poison)
        else throw (.guard error)
    | .ok .noMatch => pure (target.address, step.family.noValue, DocumentComputationReadBack.empty)
    | .ok (.poison cause) => pure (target.address, step.family.poison cause, DocumentComputationReadBack.poison)
    | .ok (.selected operation) => do
        let (outcome, cell) ← (operation.evaluateIn matchers context).mapError .operation
        pure (target.address, outcome, cell)

end CheckedParallelJoinedRowStep

/-- Certify joined alternatives into `targetField`. Each field an operation or a view guard part reads
beyond the target row draws one key join to its group; a group already joined adds none. -/
def checkParallelJoinedRowStep (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (joined : List GroupPath) (alternatives : List (ParallelJoinedRowAlternative model joined)) :
    Except ParallelJoinedRowStepError (CheckedParallelJoinedRowStep model) := do
  let some first := alternatives.head? | throw .empty
  let family := first.operation.family
  let targetDeclaration ← (model.lookupUniqueId targetField).mapError (.route ∘ .targetResolve)
  let reads := model.fields.filter fun declaration =>
    !declaration.repeatableScope.isPrefixOf targetDeclaration.repeatableScope &&
      alternatives.any fun alternative =>
        alternative.operation.referencesWith declaration.id (·.referencesField declaration.id) ||
          alternative.precondition.any (·.readsField declaration.id)
  let joins ← reads.foldlM (fun (joins : List (CheckedParallelTargetJoin model)) declaration => do
    if joins.any (·.admitsGuardField declaration.id) then pure joins else
      let reference : SurfaceFieldPath :=
        { base := .absolute, groups := declaration.groupPath, field := declaration.name }
      let join ← (checkParallelTargetJoin model declaringGroup targetField reference).mapError .route
      pure (joins ++ [join])) []
  let primary :: additional := joins | throw .noJoinedRead
  if sameTarget : alternatives.all (·.operation.target == primary.targetField) = true then
    if sameFamily : alternatives.all (·.operation.family == family) = true then
      if targetsCoherent : additional.all (·.targetDeclaration == primary.targetDeclaration) = true then
        if excludesTarget : alternatives.all (fun alternative =>
            !alternative.operation.referencesWith primary.targetField (·.forbidsTarget primary.targetField) &&
              !alternative.precondition.any (·.forbidsTarget primary.targetField)) = true then
          if guardsAdmitted : alternatives.all (fun alternative =>
              parallelNumericDirectGuardAdmitted (primary :: additional) alternative.precondition) = true then
            if scopesAvailable : (primary :: additional).all (·.scopeAvailable) = true then
              pure { joined, primary, additional, family, alternatives, sameTarget, sameFamily,
                     targetsCoherent, excludesTarget, guardsAdmitted, scopesAvailable }
            else throw .operandFrameOutsideTarget
          else throw .guardNotJoined
        else throw .targetReference
      else throw .targetMismatch
    else throw .familyMismatch
  else throw .targetMismatch

end A12Kernel
