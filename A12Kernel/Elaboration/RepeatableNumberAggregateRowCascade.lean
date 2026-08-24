import A12Kernel.Elaboration.RepeatableNumberAggregateCascade
import A12Kernel.Elaboration.CurrentRepetitionComputation

/-! # Aggregate completion into one repeatable Number consumer -/

namespace A12Kernel

namespace CheckedRepeatableNumberAggregateCascade

def aggregateAddress
    (cascade : CheckedRepeatableNumberAggregateCascade model) : CellAddr := {
  field := cascade.total.operation.core.target.id
  path := []
}

/-- Expose one completed aggregate only at its exact root address and delegate every other read to the immutable document. -/
def readCompletion (cascade : CheckedRepeatableNumberAggregateCascade model)
    (outcome : NumericTargetOutcome) (input : CheckedDocument model)
    (address : CellAddr) : Except CheckedDocumentError CheckedCell :=
  if address == cascade.aggregateAddress then
    .ok (NumericDependencyCell.ofOutcome outcome).checked
  else
    input.read address

end CheckedRepeatableNumberAggregateCascade

inductive RepeatableNumberAggregateRowCascadeElabError where
  | suffix (cause : AddressedNumberFieldElabError)
  | duplicateTarget (field : FieldId)
  | missingAggregateDependency (expected actual : FieldId)
  | cycle (field : FieldId)
  deriving Repr, DecidableEq

/-- One checked row-to-root aggregate prefix followed by one repeatable direct Number assignment that reads the aggregate. -/
structure CheckedRepeatableNumberAggregateRowCascade (model : FlatModel) where
  private mk ::
  cascade : CheckedRepeatableNumberAggregateCascade model
  suffix : CheckedAddressedNumberField model
  distinctFromRows : suffix.placement.targetField ≠ cascade.row.targetField
  distinctFromAggregate :
    suffix.placement.targetField ≠ cascade.total.operation.core.target.id
  noBackEdge :
    (cascade.row.sourceFields ++ cascade.consumer.fieldDependencies).contains
      suffix.placement.targetField = false
  aggregateDependency :
    suffix.placement.sourceDeclaration.id =
      cascade.total.operation.core.target.id

private def certifyRepeatableNumberAggregateRowCascade
    (cascade : CheckedRepeatableNumberAggregateCascade model)
    (suffix : CheckedAddressedNumberField model) :
    Except RepeatableNumberAggregateRowCascadeElabError
      (CheckedRepeatableNumberAggregateRowCascade model) := do
  if hRows : suffix.placement.targetField ≠ cascade.row.targetField then
    if hAggregate : suffix.placement.targetField ≠
        cascade.total.operation.core.target.id then
      if hBackEdge :
          (cascade.row.sourceFields ++
            cascade.consumer.fieldDependencies).contains
              suffix.placement.targetField = false then
        if hDependency : suffix.placement.sourceDeclaration.id =
            cascade.total.operation.core.target.id then
          pure {
            cascade, suffix
            distinctFromRows := hRows
            distinctFromAggregate := hAggregate
            noBackEdge := hBackEdge
            aggregateDependency := hDependency
          }
        else throw (.missingAggregateDependency
          cascade.total.operation.core.target.id
          suffix.placement.sourceDeclaration.id)
      else throw (.cycle suffix.placement.targetField)
    else throw (.duplicateTarget suffix.placement.targetField)
  else throw (.duplicateTarget suffix.placement.targetField)

/-- Compose two already-checked execution phases without constructing a scheduler. The suffix must consume the aggregate, own a new target, and remain absent from every prefix dependency. -/
def checkRepeatableNumberAggregateRowCascade
    (cascade : CheckedRepeatableNumberAggregateCascade model)
    (suffixDeclaringGroup : GroupPath) (suffixTarget : FieldId)
    (suffixSource : SurfaceFieldPath) :
    Except RepeatableNumberAggregateRowCascadeElabError
      (CheckedRepeatableNumberAggregateRowCascade model) := do
  if suffixTarget == cascade.row.targetField ||
      suffixTarget == cascade.total.operation.core.target.id then
    throw (.duplicateTarget suffixTarget)
  if (cascade.row.sourceFields ++
      cascade.consumer.fieldDependencies).contains suffixTarget then
    throw (.cycle suffixTarget)
  let suffix ← checkAddressedNumberField model suffixDeclaringGroup
    suffixTarget suffixSource |>.mapError .suffix
  certifyRepeatableNumberAggregateRowCascade cascade suffix

structure RepeatableNumberAggregateRowCascadeAnalysis where
  cascade : RepeatableNumberAggregateCascadeAnalysis
  suffixTarget : FieldId
  repeatableScope : List RepeatableLevel
  fieldDependencies : List (FieldId × List FieldId)
  deriving Repr, DecidableEq

structure RepeatableNumberAggregateRowCascadeOutcomes where
  cascade : RepeatableNumberAggregateCascadeOutcomes
  suffix : List (SourcedNumericTargetOutcome CellAddr)
  deriving Repr, DecidableEq

inductive RepeatableNumberAggregateRowCascadeFault where
  | cascade (cause : RepeatableNumberAggregateCascadeFault)
  | suffix (cause : AddressedNumberFieldFault)
  deriving Repr, DecidableEq

namespace CheckedRepeatableNumberAggregateRowCascade

def analyze (plan : CheckedRepeatableNumberAggregateRowCascade model) :
    RepeatableNumberAggregateRowCascadeAnalysis := {
  cascade := plan.cascade.analyze
  suffixTarget := plan.suffix.placement.targetField
  repeatableScope := plan.suffix.placement.targetDeclaration.repeatableScope
  fieldDependencies := plan.cascade.analyze.fieldDependencies ++ [
    (plan.suffix.placement.targetField,
      [plan.suffix.placement.sourceDeclaration.id])]
}

def aggregateAddress
    (plan : CheckedRepeatableNumberAggregateRowCascade model) : CellAddr :=
  plan.cascade.aggregateAddress

/-- Expose the completed aggregate only at its exact root address and delegate every other read to the immutable document. -/
def readPolicy (plan : CheckedRepeatableNumberAggregateRowCascade model)
    (outcome : NumericTargetOutcome) (input : CheckedDocument model)
    (address : CellAddr) : Except CheckedDocumentError CheckedCell :=
  plan.cascade.readCompletion outcome input address

/-- Execute the prefix, overlay its rich aggregate outcome at the root, then reuse the existing repeatable direct-assignment executor and its target-row enumeration. -/
def execute (plan : CheckedRepeatableNumberAggregateRowCascade model)
    (world : World) (input : CheckedDocument model) :
    Except RepeatableNumberAggregateRowCascadeFault
      RepeatableNumberAggregateRowCascadeOutcomes := do
  let cascade ← plan.cascade.execute world input |>.mapError .cascade
  let suffix ← plan.suffix.executeWithRead input
    (plan.readPolicy cascade.aggregate.outcome input) |>.mapError .suffix
  pure { cascade, suffix }

end CheckedRepeatableNumberAggregateRowCascade

inductive RepeatableNumberAggregateRowChainElabError where
  | duplicateTarget (field : FieldId)
  | missingAggregateDependency (expected actual : FieldId)
  | cycle (field : FieldId)
  | incoherentChain
  deriving Repr, DecidableEq

private def aggregateRowChainTargets
    (suffix : CheckedCurrentRepetitionNumberCascade model) : List FieldId :=
  [suffix.first.placement.targetField, suffix.second.placement.targetField]

/-- One checked aggregate prefix followed by the existing fixed two-step repeatable Number cascade. -/
structure CheckedRepeatableNumberAggregateRowChain (model : FlatModel) where
  private mk ::
  cascade : CheckedRepeatableNumberAggregateCascade model
  suffix : CheckedCurrentRepetitionNumberCascade model
  distinctTargets : (aggregateRowChainTargets suffix).all (fun field =>
    field != cascade.row.targetField &&
      field != cascade.total.operation.core.target.id) = true
  noBackEdge : (aggregateRowChainTargets suffix).all (fun field =>
    !(cascade.row.sourceFields ++
      cascade.consumer.fieldDependencies).contains field) = true
  aggregateDependency :
    suffix.first.placement.sourceDeclaration.id =
      cascade.total.operation.core.target.id

/-- Compose the two checked phases while retaining their existing finite orders. Every suffix target must be new and absent from the prefix reads, and the first suffix operation must consume the aggregate. -/
def checkRepeatableNumberAggregateRowChain
    (cascade : CheckedRepeatableNumberAggregateCascade model)
    (suffix : CheckedCurrentRepetitionNumberCascade model) :
    Except RepeatableNumberAggregateRowChainElabError
      (CheckedRepeatableNumberAggregateRowChain model) := do
  let targets := aggregateRowChainTargets suffix
  if hDistinct : targets.all (fun field =>
      field != cascade.row.targetField &&
        field != cascade.total.operation.core.target.id) = true then
    if hBackEdge : targets.all (fun field =>
        !(cascade.row.sourceFields ++
          cascade.consumer.fieldDependencies).contains field) = true then
      if hDependency : suffix.first.placement.sourceDeclaration.id =
          cascade.total.operation.core.target.id then
        pure {
          cascade, suffix
          distinctTargets := hDistinct
          noBackEdge := hBackEdge
          aggregateDependency := hDependency
        }
      else throw (.missingAggregateDependency
        cascade.total.operation.core.target.id
        suffix.first.placement.sourceDeclaration.id)
    else
      match targets.find? fun field =>
          (cascade.row.sourceFields ++
            cascade.consumer.fieldDependencies).contains field with
      | some field => throw (.cycle field)
      | none => throw .incoherentChain
  else
    match targets.find? fun field =>
        field == cascade.row.targetField ||
          field == cascade.total.operation.core.target.id with
    | some field => throw (.duplicateTarget field)
    | none => throw .incoherentChain

structure RepeatableNumberAggregateRowChainAnalysis where
  cascade : RepeatableNumberAggregateCascadeAnalysis
  suffix : CurrentRepetitionCascadeAnalysis
  deriving Repr, DecidableEq

structure RepeatableNumberAggregateRowChainOutcomes where
  cascade : RepeatableNumberAggregateCascadeOutcomes
  suffix : CurrentRepetitionNumberCascadeOutcomes
  deriving Repr, DecidableEq

inductive RepeatableNumberAggregateRowChainFault where
  | cascade (cause : RepeatableNumberAggregateCascadeFault)
  | suffix (cause : CurrentRepetitionNumberCascadeFault)
  deriving Repr, DecidableEq

namespace CheckedRepeatableNumberAggregateRowChain

def analyze (plan : CheckedRepeatableNumberAggregateRowChain model) :
    RepeatableNumberAggregateRowChainAnalysis := {
  cascade := plan.cascade.analyze
  suffix := plan.suffix.analyze
}

/-- Execute the aggregate prefix, expose its completion to the first repeatable suffix step, and reuse the existing exact-row overlay for the second step. -/
def execute (plan : CheckedRepeatableNumberAggregateRowChain model)
    (world : World) (input : CheckedDocument model) :
    Except RepeatableNumberAggregateRowChainFault
      RepeatableNumberAggregateRowChainOutcomes := do
  let cascade ← plan.cascade.execute world input |>.mapError .cascade
  let suffix ← plan.suffix.executeWithRead input
    (plan.cascade.readCompletion cascade.aggregate.outcome input)
    |>.mapError .suffix
  pure { cascade, suffix }

end CheckedRepeatableNumberAggregateRowChain

end A12Kernel
