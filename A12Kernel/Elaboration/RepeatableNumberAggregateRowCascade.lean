import A12Kernel.Elaboration.RepeatableNumberAggregateCascade

/-! # Aggregate completion into one repeatable Number consumer -/

namespace A12Kernel

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
    (plan : CheckedRepeatableNumberAggregateRowCascade model) : CellAddr := {
  field := plan.cascade.total.operation.core.target.id
  path := []
}

/-- Expose the completed aggregate only at its exact root address and delegate every other read to the immutable document. -/
def readPolicy (plan : CheckedRepeatableNumberAggregateRowCascade model)
    (outcome : NumericTargetOutcome) (input : CheckedDocument model)
    (address : CellAddr) : Except CheckedDocumentError CheckedCell :=
  if address == plan.aggregateAddress then
    .ok (NumericDependencyCell.ofOutcome outcome).checked
  else
    input.read address

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

end A12Kernel
