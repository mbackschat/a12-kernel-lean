import A12Kernel.Elaboration.RepeatableNumberAggregateCascade
import A12Kernel.Elaboration.AddressedFieldValueAsString
import A12Kernel.Semantics.HeterogeneousComputationDependency

/-! # Aggregate completion into one repeatable String target -/

namespace A12Kernel

inductive RepeatableNumberAggregateStringRowCascadeElabError where
  | suffix (cause : AddressedFieldValueAsStringElabError)
  | duplicateTarget (field : FieldId)
  | missingAggregateDependency (expected actual : FieldId)
  | scopeMismatch (producerScope suffixScope : List RepeatableLevel)
  | cycle (field : FieldId)
  deriving Repr, DecidableEq

private structure RepeatableNumberAggregateStringRowSuffixCertificate
    (cascade : CheckedRepeatableNumberAggregateCascade model)
    (suffix : CheckedAddressedFieldValueAsString model) : Type where
  distinctFromRows : suffix.targetField ≠ cascade.row.targetField
  distinctFromAggregate :
    suffix.targetField ≠ cascade.total.operation.core.target.id
  noBackEdge :
    (cascade.row.sourceFields ++ cascade.consumer.fieldDependencies).contains
      suffix.targetField = false
  sameScope : suffix.targetDeclaration.repeatableScope =
    cascade.row.targetDeclaration.repeatableScope
  aggregateDependency :
    suffix.sourceDeclaration.id = cascade.total.operation.core.target.id

/-- One checked row-to-root aggregate prefix followed by one repeatable `FieldValueAsString` target that reads the aggregate. -/
structure CheckedRepeatableNumberAggregateStringRowCascade
    (model : FlatModel) where
  private mk ::
  cascade : CheckedRepeatableNumberAggregateCascade model
  suffix : CheckedAddressedFieldValueAsString model
  distinctFromRows : suffix.targetField ≠ cascade.row.targetField
  distinctFromAggregate :
    suffix.targetField ≠ cascade.total.operation.core.target.id
  noBackEdge :
    (cascade.row.sourceFields ++ cascade.consumer.fieldDependencies).contains
      suffix.targetField = false
  sameScope : suffix.targetDeclaration.repeatableScope =
    cascade.row.targetDeclaration.repeatableScope
  aggregateDependency :
    suffix.sourceDeclaration.id = cascade.total.operation.core.target.id

private def certifyRepeatableNumberAggregateStringRowSuffix
    (cascade : CheckedRepeatableNumberAggregateCascade model)
    (suffix : CheckedAddressedFieldValueAsString model) :
    Except RepeatableNumberAggregateStringRowCascadeElabError
      (RepeatableNumberAggregateStringRowSuffixCertificate cascade suffix) := do
  if hRows : suffix.targetField ≠ cascade.row.targetField then
    if hAggregate : suffix.targetField ≠
        cascade.total.operation.core.target.id then
      if hBackEdge :
          (cascade.row.sourceFields ++
            cascade.consumer.fieldDependencies).contains
              suffix.targetField = false then
        let hScope ← certifyRepeatableNumberAggregateSuffixScope cascade
          suffix.targetDeclaration.repeatableScope
          |>.mapError fun (producerScope, suffixScope) =>
            .scopeMismatch producerScope suffixScope
        if hDependency : suffix.sourceDeclaration.id =
            cascade.total.operation.core.target.id then
          pure {
            distinctFromRows := hRows
            distinctFromAggregate := hAggregate
            noBackEdge := hBackEdge
            sameScope := hScope.sameScope
            aggregateDependency := hDependency
          }
        else throw (.missingAggregateDependency
          cascade.total.operation.core.target.id suffix.sourceDeclaration.id)
      else throw (.cycle suffix.targetField)
    else throw (.duplicateTarget suffix.targetField)
  else throw (.duplicateTarget suffix.targetField)

/-- Compose two checked phases. The String suffix must consume the aggregate in the producer's exact row scope, own a new target, and stay absent from every prefix dependency. -/
def checkRepeatableNumberAggregateStringRowCascade
    (cascade : CheckedRepeatableNumberAggregateCascade model)
    (suffixDeclaringGroup : GroupPath) (suffixTarget : FieldId)
    (suffixSource : SurfaceFieldPath) :
    Except RepeatableNumberAggregateStringRowCascadeElabError
      (CheckedRepeatableNumberAggregateStringRowCascade model) := do
  if suffixTarget == cascade.row.targetField ||
      suffixTarget == cascade.total.operation.core.target.id then
    throw (.duplicateTarget suffixTarget)
  if (cascade.row.sourceFields ++
      cascade.consumer.fieldDependencies).contains suffixTarget then
    throw (.cycle suffixTarget)
  let suffix ← checkAddressedFieldValueAsString model suffixDeclaringGroup
    suffixTarget suffixSource |>.mapError .suffix
  let certificate ←
    certifyRepeatableNumberAggregateStringRowSuffix cascade suffix
  pure {
    cascade
    suffix
    distinctFromRows := certificate.distinctFromRows
    distinctFromAggregate := certificate.distinctFromAggregate
    noBackEdge := certificate.noBackEdge
    sameScope := certificate.sameScope
    aggregateDependency := certificate.aggregateDependency
  }

structure RepeatableNumberAggregateStringRowCascadeAnalysis where
  cascade : RepeatableNumberAggregateCascadeAnalysis
  suffixTarget : FieldId
  repeatableScope : List RepeatableLevel
  fieldDependencies : List (FieldId × List FieldId)
  deriving Repr, DecidableEq

structure RepeatableNumberAggregateStringRowCascadeOutcomes where
  cascade : RepeatableNumberAggregateCascadeOutcomes
  suffix : List (SourcedStringTargetOutcome CellAddr)
  deriving Repr, DecidableEq

inductive RepeatableNumberAggregateStringRowCascadeFault where
  | cascade (cause : RepeatableNumberAggregateCascadeFault)
  | suffix (cause : AddressedFieldValueAsStringFault)
  deriving Repr, DecidableEq

namespace CheckedRepeatableNumberAggregateStringRowCascade

def analyze (plan : CheckedRepeatableNumberAggregateStringRowCascade model) :
    RepeatableNumberAggregateStringRowCascadeAnalysis := {
  cascade := plan.cascade.analyze
  suffixTarget := plan.suffix.targetField
  repeatableScope := plan.suffix.targetDeclaration.repeatableScope
  fieldDependencies := plan.cascade.analyze.fieldDependencies ++ [
    (plan.suffix.targetField, [plan.suffix.sourceDeclaration.id])]
}

def aggregateAddress
    (plan : CheckedRepeatableNumberAggregateStringRowCascade model) : CellAddr :=
  plan.cascade.aggregateAddress

/-- Expose the aggregate through the canonical Number-to-String dependency projection only at its exact root address; ordinary Number text remains document-owned. -/
def readPolicy
    (plan : CheckedRepeatableNumberAggregateStringRowCascade model)
    (outcome : NumericTargetOutcome) (input : CheckedDocument model)
    (address : CellAddr) : Except CheckedDocumentError CheckedCell :=
  if address == plan.aggregateAddress then
    .ok (StringDependencyCell.ofNumericOutcome outcome).checked
  else
    CheckedAddressedFieldValueAsString.readSource input address

/-- Execute the prefix, expose its aggregate through the cross-family root overlay, and reuse the addressed String target-row executor. -/
def execute (plan : CheckedRepeatableNumberAggregateStringRowCascade model)
    (world : World)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model) :
    Except RepeatableNumberAggregateStringRowCascadeFault
      RepeatableNumberAggregateStringRowCascadeOutcomes := do
  let cascade ← plan.cascade.execute world input |>.mapError .cascade
  let suffix ← plan.suffix.executeWithRead patterns input
    (plan.readPolicy cascade.aggregate.outcome input) |>.mapError .suffix
  pure { cascade, suffix }

end CheckedRepeatableNumberAggregateStringRowCascade

end A12Kernel
