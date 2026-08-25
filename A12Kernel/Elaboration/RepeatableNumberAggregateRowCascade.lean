import A12Kernel.Elaboration.RepeatableNumberAggregateCascade
import A12Kernel.Elaboration.CurrentRepetitionComputation
import A12Kernel.Elaboration.CurrentRepetitionNumberToString
import A12Kernel.Elaboration.AddressedNumberBinary
import A12Kernel.Elaboration.AddressedNumberDivision

/-! # Aggregate completion into bounded repeatable scalar consumers -/

namespace A12Kernel

inductive RepeatableNumberAggregateRowCascadeElabError where
  | suffix (cause : AddressedNumberFieldElabError)
  | duplicateTarget (field : FieldId)
  | missingAggregateDependency (expected actual : FieldId)
  | scopeMismatch (producerScope suffixScope : List RepeatableLevel)
  | cycle (field : FieldId)
  deriving Repr, DecidableEq

/-- The shared static certificate for a direct Number suffix that consumes one aggregate completion in the producer's exact row scope. -/
private structure RepeatableNumberAggregateRowSuffixCertificate
    (cascade : CheckedRepeatableNumberAggregateCascade model)
    (suffix : CheckedAddressedNumberField model) : Type where
  distinctFromRows : suffix.placement.targetField ≠ cascade.row.targetField
  distinctFromAggregate :
    suffix.placement.targetField ≠ cascade.total.operation.core.target.id
  noBackEdge :
    (cascade.row.sourceFields ++ cascade.consumer.fieldDependencies).contains
      suffix.placement.targetField = false
  sameScope : suffix.placement.targetDeclaration.repeatableScope =
    cascade.row.targetDeclaration.repeatableScope
  aggregateDependency :
    suffix.placement.sourceDeclaration.id =
      cascade.total.operation.core.target.id

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
  sameScope : suffix.placement.targetDeclaration.repeatableScope =
    cascade.row.targetDeclaration.repeatableScope
  aggregateDependency :
    suffix.placement.sourceDeclaration.id =
      cascade.total.operation.core.target.id

private def certifyRepeatableNumberAggregateRowSuffix
    (cascade : CheckedRepeatableNumberAggregateCascade model)
    (suffix : CheckedAddressedNumberField model) :
    Except RepeatableNumberAggregateRowCascadeElabError
      (RepeatableNumberAggregateRowSuffixCertificate cascade suffix) := do
  if hRows : suffix.placement.targetField ≠ cascade.row.targetField then
    if hAggregate : suffix.placement.targetField ≠
        cascade.total.operation.core.target.id then
      if hBackEdge :
          (cascade.row.sourceFields ++
            cascade.consumer.fieldDependencies).contains
              suffix.placement.targetField = false then
        let hScope ← certifyRepeatableNumberAggregateSuffixScope cascade
          suffix.placement.targetDeclaration.repeatableScope
          |>.mapError fun (producerScope, suffixScope) =>
            .scopeMismatch producerScope suffixScope
        if hDependency : suffix.placement.sourceDeclaration.id =
            cascade.total.operation.core.target.id then
          pure {
            distinctFromRows := hRows
            distinctFromAggregate := hAggregate
            noBackEdge := hBackEdge
            sameScope := hScope.sameScope
            aggregateDependency := hDependency
          }
        else throw (.missingAggregateDependency
          cascade.total.operation.core.target.id
          suffix.placement.sourceDeclaration.id)
      else throw (.cycle suffix.placement.targetField)
    else throw (.duplicateTarget suffix.placement.targetField)
  else throw (.duplicateTarget suffix.placement.targetField)

/-- Compose two already-checked execution phases without constructing a scheduler. The suffix must consume the aggregate in the producer's exact row scope, own a new target, and remain absent from every prefix dependency. -/
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
  let certificate ← certifyRepeatableNumberAggregateRowSuffix cascade suffix
  pure {
    cascade, suffix
    distinctFromRows := certificate.distinctFromRows
    distinctFromAggregate := certificate.distinctFromAggregate
    noBackEdge := certificate.noBackEdge
    sameScope := certificate.sameScope
    aggregateDependency := certificate.aggregateDependency
  }

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
  | scopeMismatch (producerScope suffixScope : List RepeatableLevel)
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
  sameScope : suffix.first.placement.targetDeclaration.repeatableScope =
    cascade.row.targetDeclaration.repeatableScope
  aggregateDependency :
    suffix.first.placement.sourceDeclaration.id =
      cascade.total.operation.core.target.id

/-- Compose the two checked phases while retaining their existing finite orders. The suffix stays in the producer's exact row scope, every suffix target is new and absent from the prefix reads, and the first suffix operation consumes the aggregate. -/
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
      let hScope ← certifyRepeatableNumberAggregateSuffixScope cascade
        suffix.first.placement.targetDeclaration.repeatableScope
        |>.mapError fun (producerScope, suffixScope) =>
          .scopeMismatch producerScope suffixScope
      if hDependency : suffix.first.placement.sourceDeclaration.id =
          cascade.total.operation.core.target.id then
        pure {
          cascade, suffix
          distinctTargets := hDistinct
          noBackEdge := hBackEdge
          sameScope := hScope.sameScope
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

/-- One checked aggregate prefix followed by the existing fixed repeatable Number-to-String cascade. Its established direct-Number suffix certificate is reused unchanged, while the typed suffix retains its separately checked String edge. -/
structure CheckedRepeatableNumberAggregateNumberToStringRowChain
    (model : FlatModel) where
  private mk ::
  cascade : CheckedRepeatableNumberAggregateCascade model
  suffix : CheckedCurrentRepetitionNumberToStringCascade model
  distinctFromRows :
    suffix.number.placement.targetField ≠ cascade.row.targetField
  distinctFromAggregate :
    suffix.number.placement.targetField ≠
      cascade.total.operation.core.target.id
  noBackEdge :
    (cascade.row.sourceFields ++ cascade.consumer.fieldDependencies).contains
      suffix.number.placement.targetField = false
  sameScope : suffix.number.placement.targetDeclaration.repeatableScope =
    cascade.row.targetDeclaration.repeatableScope
  aggregateDependency :
    suffix.number.placement.sourceDeclaration.id =
      cascade.total.operation.core.target.id

/-- Reuse the checked direct-Number suffix boundary, including its exact producer-scope certificate, before retaining the suffix's already-checked structural and typed edge. -/
def checkRepeatableNumberAggregateNumberToStringRowChain
    (cascade : CheckedRepeatableNumberAggregateCascade model)
    (suffix : CheckedCurrentRepetitionNumberToStringCascade model) :
    Except RepeatableNumberAggregateRowCascadeElabError
      (CheckedRepeatableNumberAggregateNumberToStringRowChain model) := do
  let certificate ←
    certifyRepeatableNumberAggregateRowSuffix cascade suffix.number
  pure {
    cascade, suffix
    distinctFromRows := certificate.distinctFromRows
    distinctFromAggregate := certificate.distinctFromAggregate
    noBackEdge := certificate.noBackEdge
    sameScope := certificate.sameScope
    aggregateDependency := certificate.aggregateDependency
  }

structure RepeatableNumberAggregateNumberToStringRowChainOutcomes where
  cascade : RepeatableNumberAggregateCascadeOutcomes
  suffix : CurrentRepetitionNumberToStringOutcomes
  deriving Repr, DecidableEq

inductive RepeatableNumberAggregateNumberToStringRowChainFault where
  | cascade (cause : RepeatableNumberAggregateCascadeFault)
  | suffix (cause : CurrentRepetitionNumberToStringFault)
  deriving Repr, DecidableEq

namespace CheckedRepeatableNumberAggregateNumberToStringRowChain

def analyze
    (plan : CheckedRepeatableNumberAggregateNumberToStringRowChain model) :
    RepeatableNumberAggregateRowChainAnalysis := {
  cascade := plan.cascade.analyze
  suffix := plan.suffix.analyze
}

/-- Execute the aggregate prefix, expose its completion only to the first repeatable Number read, and reuse the suffix's exact-row Number-to-String projection. -/
def execute
    (plan : CheckedRepeatableNumberAggregateNumberToStringRowChain model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (world : World) (input : CheckedDocument model) :
    Except RepeatableNumberAggregateNumberToStringRowChainFault
      RepeatableNumberAggregateNumberToStringRowChainOutcomes := do
  let cascade ← plan.cascade.execute world input |>.mapError .cascade
  let suffix ← plan.suffix.executeWithRead patterns input
    (plan.cascade.readCompletion cascade.aggregate.outcome input)
    |>.mapError .suffix
  pure { cascade, suffix }

end CheckedRepeatableNumberAggregateNumberToStringRowChain

private inductive RepeatableNumberAggregatePairRowSuffixElabError where
  | duplicateTarget (field : FieldId)
  | missingAggregateDependency (expected : FieldId)
  | scopeMismatch (producerScope suffixScope : List RepeatableLevel)
  | cycle (field : FieldId)
  deriving Repr, DecidableEq

private structure RepeatableNumberAggregatePairRowSuffixCertificate
    (cascade : CheckedRepeatableNumberAggregateCascade model)
    (pair : CheckedAddressedNumberPair model) : Type where
  distinctFromRows : pair.left.placement.targetField ≠ cascade.row.targetField
  distinctFromAggregate : pair.left.placement.targetField ≠
    cascade.total.operation.core.target.id
  noBackEdge :
    (cascade.row.sourceFields ++ cascade.consumer.fieldDependencies).contains
      pair.left.placement.targetField = false
  sameScope : pair.left.placement.targetDeclaration.repeatableScope =
    cascade.row.targetDeclaration.repeatableScope
  aggregateDependency :
    (pair.left.placement.sourceDeclaration.id ==
        cascade.total.operation.core.target.id ||
      pair.right.placement.sourceDeclaration.id ==
        cascade.total.operation.core.target.id) = true

private def certifyRepeatableNumberAggregatePairRowSuffix
    (cascade : CheckedRepeatableNumberAggregateCascade model)
    (pair : CheckedAddressedNumberPair model) :
    Except RepeatableNumberAggregatePairRowSuffixElabError
      (RepeatableNumberAggregatePairRowSuffixCertificate cascade pair) := do
  let target := pair.left.placement.targetField
  if hRows : target ≠ cascade.row.targetField then
    if hAggregate : target ≠ cascade.total.operation.core.target.id then
      if hBackEdge :
          (cascade.row.sourceFields ++
            cascade.consumer.fieldDependencies).contains target = false then
        let hScope ← certifyRepeatableNumberAggregateSuffixScope cascade
          pair.left.placement.targetDeclaration.repeatableScope
          |>.mapError fun (producerScope, suffixScope) =>
            .scopeMismatch producerScope suffixScope
        if hDependency :
            (pair.left.placement.sourceDeclaration.id ==
                cascade.total.operation.core.target.id ||
              pair.right.placement.sourceDeclaration.id ==
                cascade.total.operation.core.target.id) = true then
          pure {
            distinctFromRows := hRows
            distinctFromAggregate := hAggregate
            noBackEdge := hBackEdge
            sameScope := hScope.sameScope
            aggregateDependency := hDependency
          }
        else throw (.missingAggregateDependency
          cascade.total.operation.core.target.id)
      else throw (.cycle target)
    else throw (.duplicateTarget target)
  else throw (.duplicateTarget target)

inductive RepeatableNumberAggregateBinaryRowCascadeElabError where
  | suffix (cause : AddressedNumberBinaryElabError)
  | duplicateTarget (field : FieldId)
  | missingAggregateDependency (expected : FieldId)
  | scopeMismatch (producerScope suffixScope : List RepeatableLevel)
  | cycle (field : FieldId)
  deriving Repr, DecidableEq

private def pairSuffixErrorToBinary :
    RepeatableNumberAggregatePairRowSuffixElabError →
      RepeatableNumberAggregateBinaryRowCascadeElabError
  | .duplicateTarget field => .duplicateTarget field
  | .missingAggregateDependency expected => .missingAggregateDependency expected
  | .scopeMismatch producerScope suffixScope =>
      .scopeMismatch producerScope suffixScope
  | .cycle field => .cycle field

/-- One checked aggregate prefix followed by one ordered direct-field binary Number operation at every suffix row. -/
structure CheckedRepeatableNumberAggregateBinaryRowCascade
    (model : FlatModel) where
  private mk ::
  cascade : CheckedRepeatableNumberAggregateCascade model
  suffix : CheckedAddressedNumberBinary model
  distinctFromRows :
    suffix.pair.left.placement.targetField ≠ cascade.row.targetField
  distinctFromAggregate :
    suffix.pair.left.placement.targetField ≠
      cascade.total.operation.core.target.id
  noBackEdge :
    (cascade.row.sourceFields ++ cascade.consumer.fieldDependencies).contains
      suffix.pair.left.placement.targetField = false
  sameScope :
    suffix.pair.left.placement.targetDeclaration.repeatableScope =
      cascade.row.targetDeclaration.repeatableScope
  aggregateDependency :
    (suffix.pair.left.placement.sourceDeclaration.id ==
        cascade.total.operation.core.target.id ||
      suffix.pair.right.placement.sourceDeclaration.id ==
        cascade.total.operation.core.target.id) = true

/-- Compose the checked aggregate with an ordered addressed binary suffix in the producer's exact row scope that reads the aggregate on at least one side and owns a later target. -/
def checkRepeatableNumberAggregateBinaryRowCascade
    (cascade : CheckedRepeatableNumberAggregateCascade model)
    (suffixDeclaringGroup : GroupPath) (suffixTarget : FieldId)
    (leftSource rightSource : SurfaceFieldPath)
    (operation : NumericArithmeticOp) :
    Except RepeatableNumberAggregateBinaryRowCascadeElabError
      (CheckedRepeatableNumberAggregateBinaryRowCascade model) := do
  if suffixTarget == cascade.total.operation.core.target.id then
    throw (.duplicateTarget suffixTarget)
  let suffix ← checkAddressedNumberBinary model suffixDeclaringGroup
    suffixTarget leftSource rightSource operation |>.mapError .suffix
  let certificate ← certifyRepeatableNumberAggregatePairRowSuffix cascade suffix.pair
    |>.mapError pairSuffixErrorToBinary
  pure {
    cascade, suffix
    distinctFromRows := certificate.distinctFromRows
    distinctFromAggregate := certificate.distinctFromAggregate
    noBackEdge := certificate.noBackEdge
    sameScope := certificate.sameScope
    aggregateDependency := certificate.aggregateDependency
  }

structure RepeatableNumberAggregateBinaryRowCascadeAnalysis where
  cascade : RepeatableNumberAggregateCascadeAnalysis
  suffixOperation : NumericArithmeticOp
  suffixTarget : FieldId
  repeatableScope : List RepeatableLevel
  fieldDependencies : List (FieldId × List FieldId)
  deriving Repr, DecidableEq

structure RepeatableNumberAggregateBinaryRowCascadeOutcomes where
  cascade : RepeatableNumberAggregateCascadeOutcomes
  suffix : List (SourcedNumericTargetOutcome CellAddr)
  deriving Repr, DecidableEq

inductive RepeatableNumberAggregateBinaryRowCascadeFault where
  | cascade (cause : RepeatableNumberAggregateCascadeFault)
  | suffix (cause : AddressedNumberBinaryFault)
  deriving Repr, DecidableEq

namespace CheckedRepeatableNumberAggregateBinaryRowCascade

def analyze (plan : CheckedRepeatableNumberAggregateBinaryRowCascade model) :
    RepeatableNumberAggregateBinaryRowCascadeAnalysis := {
  cascade := plan.cascade.analyze
  suffixOperation := plan.suffix.op
  suffixTarget := plan.suffix.pair.left.placement.targetField
  repeatableScope :=
    plan.suffix.pair.left.placement.targetDeclaration.repeatableScope
  fieldDependencies := plan.cascade.analyze.fieldDependencies ++ [
    (plan.suffix.pair.left.placement.targetField,
      [plan.suffix.pair.left.placement.sourceDeclaration.id,
        plan.suffix.pair.right.placement.sourceDeclaration.id].eraseDups)]
}

/-- Execute the aggregate prefix, expose its completion only at the exact root address, and preserve the binary suffix's authored operand order at every row. -/
def execute (plan : CheckedRepeatableNumberAggregateBinaryRowCascade model)
    (world : World) (input : CheckedDocument model) :
    Except RepeatableNumberAggregateBinaryRowCascadeFault
      RepeatableNumberAggregateBinaryRowCascadeOutcomes := do
  let cascade ← plan.cascade.execute world input |>.mapError .cascade
  let suffix ← plan.suffix.executeWithRead input
    (plan.cascade.readCompletion cascade.aggregate.outcome input)
    |>.mapError .suffix
  pure { cascade, suffix }

end CheckedRepeatableNumberAggregateBinaryRowCascade

inductive RepeatableNumberAggregateDivisionRowCascadeElabError where
  | suffix (cause : AddressedNumberDivisionElabError)
  | duplicateTarget (field : FieldId)
  | missingAggregateDependency (expected : FieldId)
  | scopeMismatch (producerScope suffixScope : List RepeatableLevel)
  | cycle (field : FieldId)
  deriving Repr, DecidableEq

private def pairSuffixErrorToDivision :
    RepeatableNumberAggregatePairRowSuffixElabError →
      RepeatableNumberAggregateDivisionRowCascadeElabError
  | .duplicateTarget field => .duplicateTarget field
  | .missingAggregateDependency expected => .missingAggregateDependency expected
  | .scopeMismatch producerScope suffixScope =>
      .scopeMismatch producerScope suffixScope
  | .cycle field => .cycle field

/-- One checked aggregate prefix followed by one ordered direct-field division at every repeatable suffix row. -/
structure CheckedRepeatableNumberAggregateDivisionRowCascade
    (model : FlatModel) where
  private mk ::
  cascade : CheckedRepeatableNumberAggregateCascade model
  suffix : CheckedAddressedNumberDivision model
  distinctFromRows :
    suffix.pair.left.placement.targetField ≠ cascade.row.targetField
  distinctFromAggregate :
    suffix.pair.left.placement.targetField ≠
      cascade.total.operation.core.target.id
  noBackEdge :
    (cascade.row.sourceFields ++ cascade.consumer.fieldDependencies).contains
      suffix.pair.left.placement.targetField = false
  sameScope :
    suffix.pair.left.placement.targetDeclaration.repeatableScope =
      cascade.row.targetDeclaration.repeatableScope
  aggregateDependency :
    (suffix.pair.left.placement.sourceDeclaration.id ==
        cascade.total.operation.core.target.id ||
      suffix.pair.right.placement.sourceDeclaration.id ==
        cascade.total.operation.core.target.id) = true

/-- Compose the checked aggregate with a warning-suppressed addressed division in the producer's exact row scope that reads the aggregate on at least one side and owns a later target. -/
def checkRepeatableNumberAggregateDivisionRowCascade
    (cascade : CheckedRepeatableNumberAggregateCascade model)
    (suffixDeclaringGroup : GroupPath) (suffixTarget : FieldId)
    (leftSource rightSource : SurfaceFieldPath)
    (suppressExactScaleWarning : Bool) :
    Except RepeatableNumberAggregateDivisionRowCascadeElabError
      (CheckedRepeatableNumberAggregateDivisionRowCascade model) := do
  if suffixTarget == cascade.total.operation.core.target.id then
    throw (.duplicateTarget suffixTarget)
  let suffix ← checkAddressedNumberDivision model suffixDeclaringGroup
    suffixTarget leftSource rightSource suppressExactScaleWarning
      |>.mapError .suffix
  let certificate ← certifyRepeatableNumberAggregatePairRowSuffix cascade suffix.pair
    |>.mapError pairSuffixErrorToDivision
  pure {
    cascade, suffix
    distinctFromRows := certificate.distinctFromRows
    distinctFromAggregate := certificate.distinctFromAggregate
    noBackEdge := certificate.noBackEdge
    sameScope := certificate.sameScope
    aggregateDependency := certificate.aggregateDependency
  }

structure RepeatableNumberAggregateDivisionRowCascadeAnalysis where
  cascade : RepeatableNumberAggregateCascadeAnalysis
  suffixScaleWarningSuppressed : Bool
  suffixTarget : FieldId
  repeatableScope : List RepeatableLevel
  fieldDependencies : List (FieldId × List FieldId)
  deriving Repr, DecidableEq

structure RepeatableNumberAggregateDivisionRowCascadeOutcomes where
  cascade : RepeatableNumberAggregateCascadeOutcomes
  suffix : List (SourcedNumericTargetOutcome CellAddr)
  deriving Repr, DecidableEq

inductive RepeatableNumberAggregateDivisionRowCascadeFault where
  | cascade (cause : RepeatableNumberAggregateCascadeFault)
  | suffix (cause : AddressedNumberDivisionFault)
  deriving Repr, DecidableEq

namespace CheckedRepeatableNumberAggregateDivisionRowCascade

def analyze (plan : CheckedRepeatableNumberAggregateDivisionRowCascade model) :
    RepeatableNumberAggregateDivisionRowCascadeAnalysis := {
  cascade := plan.cascade.analyze
  suffixScaleWarningSuppressed := plan.suffix.suppressExactScaleWarning
  suffixTarget := plan.suffix.pair.left.placement.targetField
  repeatableScope :=
    plan.suffix.pair.left.placement.targetDeclaration.repeatableScope
  fieldDependencies := plan.cascade.analyze.fieldDependencies ++ [
    (plan.suffix.pair.left.placement.targetField,
      [plan.suffix.pair.left.placement.sourceDeclaration.id,
        plan.suffix.pair.right.placement.sourceDeclaration.id].eraseDups)]
}

/-- Execute the aggregate prefix, expose its completion only at the exact root address, and preserve the division suffix's authored operand order and warning-suppressed target check. -/
def execute (plan : CheckedRepeatableNumberAggregateDivisionRowCascade model)
    (world : World) (input : CheckedDocument model) :
    Except RepeatableNumberAggregateDivisionRowCascadeFault
      RepeatableNumberAggregateDivisionRowCascadeOutcomes := do
  let cascade ← plan.cascade.execute world input |>.mapError .cascade
  let suffix ← plan.suffix.executeWithRead input
    (plan.cascade.readCompletion cascade.aggregate.outcome input)
    |>.mapError .suffix
  pure { cascade, suffix }

end CheckedRepeatableNumberAggregateDivisionRowCascade

end A12Kernel
