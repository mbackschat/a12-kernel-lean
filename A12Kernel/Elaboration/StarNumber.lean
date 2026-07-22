import A12Kernel.Elaboration.Correlation
import A12Kernel.Elaboration.StarPath

/-! # Checked nested Number-star consumption -/

namespace A12Kernel

inductive StarNumberElabError where
  | path (error : StarPathElabError)
  | fieldNotNumber (path : List String)
  | having (error : CorrelationElabError)
  deriving Repr, DecidableEq

/-- One general starred field path whose exact model declaration is Number-valued. -/
structure CheckedStarNumberSource (model : FlatModel) where
  source : CheckedStarFieldPath model
  field : FlatNumberField
  fieldOwned : source.declaration.toNumberField? = some field

/-- One checked nested Number star paired with a checked filter over the exact candidate and captured repetition environments available at its authoring site. -/
structure CheckedStarNumberHavingSource (model : FlatModel) where
  source : CheckedStarNumberSource model
  declaringGroup : GroupPath
  filter : CheckedStarHaving model source.source declaringGroup

def CheckedStarNumberHavingSource.having
    (checked : CheckedStarNumberHavingSource model) : CorrelatedHaving :=
  checked.filter.condition

def CheckedStarNumberHavingSource.outerLevels
    (checked : CheckedStarNumberHavingSource model) : List RepeatableLevel :=
  model.repeatableScopeForGroupPath checked.declaringGroup

/-- A checked all-rows Number-star source is either unavailable to partial validation as a whole or carries the ordinary resolved side unchanged. This is deliberately not the order-aware `FirstFilledValue` relevance result. -/
inductive AllRowsValidationStarNumberSide where
  | nonRelevant
  | relevant (side : ResolvedValueListSide .number)

/-- Reuse general checked star-path lowering, then retain the declaration's exact Number metadata. -/
def elaborateStarNumberSource (model : FlatModel) (declaringGroup : GroupPath)
    (authored : SurfaceStarFieldPath) :
    Except StarNumberElabError (CheckedStarNumberSource model) := do
  let source ← elaborateStarFieldPath model declaringGroup authored |>.mapError .path
  match hField : source.declaration.toNumberField? with
  | none => throw (.fieldNotNumber source.declaration.path)
  | some field => pure { source, field, fieldOwned := hField }

/-- Resolve one general Number star and the narrow source-closed filter fragment against the same model-owned candidate/captured environment split. -/
def elaborateStarNumberHavingSource (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceStarFieldPath)
    (having : SurfaceCorrelatedHaving) :
    Except StarNumberElabError (CheckedStarNumberHavingSource model) := do
  let source ← elaborateStarNumberSource model declaringGroup authored
  let filter ← elaborateStarHavingCore model declaringGroup source.source having
    |>.mapError .having
  pure { source, declaringGroup, filter }

namespace CheckedStarNumberSource

private def bindingOverLimit (axis : StarAxis)
    (binding : RepeatableLevel × Nat) : Bool :=
  axis.level == binding.1 && match axis.repeatability with
    | none => false
    | some limit => binding.2 > limit

/-- Whether one topology-produced leaf environment lies under any over-capacity repeatable ancestor. -/
def environmentOverLimit (checked : CheckedStarNumberSource model)
    (environment : Env) : Bool :=
  (checked.source.path.axes.zip environment).any fun binding =>
    bindingOverLimit binding.1 binding.2

/-- Apply declaration-owned scalar checking unless structural over-repetition suppresses ordinary checks and becomes the sole formal cause. -/
def checkedCell (checked : CheckedStarNumberSource model)
    (read : Env → FieldId → RawCell) (environment : Env) : CheckedCell :=
  let scalar := checked.source.declaration.checkRaw (read environment checked.field.id)
  if checked.environmentOverLimit environment then
    { scalar with parsed := none, findings := [.overRepetition] }
  else
    scalar

/-- Classify one resolved leaf through the existing checked Number value-list reader. -/
def valueListCell (checked : CheckedStarNumberSource model)
    (read : Env → FieldId → RawCell) (environment : Env) : ValueListCell .number :=
  let context : FlatContext := {
    read := fun id =>
      if id == checked.field.id then checked.checkedCell read environment
      else malformedCheckedCell }
  checked.field.valueListCell context

/-- Apply one resolved validation `Having` to topology-produced leaves before classifying any selected target cell. The filter reads validation-checked cells from candidate/outer environments; the target read remains a separate declaration-owned raw channel. -/
def selectedValidationHavingValueSide (checked : CheckedStarNumberSource model)
    (resolved : ResolvedStarTopology) (having : CorrelatedHaving)
    (filterRead : Env → FieldId → CheckedCell) (outer : Env)
    (read : Env → FieldId → RawCell) : ResolvedValueListSide .number :=
  let filterContext : CorrelationContext := { read := filterRead }
  let selected := having.selectEnvironments filterContext outer resolved.environments
  { cells := selected.map (checked.valueListCell read)
    hasUninstantiatedTail := resolved.domain.hasOpenTail
    hasHaving := true }

/-- Resolve nested rows once and classify every canonical leaf through the declaration-owned Number boundary. -/
def resolvedValueSide (checked : CheckedStarNumberSource model)
    (document : Document) (outer : Env) (read : Env → FieldId → RawCell) :
    Except StarAddressingError (ResolvedValueListSide .number) := do
  let resolved ← checked.source.path.resolve document outer
  pure (resolved.toResolvedSide (checked.valueListCell read))

/-- Apply the full/partial all-rows relevance gate to one already-resolved topology. A nonrelevant source is rejected before any selected target cell is classified; relevance leaves cells and hierarchical omitted-tail state unchanged. -/
def selectedPartialAllRowsValueSide (checked : CheckedStarNumberSource model)
    (resolved : ResolvedStarTopology) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → RawCell) : AllRowsValidationStarNumberSide :=
  if checked.source.allRowsRelevant scope then
    .relevant (resolved.toResolvedSide (checked.valueListCell read))
  else
    .nonRelevant

/-- Resolve the nested topology once, then apply the all-rows validation relevance gate without pruning candidate identities or changing cell classification. -/
def resolvedPartialAllRowsValueSide (checked : CheckedStarNumberSource model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → RawCell) :
    Except StarAddressingError AllRowsValidationStarNumberSide := do
  let resolved ← checked.source.path.resolve document outer
  pure (checked.selectedPartialAllRowsValueSide resolved scope read)

/-- Resolve general nested topology once, evaluate the validation `Having` over every candidate environment with the complete captured outer environment, then read only selected Number targets. -/
def resolvedValidationHavingValueSide (checked : CheckedStarNumberSource model)
    (document : Document) (outer : Env) (having : CorrelatedHaving)
    (filterRead : Env → FieldId → CheckedCell)
    (read : Env → FieldId → RawCell) :
    Except StarAddressingError (ResolvedValueListSide .number) := do
  let resolved ← checked.source.path.resolve document outer
  pure (checked.selectedValidationHavingValueSide resolved having filterRead outer read)

end CheckedStarNumberSource

namespace CheckedStarNumberHavingSource

/-- Resolve topology, apply the checked filter with separate complete candidate/captured environments, and classify only retained Number targets. -/
def resolvedValueSide (checked : CheckedStarNumberHavingSource model)
    (document : Document) (outer : Env)
    (filterRead : Env → FieldId → CheckedCell)
    (read : Env → FieldId → RawCell) :
    Except StarAddressingError (ResolvedValueListSide .number) :=
  checked.source.resolvedValidationHavingValueSide document outer checked.having
    filterRead read

end CheckedStarNumberHavingSource

end A12Kernel
