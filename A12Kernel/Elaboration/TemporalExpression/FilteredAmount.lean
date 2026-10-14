import A12Kernel.Elaboration.DistinctCountSource
import A12Kernel.Elaboration.TokenDistinctCount
import A12Kernel.Elaboration.FieldFillList
import A12Kernel.Elaboration.TokenValueCount
import A12Kernel.Elaboration.BooleanValueCount

/-! # Filtered shift amounts

A shift amount may read a filtered entity list, which the Kernel admits wherever the ordinary
numeric grammar does (`docs/sources/temporal-runtime-fold-probes.md#src-expanded-shift-amounts`).
The Having atom family cannot carry that filter: a filter is itself built from Having atoms. The
amount therefore retains the ordinary filtered carriers unchanged, so their elaboration, filter
semantics, references and omission responsibility stay with their existing owners. Only a route
holding the checked document can evaluate them; it supplies that evaluation to the temporal
evaluator.
-/

namespace A12Kernel

/-- The authored entity-list operators of a filtered shift amount, in the ordinary surface shapes. -/
inductive SurfaceFilteredShiftAmount where
  | aggregate (op : NumericAggregateOp) (source : SurfaceNumberEntitySource)
  | firstFilled (source : SurfaceNumberEntitySource)
  | valueCount (expected : Rat) (source : SurfaceNumberEntitySource)
  | tokenValueCount (expected : String) (source : SurfaceTokenValueCountSource)
  | tokenEntityValueCount (expected : String) (source : SurfaceTokenEntitySource)
  | booleanValueCount (expected : Bool) (source : SurfaceBooleanValueCountSource)
  | filledFieldCount (source : SurfaceFieldEntitySource)

/-- One arm per ordinary checked carrier; each corresponds to exactly one ordered numeric atom. -/
inductive CheckedFilteredShiftAmount (model : FlatModel) where
  | aggregate (op : NumericAggregateOp) (source : CheckedNumberEntitySource model)
  | firstFilled (source : CheckedNumberEntitySource model)
  | valueCount (expected : Rat) (source : CheckedNumberEntitySource model)
  | tokenValueCount (source : CheckedTokenValueCountSource model)
  | booleanValueCount (source : CheckedBooleanValueCountSource model)
  | tokenDistinctCount (source : CheckedTokenEntitySource model)
  | temporalDistinctCount (run : CheckedTemporalDistinctCountRun model)
  | filledFieldCount (source : CheckedFieldFillList model)

inductive FilteredShiftAmountElabError where
  | number (error : NumberEntityElabError)
  | fieldFill (error : FieldFillListElabError)
  | tokenValueCount (error : TokenValueCountElabError)
  | booleanValueCount (error : BooleanValueCountElabError)
  /-- A carrier binds a repeatable level the amount's row does not. -/
  | unbound
  deriving Repr, DecidableEq

namespace CheckedFilteredShiftAmount

def bindingScopes : CheckedFilteredShiftAmount model → List (List RepeatableLevel)
  | .aggregate _ source | .firstFilled source | .valueCount _ source => source.bindingScopes
  | .tokenValueCount source => source.source.bindingScopes
  | .booleanValueCount source => source.bindingScopes
  | .tokenDistinctCount source => source.bindingScopes
  | .temporalDistinctCount run => run.source.bindingScopes
  | .filledFieldCount source => source.operands.flatMap (·.bindingScopes)

/-- `filterReads` selects which filter-body reads count, as each carrier's own query does. -/
def referencesWith (source : CheckedFilteredShiftAmount model) (field : FieldId)
    (filterReads : CorrelatedHaving → FieldId → Bool) : Bool :=
  match source with
  | .aggregate _ source | .firstFilled source | .valueCount _ source => source.referencesField field filterReads
  | .tokenValueCount source => source.referencesField field filterReads
  | .booleanValueCount source => source.referencesField field filterReads
  | .tokenDistinctCount source => source.referencesField field filterReads
  | .temporalDistinctCount run => run.source.referencesField field filterReads
  | .filledFieldCount source => source.referencesField field filterReads

def referencesField (source : CheckedFilteredShiftAmount model) (field : FieldId) : Bool :=
  source.referencesWith field (·.referencesField)

def fieldIds (source : CheckedFilteredShiftAmount model) : List FieldId :=
  (model.fields.filter fun declaration => source.referencesField declaration.id).map (·.id)

def summary : CheckedFilteredShiftAmount model → NumericScaleSummary
  | .aggregate op source => source.aggregateScaleSummary op
  | .firstFilled source => source.scaleSummary
  | .tokenValueCount source => source.scaleSummary
  | .booleanValueCount source => source.scaleSummary
  | .tokenDistinctCount source => source.distinctScaleSummary
  | .valueCount _ _ | .temporalDistinctCount _ | .filledFieldCount _ => NumericScaleSummary.field 0

/-- Upward counts own the omission responsibility of their filter reads (spec/10 §4.1). -/
def isCount : CheckedFilteredShiftAmount model → Bool
  | .aggregate .distinctCount _ | .tokenDistinctCount _ | .temporalDistinctCount _
  | .filledFieldCount _ => true
  | _ => false

end CheckedFilteredShiftAmount

/-- Elaborate at the rule or target group whose row the amount binds, as the ordinary numeric
comparison does for the same carriers. -/
def elaborateFilteredShiftAmount (model : FlatModel) (rowGroup bindingGroup : GroupPath) :
    SurfaceFilteredShiftAmount → Except FilteredShiftAmountElabError (CheckedFilteredShiftAmount model)
  | .aggregate .distinctCount source => do
      match ← (elaborateDistinctCountSource model rowGroup source (bindingGroup? := some bindingGroup)).mapError .number with
      | .number checked => pure (.aggregate .distinctCount checked)
      | .token checked => pure (.tokenDistinctCount checked)
      | .temporal run => pure (.temporalDistinctCount run)
  | .aggregate op source =>
      (elaborateNumberEntitySource model rowGroup source (writtenGroup := bindingGroup)
        (bindingGroup? := some bindingGroup)).map (.aggregate op) |>.mapError .number
  | .firstFilled source =>
      (elaborateNumberEntitySource model rowGroup source (writtenGroup := bindingGroup)
        (bindingGroup? := some bindingGroup)).map .firstFilled |>.mapError .number
  | .valueCount expected source =>
      (elaborateNumberEntitySource model rowGroup source (writtenGroup := bindingGroup)
        (bindingGroup? := some bindingGroup)).map (.valueCount expected) |>.mapError .number
  | .tokenValueCount expected source =>
      (elaborateTokenValueCountSource model rowGroup expected source (writtenGroup := bindingGroup)
        (bindingGroup? := some bindingGroup)).map .tokenValueCount |>.mapError .tokenValueCount
  | .tokenEntityValueCount expected source =>
      (elaborateTokenEntityValueCountSource model rowGroup expected source (writtenGroup := bindingGroup)
        (bindingGroup? := some bindingGroup)).map .tokenValueCount |>.mapError .tokenValueCount
  | .booleanValueCount expected source =>
      (elaborateBooleanValueCountSource model rowGroup expected source (writtenGroup := bindingGroup)
        (bindingGroup? := some bindingGroup)).map .booleanValueCount |>.mapError .booleanValueCount
  | .filledFieldCount source => do
      let checked ← (elaborateFieldFillList model rowGroup source bindingGroup).mapError .fieldFill
      if !checked.rowBoundBool (model.repeatableScopeForGroupPath bindingGroup) then throw .unbound
      pure (.filledFieldCount checked)

end A12Kernel
