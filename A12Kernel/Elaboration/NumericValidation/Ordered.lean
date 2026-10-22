import A12Kernel.Elaboration.NumericValidation.Core
import A12Kernel.Elaboration.IndexedStringNumeric
import A12Kernel.Elaboration.TemporalNumericExpression
import A12Kernel.Elaboration.FieldFillList
import A12Kernel.Elaboration.TokenDistinctCount
import A12Kernel.Elaboration.TemporalDistinctCount

/-! # Checked ordered numeric validation

This module owns the model-indexed numeric leaves used by addressed and generated validation. It retains checked entity-list and row-product sources without widening the scalar syntax in `NumericValidation.Core`.
-/

namespace A12Kernel

/-- A numeric leaf either delegates one established scalar atom unchanged or retains a model-certified first-filled, aggregate, or row-product source for full addressed validation. -/
inductive OrderedNumericValidationAtom (model : FlatModel) where
  | indexed (source : CheckedNumericSemanticIndexSource model)
  | indexedString (source : CheckedIndexedStringNumericSource model)
  | temporalExpression (source : CheckedTemporalNumericExpression model)
  | ordinary (source : NumericValidationAtom)
  | firstFilled (source : CheckedNumberEntitySource model)
  | valueCount (expected : Rat) (source : CheckedNumberEntitySource model)
  | tokenValueCount (source : CheckedTokenValueCountSource model)
  | booleanValueCount (source : CheckedBooleanValueCountSource model)
  | aggregate (op : NumericAggregateOp)
      (source : CheckedNumberEntitySource model)
  | sumOfProducts (source : CheckedNumericProductAggregate model)
  /-- A filled-group count whose operand list carries at least one star. The fixed-only list stays
  on the established scalar atom, so widening this operator costs the already-measured form nothing.
  A starred member contributes its in-capacity instantiated row count, which needs document row
  topology, so this arm resolves only on the addressed route. -/
  | filledGroupCountMixed (operands : List (CheckedGroupCountOperand model))
  /-- `NumberOfFilledFields` over a field-fill list, read on the addressed route because a starred or
  group operand's checked extent needs the document's row topology. -/
  | filledFieldCount (source : CheckedFieldFillList model)
  /-- `NumberOfDifferentValues` over a String/Enumeration entity list, the token half of the
  operator a Number list owns through `aggregate .distinctCount`. -/
  | tokenDistinctCount (source : CheckedTokenEntitySource model)
  /-- `NumberOfDifferentValues` over a temporal entity list sharing one component set, admitted
  only where the temporal fold has an evaluator. -/
  | temporalDistinctCount (run : CheckedTemporalDistinctCountRun model)

/-- One model-indexed numeric comparison whose atom resolver, rather than the containing leaf, owns relevance timing and addressed-source selection. -/
abbrev OrderedNumericComparison (model : FlatModel) :=
  NumericComparisonOf (OrderedNumericValidationAtom model)

namespace OrderedNumericValidationAtom

@[simp]
def addressedNumericValidationFieldIds :
    NumericValidationAtom → List FieldId
  | .field source => [source.id]
  | .temporalFieldPart source _ _ => [source.id]
  | .dateRangeBoundPart source _ _ => [source.id]
  | .stringLength source => [source.id]
  | .stringRange source _ _ => [source.id]
  | .fieldValueAsNumber source => [source.fieldId]
  | .dateDifference _ left right => ((left.fields ++ right.fields).map (·.id)).eraseDups
  | .dayDifference _ left right => ((left.fields ++ right.fields).map (·.id)).eraseDups
  | .dateTimeDifference _ left right =>
      ((left.fields ++ right.fields).map FlatField.id).eraseDups
  | _ => []

private def checkedNumberEntitySourceAdmittedIn
    (source : CheckedNumberEntitySource model)
    (rowGroup : GroupPath) (scope : NumericOperandScope) : Bool :=
  match scope with
  | .modelWideCheckedComputation => true
  | .sameGroupAddressed => source.bindingScopes.all (·.isPrefixOf (model.repeatableScopeForGroupPath rowGroup))
  | .sameGroup | .modelWideNonrepeatable =>
      match source.directResolvedFields? with
      | none => false
      | some direct =>
          direct.hasMultipleFields && direct.hasUniqueFields &&
            direct.fields.all fun field =>
              match scope with
              | .sameGroup => model.admitsNumberInGroup rowGroup field
              | .sameGroupAddressed => false
              | .modelWideNonrepeatable => model.admitsNumberModelWide field
              | .modelWideCheckedComputation => true

private def checkedTokenValueCountAdmittedIn
    (source : CheckedTokenValueCountSource model)
    (rowGroup : GroupPath) (scope : NumericOperandScope) : Bool :=
  match scope with
  | .modelWideCheckedComputation => true
  | .sameGroupAddressed => source.source.bindingScopes.all (·.isPrefixOf (model.repeatableScopeForGroupPath rowGroup))
  | .sameGroup | .modelWideNonrepeatable =>
      match source.source.directFields? with
      | none => false
      | some direct =>
          direct.all fun field =>
            match scope with
            | .sameGroup => field.declaration.groupPath == rowGroup
            | .sameGroupAddressed => false
            | .modelWideNonrepeatable => true
            | .modelWideCheckedComputation => true

def summary : OrderedNumericValidationAtom model → NumericScaleSummary
  | .indexed source => NumericScaleSummary.field source.field.info.scale
  | .indexedString source => NumericScaleSummary.field source.projection.scale
  | .temporalExpression _ => NumericScaleSummary.field 0
  | .ordinary source => numericValidationSummary source
  | .firstFilled source => source.scaleSummary
  | .valueCount _ _ => NumericScaleSummary.field 0
  | .tokenValueCount source => source.scaleSummary
  | .booleanValueCount source => source.scaleSummary
  | .aggregate op source => source.aggregateScaleSummary op
  | .sumOfProducts source => source.scaleSummary
  | .filledGroupCountMixed _ | .filledFieldCount _ => NumericScaleSummary.field 0
  | .tokenDistinctCount source => source.distinctScaleSummary
  | .temporalDistinctCount _ => NumericScaleSummary.field 0

/-- Structural coordinates and group counts retain their binding requirements independently of
    field dependencies. Field-backed atoms require addressing when a checked declaration repeats. -/
def requiresAddressedValidation : OrderedNumericValidationAtom model → Bool
  | .indexed _ | .indexedString _ => true
  | .temporalExpression source => source.requiresAddressed || source.fieldIds.any fun field =>
      (model.lookupUniqueId field).toOption.any (fun declaration => !declaration.repeatableScope.isEmpty)
  | .ordinary (.boundCurrentRepetition _) => true
  | .ordinary (.filledGroupCount groups) =>
      groups.any fun reference => !reference.boundRepeatableScope.isEmpty
  | .ordinary source =>
      (addressedNumericValidationFieldIds source).any fun field =>
          match model.lookupUniqueId field with
          | .ok declaration => !declaration.repeatableScope.isEmpty
          | .error _ => false
  | .firstFilled source => source.directResolvedFields?.isNone || source.bindingScopes.any (!·.isEmpty)
  | .valueCount _ source => source.directResolvedFields?.isNone || source.bindingScopes.any (!·.isEmpty)
  | .tokenValueCount source => source.source.directFields?.isNone || source.source.bindingScopes.any (!·.isEmpty)
  | .booleanValueCount source => source.directFields?.isNone
  | .aggregate _ _ | .sumOfProducts _ => true
  | .filledGroupCountMixed _ | .filledFieldCount _ | .tokenDistinctCount _
  | .temporalDistinctCount _ => true

def admitted (atom : OrderedNumericValidationAtom model)
    (rowGroup : GroupPath)
    (scope : NumericOperandScope) : Bool :=
  let bound (scopes : List (List RepeatableLevel)) := scopes.all fun required =>
    match scope with
    | .sameGroupAddressed | .modelWideCheckedComputation =>
        required.isPrefixOf (model.repeatableScopeForGroupPath rowGroup)
    | .sameGroup | .modelWideNonrepeatable => required.isEmpty
  match atom with
  | .indexed source => (scope == .sameGroupAddressed || scope == .modelWideCheckedComputation) &&
      bound source.toCheckedSemanticIndexSource.bindingScopes
  | .indexedString source =>
      (scope == .modelWideCheckedComputation || scope == .sameGroupAddressed) &&
        bound source.selection.bindingScopes
  | .temporalExpression source => bound source.bindingScopes && source.boundFieldIds.all fun field =>
      (model.lookupUniqueId field).toOption.any fun declaration => match scope with
        | .sameGroup => declaration.groupPath == rowGroup && declaration.repeatableScope.isEmpty
        | .sameGroupAddressed => declaration.repeatableScope.isPrefixOf (model.repeatableScopeForGroupPath rowGroup)
        | .modelWideNonrepeatable => declaration.repeatableScope.isEmpty
        | .modelWideCheckedComputation => true
  | .ordinary source => source.admitted model rowGroup scope
  | .firstFilled source => bound source.bindingScopes &&
      match scope with
      | .sameGroupAddressed => true
      | _ => checkedNumberEntitySourceAdmittedIn source rowGroup scope
  | .valueCount _ source => bound source.bindingScopes &&
      checkedNumberEntitySourceAdmittedIn source rowGroup scope
  | .tokenValueCount source => bound source.source.bindingScopes &&
      checkedTokenValueCountAdmittedIn source rowGroup scope
  | .booleanValueCount source => bound source.bindingScopes &&
      match scope with
      | .sameGroup =>
          match source.directFields? with
          | some fields => fields.all fun field => field.groupPath == rowGroup
          | none => false
      | .sameGroupAddressed => source.directFields?.isNone
      | .modelWideNonrepeatable => source.directFields?.isSome
      | .modelWideCheckedComputation => true
  -- A direct list of fixed fields keeps its scalar owner. One naming a row field is admitted here and
  -- its slots read at the rule's row, whose runtime is `external evidence pending`.
  | .aggregate _ source => bound source.bindingScopes &&
      (scope == .modelWideCheckedComputation || scope == .sameGroupAddressed) &&
        (source.directAggregateFields?.isNone || source.bindingScopes.any (!·.isEmpty))
  | .sumOfProducts source => bound source.bindingScopes &&
      (scope == .modelWideCheckedComputation || scope == .sameGroupAddressed)
  | .filledGroupCountMixed operands =>
      (scope == .modelWideCheckedComputation || scope == .sameGroupAddressed) &&
        CheckedGroupCountOperand.admittedArity operands &&
        !operands.any CheckedGroupCountOperand.isRoot
  | .filledFieldCount source =>
      (scope == .modelWideCheckedComputation || scope == .sameGroupAddressed) &&
        source.rowBoundBool (model.repeatableScopeForGroupPath rowGroup)
  | .tokenDistinctCount source => bound source.bindingScopes &&
      (scope == .modelWideCheckedComputation || scope == .sameGroupAddressed)
  | .temporalDistinctCount run => bound run.source.bindingScopes &&
      (scope == .modelWideCheckedComputation || scope == .sameGroupAddressed)

def referencesField (atom : OrderedNumericValidationAtom model)
    (field : FieldId) : Bool :=
  match atom with
  | .indexed source => source.toCheckedSemanticIndexSource.referencesField field
  | .indexedString source => source.referencesField field
  | .temporalExpression source => source.referencesField field
  | .ordinary source => source.referencesField model field
  | .firstFilled source => source.referencesField field
  | .valueCount _ source => source.referencesField field
  | .tokenValueCount source => source.referencesField field
  | .booleanValueCount source => source.referencesField field
  | .aggregate _ source => source.referencesField field
  | .sumOfProducts source =>
      source.referencesField field
  | .filledGroupCountMixed operands =>
      operands.any fun operand => operand.referencesField model field
  | .filledFieldCount source => source.referencesField field
  | .tokenDistinctCount source => source.referencesField field
  | .temporalDistinctCount run => run.source.referencesField field

/-- Whether this atom reaches `field` for the rule's error-field gates: as `referencesField` does,
    except that a filter's unmarked reads do not count. The Kernel's gates keep only the references
    outside every filter body and the `$`-marked ones inside
    ([inbound](../../../docs/sources/inbound-handbacks.md#inbound-2026-09-26d-reference-set)). -/
def referencesErrorField (atom : OrderedNumericValidationAtom model)
    (field : FieldId) : Bool :=
  match atom with
  | .firstFilled source | .valueCount _ source | .aggregate _ source =>
      source.referencesField field (CorrelatedHaving.referencesMarkedEntityField model)
  | .tokenValueCount source => source.referencesField field (CorrelatedHaving.referencesMarkedEntityField model)
  | .booleanValueCount source =>
      source.referencesField field (CorrelatedHaving.referencesMarkedEntityField model)
  | .tokenDistinctCount source => source.referencesField field (CorrelatedHaving.referencesMarkedEntityField model)
  | .temporalDistinctCount run =>
      run.source.referencesField field (CorrelatedHaving.referencesMarkedEntityField model)
  | .filledFieldCount source => source.referencesField field (CorrelatedHaving.referencesMarkedEntityField model)
  | .temporalExpression source => source.referencesWith field (fun condition => CorrelatedHaving.referencesMarkedEntityField model condition field)
  | .indexed _ | .indexedString _ | .ordinary _ | .sumOfProducts _ | .filledGroupCountMixed _ =>
      atom.referencesField field

/-- Whether this exact checked atom retains any filtered entity-list slot. This is static source structure, not a statement about which runtime branch or candidate will be reached. -/
def hasHaving : OrderedNumericValidationAtom model → Bool
  | .firstFilled source | .valueCount _ source | .aggregate _ source =>
      source.hasHaving
  | .tokenValueCount source => source.source.hasHaving
  | .booleanValueCount source => source.hasHaving
  | .tokenDistinctCount source => source.hasHaving
  | .temporalDistinctCount run => run.source.hasHaving
  | .filledFieldCount source => source.hasHaving
  | .temporalExpression source => source.hasHaving
  | .indexed _ | .indexedString _ | .ordinary _ | .sumOfProducts _ | .filledGroupCountMixed _ => false

/-- Each filtered shift amount is exactly one ordered atom, so the ordinary carriers' evaluation,
references and omission responsibility serve it unchanged. -/
def ofFiltered : CheckedFilteredShiftAmount model → OrderedNumericValidationAtom model
  | .aggregate op source => .aggregate op source
  | .firstFilled source => .firstFilled source
  | .valueCount expected source => .valueCount expected source
  | .tokenValueCount source => .tokenValueCount source
  | .booleanValueCount source => .booleanValueCount source
  | .tokenDistinctCount source => .tokenDistinctCount source
  | .temporalDistinctCount run => .temporalDistinctCount run
  | .filledFieldCount source => .filledFieldCount source

/-- The temporal dependency traversal reads a filtered amount's own projections; they must agree
with the ordered atom the evaluator and the reference projection use. -/
theorem ofFiltered_referencesField (source : CheckedFilteredShiftAmount model) (field : FieldId) :
    (ofFiltered source).referencesField field = source.referencesField field := by
  cases source <;> rfl

theorem ofFiltered_summary (source : CheckedFilteredShiftAmount model) :
    (ofFiltered source).summary = source.summary := by
  cases source <;> rfl

end OrderedNumericValidationAtom

/-- Static admission for the relevance-aware numeric leaf reuses the complete authored-operation checks and delegates only atom-specific model coherence. -/
def OrderedNumericComparison.wellFormedInBool
    (comparison : OrderedNumericComparison model)
    (rowGroup : GroupPath)
    (scope : NumericOperandScope) : Bool :=
  comparison.admittedWith (·.admitted rowGroup scope) OrderedNumericValidationAtom.summary

def OrderedNumericComparison.referencesField
    (comparison : OrderedNumericComparison model)
    (field : FieldId) : Bool :=
  comparison.left.anyAtom (·.referencesField field) ||
    comparison.right.anyAtom (·.referencesField field)

/-- The error-field reference over both operands, `OrderedNumericValidationAtom.referencesErrorField`
    at every atom. -/
def OrderedNumericComparison.referencesErrorField
    (comparison : OrderedNumericComparison model)
    (field : FieldId) : Bool :=
  comparison.left.anyAtom (·.referencesErrorField field) ||
    comparison.right.anyAtom (·.referencesErrorField field)

/-- Discover `Having` across both complete authored operands without evaluating or lowering away their expression shape. -/
def OrderedNumericComparison.hasHaving
    (comparison : OrderedNumericComparison model) : Bool :=
  comparison.left.anyAtom OrderedNumericValidationAtom.hasHaving ||
    comparison.right.anyAtom OrderedNumericValidationAtom.hasHaving

def OrderedNumericComparison.requiresAddressedValidation
    (comparison : OrderedNumericComparison model) : Bool :=
  comparison.left.anyAtom OrderedNumericValidationAtom.requiresAddressedValidation ||
    comparison.right.anyAtom OrderedNumericValidationAtom.requiresAddressedValidation

/-- Whether the rule must retain temporal runtime effects while evaluating its numeric leaves. -/
def OrderedNumericComparison.hasTemporalExpression (comparison : OrderedNumericComparison model) : Bool :=
  let temporal : OrderedNumericValidationAtom model → Bool
    | .temporalExpression _ => true
    | _ => false
  comparison.left.anyAtom temporal || comparison.right.anyAtom temporal

/-- Whether partial addressed evaluation has an exact interpretation for an atom. Supported ordinary atoms use per-field relevance, entity-list aggregates use their source-owned extent relevance, and the mixed filled-group count walks its counted groups' own instances. `false` is structural unsupported information, never numeric UNKNOWN.

    A bound repetition coordinate **is** supported, and it is the one supported atom that reads no cell: it answers from the row environment, so its relevance query is vacuously satisfied and no coverage can mask it. That is the Kernel's behaviour — a rule reading it answers under a coverage that drives its field-reading twin to UNKNOWN ([checkpoint](../../../docs/sources/group-and-iteration-probes.md#src-repetition-operand-partial-relevance)) — and refusing it here made the whole rule structurally unsupported rather than merely unmasked. Unmaskable is not unconditional: the separate error-field gate still skips the row before any of this is reached, so a coverage naming neither field reports nothing. -/
def OrderedNumericValidationAtom.supportsAddressedPartial :
    OrderedNumericValidationAtom model → Bool
  | .ordinary _ | .aggregate _ _ | .filledGroupCountMixed _ | .firstFilled _ => true
  | .filledFieldCount source => source.supportsPartialCount
  | .indexed _ | .indexedString _ | .valueCount _ _ | .tokenValueCount _ | .booleanValueCount _ | .tokenDistinctCount _ | .temporalDistinctCount _ => true
  | .sumOfProducts _ => true
  | .temporalExpression source => !source.hasHaving

def OrderedNumericComparison.supportsAddressedPartial
    (comparison : OrderedNumericComparison model) : Bool :=
  !comparison.hasHaving &&
    comparison.left.allAtoms
      OrderedNumericValidationAtom.supportsAddressedPartial &&
    comparison.right.allAtoms
      OrderedNumericValidationAtom.supportsAddressedPartial

structure CheckedOrderedNumericComparison (model : FlatModel) where
  rowGroup : GroupPath
  operandScope : NumericOperandScope := .sameGroup
  core : OrderedNumericComparison model
  modelWellFormed : model.validate.isOk = true
  wellFormed : core.wellFormedInBool rowGroup operandScope = true

end A12Kernel
