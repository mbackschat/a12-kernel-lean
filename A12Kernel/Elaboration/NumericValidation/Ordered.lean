import A12Kernel.Elaboration.NumericValidation.Core

/-! # Checked ordered numeric validation

This module owns the model-indexed numeric leaves used by addressed and generated validation. It retains checked entity-list and row-product sources without widening the scalar syntax in `NumericValidation.Core`.
-/

namespace A12Kernel

/-- A numeric leaf either delegates one established scalar atom unchanged or retains a model-certified first-filled, aggregate, or row-product source for full addressed validation. -/
inductive OrderedNumericValidationAtom (model : FlatModel) where
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

/-- One model-indexed numeric comparison whose atom resolver, rather than the containing leaf, owns relevance timing and addressed-source selection. -/
abbrev OrderedNumericComparison (model : FlatModel) :=
  NumericComparisonOf (OrderedNumericValidationAtom model)

namespace OrderedNumericValidationAtom

@[simp]
def addressedNumericValidationFieldIds :
    NumericValidationAtom → List FieldId
  | .field source => [source.id]
  | .temporalFieldPart source _ => [source.id]
  | .dateRangeBoundPart source _ _ => [source.id]
  | .stringLength source => [source.id]
  | .stringRange source _ _ => [source.id]
  | .fieldValueAsNumber source => [source.fieldId]
  | .dateDifference _ left right | .dayDifference _ left right =>
      let fieldId : ResolvedDateDifferenceOperand → List FieldId
        | .field source => [source.id]
        | .baseYear _ _ => []
      (fieldId left ++ fieldId right).eraseDups
  | .dateTimeDifference _ left right =>
      ((left.fields ++ right.fields).map FlatField.id).eraseDups
  | _ => []

private def checkedNumberEntitySourceAdmittedIn
    (source : CheckedNumberEntitySource model)
    (rowGroup : GroupPath) (scope : NumericOperandScope) : Bool :=
  match scope with
  | .modelWideCheckedComputation => true
  | .sameGroupAddressed => source.directResolvedFields?.isNone
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
  | .sameGroupAddressed => source.source.directFields?.isNone
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

def isDataDependent : OrderedNumericValidationAtom model → Bool
  | .ordinary source => source.isDataDependent
  | .firstFilled _ | .valueCount _ _ | .tokenValueCount _
  | .booleanValueCount _ | .aggregate _ _ | .sumOfProducts _
  | .filledGroupCountMixed _ => true

def summary : OrderedNumericValidationAtom model → NumericScaleSummary
  | .ordinary source => numericValidationSummary source
  | .firstFilled source => source.scaleSummary
  | .valueCount _ _ => NumericScaleSummary.field 0
  | .tokenValueCount source => source.scaleSummary
  | .booleanValueCount source => source.scaleSummary
  | .aggregate op source => source.aggregateScaleSummary op
  | .sumOfProducts source => source.scaleSummary
  | .filledGroupCountMixed _ => NumericScaleSummary.field 0

/-- An ordinary direct atom needs addressed evaluation exactly when any checked field declaration is repeatable. Specialized sources retain their established addressed criteria. -/
def requiresAddressedValidation : OrderedNumericValidationAtom model → Bool
  | .ordinary (.filledGroupCount groups) =>
      groups.any fun reference => !reference.boundRepeatableScope.isEmpty
  | .ordinary source =>
      (addressedNumericValidationFieldIds source).any fun field =>
          match model.lookupUniqueId field with
          | .ok declaration => !declaration.repeatableScope.isEmpty
          | .error _ => false
  | .firstFilled source => source.directResolvedFields?.isNone
  | .valueCount _ source => source.directResolvedFields?.isNone
  | .tokenValueCount source => source.source.directFields?.isNone
  | .booleanValueCount source => source.directFields?.isNone
  | .aggregate _ _ | .sumOfProducts _ => true
  | .filledGroupCountMixed _ => true

def admitted (atom : OrderedNumericValidationAtom model)
    (rowGroup : GroupPath)
    (scope : NumericOperandScope) : Bool :=
  match atom with
  | .ordinary source => source.admitted model rowGroup scope
  | .firstFilled source =>
      checkedNumberEntitySourceAdmittedIn source rowGroup scope
  | .valueCount _ source =>
      checkedNumberEntitySourceAdmittedIn source rowGroup scope
  | .tokenValueCount source =>
      checkedTokenValueCountAdmittedIn source rowGroup scope
  | .booleanValueCount source =>
      match scope with
      | .sameGroup =>
          match source.directFields? with
          | some fields =>
              fields.all fun field => field.groupPath == rowGroup
          | none => false
      | .sameGroupAddressed => source.directFields?.isNone
      | .modelWideNonrepeatable => source.directFields?.isSome
      | .modelWideCheckedComputation => true
  | .aggregate _ source =>
      (scope == .modelWideCheckedComputation ||
        scope == .sameGroupAddressed) &&
        source.directAggregateFields?.isNone
  | .sumOfProducts _ =>
      scope == .modelWideCheckedComputation ||
        scope == .sameGroupAddressed
  | .filledGroupCountMixed operands =>
      (scope == .modelWideCheckedComputation ||
        scope == .sameGroupAddressed) &&
        1 < operands.length &&
        !operands.any CheckedGroupCountOperand.isRoot

def referencesField (atom : OrderedNumericValidationAtom model)
    (field : FieldId) : Bool :=
  match atom with
  | .ordinary source => source.referencesField model field
  | .firstFilled source => source.referencesField field
  | .valueCount _ source => source.referencesField field
  | .tokenValueCount source => source.referencesField field
  | .booleanValueCount source => source.referencesField field
  | .aggregate _ source => source.referencesField field
  | .sumOfProducts source =>
      source.left.field.id == field || source.right.field.id == field
  | .filledGroupCountMixed operands =>
      operands.any fun operand => operand.referencesField model field

/-- Whether this exact checked atom retains any filtered entity-list slot. This is static source structure, not a statement about which runtime branch or candidate will be reached. -/
def hasHaving : OrderedNumericValidationAtom model → Bool
  | .firstFilled source | .valueCount _ source | .aggregate _ source =>
      source.hasHaving
  | .tokenValueCount source => source.source.hasHaving
  | .booleanValueCount source => source.hasHaving
  | .ordinary _ | .sumOfProducts _ | .filledGroupCountMixed _ => false

end OrderedNumericValidationAtom

/-- Static admission for the relevance-aware numeric leaf reuses the complete authored-operation checks and delegates only atom-specific model coherence. -/
def OrderedNumericComparison.wellFormedInBool
    (comparison : OrderedNumericComparison model)
    (rowGroup : GroupPath)
    (scope : NumericOperandScope) : Bool :=
  (comparison.left.anyAtom OrderedNumericValidationAtom.isDataDependent ||
      comparison.right.anyAtom OrderedNumericValidationAtom.isDataDependent) &&
    comparison.left.isAdmittedResolvedNumericOperation &&
    comparison.right.isAdmittedResolvedNumericOperation &&
    comparison.left.allAtoms (·.admitted rowGroup scope) &&
    comparison.right.allAtoms (·.admitted rowGroup scope) &&
    comparison.left.numericOperationAuthoringCheck == .accepted &&
    comparison.right.numericOperationAuthoringCheck == .accepted &&
    match
        comparison.left.summary? OrderedNumericValidationAtom.summary,
        comparison.right.summary? OrderedNumericValidationAtom.summary with
    | some leftSummary, some rightSummary =>
        comparison.op.acceptsScalesWithSuppression
          comparison.suppressExactScaleWarning leftSummary rightSummary
    | _, _ => false

def OrderedNumericComparison.referencesField
    (comparison : OrderedNumericComparison model)
    (field : FieldId) : Bool :=
  comparison.left.anyAtom (·.referencesField field) ||
    comparison.right.anyAtom (·.referencesField field)

/-- Discover `Having` across both complete authored operands without evaluating or lowering away their expression shape. -/
def OrderedNumericComparison.hasHaving
    (comparison : OrderedNumericComparison model) : Bool :=
  comparison.left.anyAtom OrderedNumericValidationAtom.hasHaving ||
    comparison.right.anyAtom OrderedNumericValidationAtom.hasHaving

def OrderedNumericComparison.requiresAddressedValidation
    (comparison : OrderedNumericComparison model) : Bool :=
  comparison.left.anyAtom OrderedNumericValidationAtom.requiresAddressedValidation ||
    comparison.right.anyAtom OrderedNumericValidationAtom.requiresAddressedValidation

/-- Whether partial addressed evaluation has an exact interpretation for an atom. Ordinary atoms use per-field relevance; entity-list aggregates use their source-owned extent relevance. `false` is structural unsupported information, never numeric UNKNOWN. -/
def OrderedNumericValidationAtom.supportsAddressedPartial :
    OrderedNumericValidationAtom model → Bool
  | .ordinary (.filledGroupCount _) => false
  | .ordinary _ | .aggregate _ _ => true
  | .firstFilled _ | .valueCount _ _ | .tokenValueCount _
  | .booleanValueCount _ | .sumOfProducts _ | .filledGroupCountMixed _ => false

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
