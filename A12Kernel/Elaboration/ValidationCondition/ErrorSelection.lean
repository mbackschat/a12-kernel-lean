import A12Kernel.Elaboration.ValidationCondition.ErrorReferences
import A12Kernel.Elaboration.ValidationCondition.StaticIteration

/-! Error-address selection retains authored key identity independently of selected values and
message-cache coordinates (spec/08 §4.3; SemanticIndices4ErrorFieldVisitor). -/

namespace A12Kernel

/-- One authored selection of the error field, before parent-local cache association. -/
structure SelectedErrorReference where
  group : SemanticIndexGroup
  indexDeclaration : FlatFieldDecl
  key : CheckedSemanticIndexKey

namespace SelectedErrorReference

/-- Numeric lookup equivalence does not merge differently spelled authored keys. A typed literal
without spelling uses its supplied token identity; field identity is its checked declaration. -/
def sameKey (left right : SelectedErrorReference) : Bool :=
  left.group == right.group && match left.key, right.key with
  | .literal a sa, .literal b sb => match sa, sb with
      | some a, some b => a == b
      | none, none => a == b
      | _, _ => false
  | .field a, .field b => a.id == b.id
  | _, _ => false

end SelectedErrorReference

namespace ValidationCondition

private def selectedErrorReference (field : FieldId)
    (source : Sum (CheckedSemanticIndexSource model) (CheckedKeyedEntityExtent model)) :
    List SelectedErrorReference :=
  let selection := match source with
    | .inl source => source
    | .inr source => source.selection.indexSource
  let declarations := match source with
    | .inl source => [source.targetDeclaration]
    | .inr source => source.declarations
  if declarations.any (·.id == field) then
    [{ group := selection.group, indexDeclaration := selection.indexDeclaration, key := selection.key }]
  else []

private def shapeErrorSelections (field : FieldId) (shape : CheckedFieldEntityShape model) :
    List SelectedErrorReference :=
  shape.operands.flatMap fun
    | .indexed source _ => selectedErrorReference field (.inl source)
    | .keyed source _ => selectedErrorReference field (.inr source)
    | _ => []

private def numberErrorSelections (field : FieldId) (source : CheckedNumberEntitySource model) :
    List SelectedErrorReference :=
  source.operands.flatMap fun
    | .selected source => selectedErrorReference field source.source
    | _ => []

private def tokenErrorSelections (field : FieldId) (source : CheckedTokenEntitySource model) :
    List SelectedErrorReference :=
  source.operands.flatMap fun
    | .selected source => selectedErrorReference field source.source
    | _ => []

private def fillErrorSelections (field : FieldId) (source : CheckedFieldFillList model) :
    List SelectedErrorReference :=
  source.operands.flatMap fun
    | .indexed source => selectedErrorReference field (.inl source)
    | .keyed source => selectedErrorReference field (.inr source)
    | _ => []

/-- The temporal arm is supplied by the caller because a temporal amount may carry a filtered
entity list, whose selections are this function's own. -/
private def orderedNumericErrorSelections (field : FieldId)
    (temporal : CheckedTemporalNumericExpression model → List SelectedErrorReference) :
    OrderedNumericValidationAtom model → List SelectedErrorReference
  | .firstFilled source | .valueCount _ source | .aggregate _ source => numberErrorSelections field source
  | .tokenValueCount source => tokenErrorSelections field source.source
  | .tokenDistinctCount source => tokenErrorSelections field source
  | .booleanValueCount source => source.operands.flatMap fun
      | .selected source => selectedErrorReference field source.source
      | _ => []
  | .temporalDistinctCount run => shapeErrorSelections field run.source.shape
  | .filledFieldCount source => fillErrorSelections field source
  | .temporalExpression source => temporal source
  | .indexed source => selectedErrorReference field (.inl source.toCheckedSemanticIndexSource)
  | .indexedString source => selectedErrorReference field (.inl source.selection)
  | .sumOfProducts (.selected source) =>
      selectedErrorReference field (.inr source.left.source) ++
      selectedErrorReference field (.inr source.right.source)
  | .sumOfProducts (.row _) | .filledGroupCountMixed _ | .ordinary _ => []

private def filteredAmountErrorSelections (field : FieldId) (amount : CheckedFilteredShiftAmount model) :
    List SelectedErrorReference :=
  orderedNumericErrorSelections field (fun _ => []) (.ofFiltered amount)

private def temporalErrorSelections (field : FieldId) (source : ScalarTemporalExpression model) :
    List SelectedErrorReference :=
  source.dependenciesWith (fun _ => [])
    (fun source => shapeErrorSelections field source.shape)
    (fun source => selectedErrorReference field (.inl source))
    (numeric := fun _ => []) (filtered := filteredAmountErrorSelections field)

private def typedErrorSelections (field : FieldId) :
    CheckedFirstFilledComparisonOperand model → List SelectedErrorReference
  | .firstFilled source => fillErrorSelections field source.source
  | .indexed source _ => selectedErrorReference field (.inl source)
  | .temporal source => temporalErrorSelections field source.core
  | .field _ _ | .boolean _ => []

private def numericErrorSelections (field : FieldId) :
    OrderedNumericValidationAtom model → List SelectedErrorReference :=
  orderedNumericErrorSelections field fun source => match source.core with
    | .temporal operation => operation.sources.flatMap fun source => temporalErrorSelections field source.core
    | .storedProjection source => source.dependenciesWith (fun _ => [])
        (fun source => shapeErrorSelections field source.shape)
        (fun source => selectedErrorReference field (.inl source)) (numeric := fun _ => [])
        (filtered := filteredAmountErrorSelections field)

private def tokenOperandErrorSelections (field : FieldId) :
    CheckedTokenComparisonOperand model → List SelectedErrorReference
  | .firstFilled source _ | .indexed source => tokenErrorSelections field source
  | .literal _ | .field _ => []

private def leafErrorSelections (field : FieldId) :
    ValidationConditionLeaf model → List SelectedErrorReference
  | .indexedFieldPresence _ source => selectedErrorReference field (.inl source)
  | .keyedGroupPresence _ source => selectedErrorReference field (.inr source)
  | .indexedStringPattern source => selectedErrorReference field (.inl source.selection)
  | .indexedCustomFieldValidity source => selectedErrorReference field (.inl source.source.selection)
  | .stringExpression comparison =>
      (comparison.left.core.fields ++ comparison.right.core.fields).flatMap fun
        | .inl _ => []
        | .inr source => selectedErrorReference field (.inl source)
  | .valueList (.number source) =>
      numberErrorSelections field source.fields ++ numberErrorSelections field source.values
  | .valueList (.token source) =>
      tokenErrorSelections field source.fields ++ tokenErrorSelections field source.values
  | .valueList (.literals source) => tokenErrorSelections field source.fields
  | .groupList _ operands => operands.flatMap fun
      | .indexed source => selectedErrorReference field (.inl source)
      | .keyed source => selectedErrorReference field (.inr source)
      | _ => []
  | .fieldFill _ source => fillErrorSelections field source
  | .valuesNotUnique (.number source) => numberErrorSelections field source
  | .valuesNotUnique (.token source) => tokenErrorSelections field source.source
  | .valuesNotUnique (.temporal source) => shapeErrorSelections field source.shape
  | .orderedNumeric _ comparison =>
      (comparison.left.atoms ++ comparison.right.atoms).flatMap (numericErrorSelections field)
  | .firstFilledComparison comparison =>
      typedErrorSelections field comparison.left ++ typedErrorSelections field comparison.right
  | .tokenComparison comparison =>
      tokenOperandErrorSelections field comparison.left ++ tokenOperandErrorSelections field comparison.right
  | .scalarTemporal comparison =>
      temporalErrorSelections field comparison.left.core ++ temporalErrorSelections field comparison.right.core
  | .constructedDateValidity _ source => temporalErrorSelections field source.scalarCore
  | .iteratedDateRange condition => match condition with
      | .overlap source | .pluralOverlap source => shapeErrorSelections field source.shape
      | .yearlessOverlap source | .yearlessPluralOverlap source => shapeErrorSelections field source.shape
      | _ => []
  | .customCondition _ | .flat _ | .numeric _ _ | .groupPresence _ _
  | .repeatableFieldPresence _ _ | .repetitionNotUnique _
  | .guardedRootCurrentRepetition _ _ _ | .guardedRepeatableCurrentRepetition _ _ _
  | .customFieldValidity _ | .stringPattern _ => []

/-- Structural error selections ignore value availability and short-circuiting. Filter bodies
cannot introduce semantic-index operands; their marked ordinary reads own no selection. -/
def errorSelections (condition : ValidationCondition model) (field : FieldId) :
    List SelectedErrorReference :=
  match condition with
  | .leaf leaf => leafErrorSelections field leaf
  | .and left right | .or left right => errorSelections left field ++ errorSelections right field

/-- The error field's selections when they all name one repeatable group by one key. -/
private def soleErrorSelection? (condition : ValidationCondition model) (field : FieldId) :
    Option (SelectedErrorReference × RepeatableGroupDecl) := do
  let selections := condition.errorSelections field
  let first ← selections.head?
  let .repeatable group := first.group | none
  if selections.all first.sameKey then some (first, group) else none

/-- A unique authored selection reanchors only a repeatable level outside the rule's ordinary
iteration, returned with the selection. A single instance has no level to reanchor, so its error
address stays the rule's own
([single-instance key](../../../docs/sources/model-structure-and-declaration-probes.md#src-single-instance-key), rule `LG4`).
The parallel evaluator owns its separate iteration domain and never calls this ordinary selector. -/
def uniqueErrorSelection? (condition : ValidationCondition model) (field : FieldId)
    (iterated : List RepeatableLevel) : Option (SelectedErrorReference × RepeatableGroupDecl) := do
  let (first, group) ← condition.soleErrorSelection? field
  if iterated.contains group.level then none else some (first, group)

/-- Whether a leaf without any semantic-index selection iterates `level`. Its scope comes from
unkeyed reads alone, so its derived iteration scope answers exactly, field-free reads such as a
current-repetition coordinate included; an underivable scope counts as iterating. -/
private def selectionFreeLeafIterates (level : RepeatableLevel) (leaf : ValidationConditionLeaf model) : Bool :=
  model.fields.all (fun declaration => (leafErrorSelections declaration.id leaf).isEmpty) &&
    match ordinaryIterationScope (.leaf leaf) with
    | .ok scope => scope.any (·.contains level)
    | .error _ => true

/-- The error field's selection when it binds the iterated `level` itself: the field reaches the
level only through that selection and nothing else iterates it, so the rule iterates inside the
selected row rather than over the level. A read of another field at the level keeps the level
iterated and the error field unbound there
([below-key error scope](../../../docs/sources/model-structure-and-declaration-probes.md#src-below-key-error-scope),
`N2` and `E2` against `e3` and `e4`), and so does a leaf without a selection whose scope holds the
level. A field-free read inside a leaf that also holds a selection is not seen, and a field-valued
key is treated as another field's read; both are unmeasured. An unresolved reference answer keeps
the level iterated. -/
def levelBindingErrorSelection? (condition : ValidationCondition model) (field : FieldId)
    (level : RepeatableLevel) : Option (SelectedErrorReference × RepeatableGroupDecl) := do
  let (selection, group) ← condition.soleErrorSelection? field
  let unbound (candidate : FieldId) := condition.errorReferenceAt? candidate level == some false
  if group.level == level && unbound field && model.fields.all (fun declaration =>
      declaration.id == field || !condition.referencesField declaration.id || unbound declaration.id) &&
      !condition.anyLeaf (selectionFreeLeafIterates level) then
    some (selection, group)
  else none

end ValidationCondition
end A12Kernel
