import A12Kernel.Elaboration.ValidationCondition.Core

/-! Error-address selection retains authored key identity independently of selected values and
message-cache coordinates (spec/08 §4.3; SemanticIndices4ErrorFieldVisitor). -/

namespace A12Kernel

/-- One authored selection of the error field, before parent-local cache association. -/
structure SelectedErrorReference where
  group : RepeatableGroupDecl
  indexDeclaration : FlatFieldDecl
  key : CheckedSemanticIndexKey

namespace SelectedErrorReference

/-- Numeric lookup equivalence does not merge differently spelled authored keys. A typed literal
without spelling uses its supplied token identity; field identity is its checked declaration. -/
def sameKey (left right : SelectedErrorReference) : Bool :=
  left.group.level == right.group.level && match left.key, right.key with
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
    | .indexed source => selectedErrorReference field (.inl source)
    | .keyed source => selectedErrorReference field (.inr source)
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

private def temporalErrorSelections (field : FieldId) (source : ScalarTemporalExpression model) :
    List SelectedErrorReference :=
  source.dependenciesWith (fun _ => [])
    (fun source => shapeErrorSelections field source.shape)
    (fun source => selectedErrorReference field (.inl source))
    (numeric := fun _ => [])

private def typedErrorSelections (field : FieldId) :
    CheckedFirstFilledComparisonOperand model → List SelectedErrorReference
  | .firstFilled source => fillErrorSelections field source.source
  | .indexed source _ => selectedErrorReference field (.inl source)
  | .temporal source => temporalErrorSelections field source.core
  | .field _ _ | .boolean _ => []

private def numericErrorSelections (field : FieldId) :
    OrderedNumericValidationAtom model → List SelectedErrorReference
  | .firstFilled source | .valueCount _ source | .aggregate _ source => numberErrorSelections field source
  | .tokenValueCount source => tokenErrorSelections field source.source
  | .tokenDistinctCount source => tokenErrorSelections field source
  | .booleanValueCount source => source.operands.flatMap fun
      | .selected source => selectedErrorReference field source.source
      | _ => []
  | .temporalDistinctCount run => shapeErrorSelections field run.source.shape
  | .filledFieldCount source => fillErrorSelections field source
  | .temporalExpression source => match source.core with
      | .temporal operation => operation.sources.flatMap fun source => temporalErrorSelections field source.core
      | .storedProjection source => source.dependenciesWith (fun _ => [])
          (fun source => shapeErrorSelections field source.shape)
          (fun source => selectedErrorReference field (.inl source)) (numeric := fun _ => [])
  | .indexed source => selectedErrorReference field (.inl source.toCheckedSemanticIndexSource)
  | .indexedString source => selectedErrorReference field (.inl source.selection)
  | .sumOfProducts (.selected source) =>
      selectedErrorReference field (.inr source.left.source) ++
      selectedErrorReference field (.inr source.right.source)
  | .sumOfProducts (.row _) | .filledGroupCountMixed _ | .ordinary _ => []

private def tokenOperandErrorSelections (field : FieldId) :
    CheckedTokenComparisonOperand model → List SelectedErrorReference
  | .firstFilled source _ => tokenErrorSelections field source
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

/-- A unique authored selection reanchors only a level outside the rule's ordinary iteration.
The parallel evaluator owns its separate iteration domain and never calls this ordinary selector. -/
def uniqueErrorSelection? (condition : ValidationCondition model) (field : FieldId)
    (iterated : List RepeatableLevel) : Option SelectedErrorReference := do
  let selections := condition.errorSelections field
  let first ← selections.head?
  if iterated.contains first.group.level || !selections.all first.sameKey then none else some first

end ValidationCondition
end A12Kernel
