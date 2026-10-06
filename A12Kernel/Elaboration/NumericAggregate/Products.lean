import A12Kernel.Elaboration.NumericAggregate.Fields

namespace A12Kernel

/-- A Number field below one selected parent, reopening only its lowest repeatable level. -/
structure CheckedKeyedNumberProductOperand (model : FlatModel) where
  private mk ::
  source : CheckedKeyedEntityExtent model
  star : CheckedStarFieldPath model
  targetOwned : source.target = .star star
  field : FlatNumberField
  fieldOwned : star.declaration.toNumberField? = some field
  lowestStar : star.path.firstStar + 1 = star.path.axes.length

namespace CheckedKeyedNumberProductOperand

def sideWith (source : CheckedKeyedNumberProductOperand model) (phase : Phase)
    (document : Document) (outer : Env) (direct : FieldId → CheckedCell)
    (stored : FieldId → Option String) (read : Env → FieldId → CheckedCell)
    (column : SemanticIndexColumnReader) :
    Except CheckedAddressingError (ResolvedValueListSide .number) :=
  selectedValueListSideWith (.inr source.source) phase document outer direct stored read column
    (fun _ value => pure value.asNumberValueListCell)

def sideIn (source : CheckedKeyedNumberProductOperand model) (phase : Phase)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError (ResolvedValueListSide .number) :=
  source.sideWith phase document.source.toDocument outer document.flatContext.read
    document.flatContext.storedText document.computationFillContext.read
    (document.resolveSemanticIndexColumnWith document.read)

end CheckedKeyedNumberProductOperand

/-- Each independently keyed operand retains its own selection; the shared owning group is a
static admission constraint, not a runtime row identity (spec/07 §4). -/
structure CheckedSelectedNumericProductAggregate (model : FlatModel) where
  left : CheckedKeyedNumberProductOperand model
  right : CheckedKeyedNumberProductOperand model
  sameGroup : left.star.declaration.groupPath = right.star.declaration.groupPath

inductive CheckedNumericProductAggregate (model : FlatModel) where
  | row (source : CheckedRowNumericProductAggregate model)
  | selected (source : CheckedSelectedNumericProductAggregate model)

private def requireKeyedProductLowestStar (source : CheckedKeyedEntityExtent model) :
    Except NumericProductAggregateElabError Unit :=
  match source.target with
  | .star star =>
      if star.path.firstStar + 1 = star.path.axes.length then pure ()
      else throw (.wildcardOnlyAtLowestLevel star.declaration.path)
  | _ => throw .incompatibleTopology

private def certifyKeyedProductOperand (source : CheckedKeyedEntityExtent model) :
    Except NumericProductAggregateElabError (CheckedKeyedNumberProductOperand model) := do
  match hTarget : source.target with
  | .star star =>
      if hLowest : star.path.firstStar + 1 = star.path.axes.length then
        match hField : star.declaration.toNumberField? with
        | none => throw (.source (.fieldNotNumber star.declaration.path))
        | some field => pure {
            source, star, targetOwned := hTarget, field, fieldOwned := hField
            lowestStar := hLowest }
      else throw (.wildcardOnlyAtLowestLevel star.declaration.path)
  | _ => throw .incompatibleTopology

def elaborateNumericProductAggregate (model : FlatModel) (declaringGroup : GroupPath)
    (authored : SurfaceNumericProductAggregate) (writtenGroup : GroupPath := declaringGroup) :
    Except NumericProductAggregateElabError (CheckedNumericProductAggregate model) := do
  match authored.leftKey, authored.rightKey with
  | none, none => .row <$> elaborateRowNumericProductAggregate model declaringGroup authored writtenGroup
  | some leftKey, some rightKey =>
      let left ← elaborateKeyedEntityExtent model declaringGroup { target := .star authored.left, key := leftKey }
        |>.mapError .keyed
      let right ← elaborateKeyedEntityExtent model declaringGroup { target := .star authored.right, key := rightKey }
        |>.mapError .keyed
      if left.groupPath != right.groupPath then throw (.differentGroups left.groupPath right.groupPath)
      if authored.leftHaving.isSome || authored.rightHaving.isSome then throw .wildcardAtLowestLevelRequired
      requireKeyedProductLowestStar left
      requireKeyedProductLowestStar right
      let left ← certifyKeyedProductOperand left
      let right ← certifyKeyedProductOperand right
      if hGroup : left.star.declaration.groupPath = right.star.declaration.groupPath then
        pure (.selected { left, right, sameGroup := hGroup })
      else throw (.differentGroups left.star.declaration.groupPath right.star.declaration.groupPath)
  | _, _ => throw .incompatibleTopology

namespace CheckedNumericProductAggregate

def scaleSummary : CheckedNumericProductAggregate model → NumericScaleSummary
  | .row source => source.scaleSummary
  | .selected source => NumericScaleSummary.binary .multiply
      (NumericScaleSummary.field source.left.field.info.scale)
      (NumericScaleSummary.field source.right.field.info.scale)

def referencesField (source : CheckedNumericProductAggregate model) (field : FieldId) : Bool :=
  match source with
  | .row source => source.left.field.id == field || source.right.field.id == field
  | .selected source => source.left.source.referencesField field || source.right.source.referencesField field

def evaluateAt (source : CheckedNumericProductAggregate model) (phase : Phase)
    (document : Document) (outer : Env) (read : Env → FieldId → CheckedCell)
    (selectedRead : CheckedKeyedNumberProductOperand model → Except StarAddressingError (ResolvedValueListSide .number) :=
      fun source => .error (.unsupportedGroupOperand source.source.groupPath)) :
    Except StarAddressingError NumericOperand := do
  match source with
  | .row source => source.evaluateAt phase document outer read
  | .selected source =>
      let left ← selectedRead source.left
      let right ← selectedRead source.right
      pure (evalIndependentNumericProductAggregate left right source.left.field.info.signed source.right.field.info.signed)

def evaluateCheckedDocumentAt (source : CheckedNumericProductAggregate model) (phase : Phase)
    (document : CheckedDocument model) (outer : Env) : Except CheckedAddressingError NumericOperand := do
  match source with
  | .row source => source.evaluateCheckedDocumentAt phase document outer
  | .selected source =>
      let left ← source.left.sideIn phase document outer
      let right ← source.right.sideIn phase document outer
      pure (evalIndependentNumericProductAggregate left right source.left.field.info.signed source.right.field.info.signed)

def evaluateValidation (source : CheckedNumericProductAggregate model)
    (document : Document) (outer : Env) (read : Env → FieldId → RawCell) :
    Except StarAddressingError NumericOperand :=
  match source with
  | .row source => source.evaluateValidation document outer read
  | .selected source => .error (.unsupportedGroupOperand source.left.source.groupPath)

def evaluatePartial (source : CheckedNumericProductAggregate model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → RawCell) : Except StarAddressingError PartialValidationNumberAggregateResult :=
  match source with
  | .row source => source.evaluatePartial document outer scope read
  | .selected source => .error (.unsupportedGroupOperand source.left.source.groupPath)

end CheckedNumericProductAggregate
end A12Kernel
