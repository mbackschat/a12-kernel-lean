import A12Kernel.Elaboration.NumericAggregate.Fields
import A12Kernel.Elaboration.PartialSemanticIndex

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
    (fun _ value => pure value.asNumberValueListCell) (missingStarIsOmitted := true)

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

private def partialProductCell (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell))
    (environment : Env) (field : FieldId) : Except CheckedAddressingError (ValueListCell .number) := do
  let some cell ← read environment field | throw (.partialUnavailable environment field)
  pure (observeCell .validation cell).asNumberValueListCell

private def partialProductCells (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell))
    (field : FieldId) : List Env → Except CheckedAddressingError (List (ValueListCell .number))
  | [] => pure []
  | environment :: rest => do
      let cell ← partialProductCell read environment field
      match cell with
      | .unknown _ => pure [cell]
      | _ => pure (cell :: (← partialProductCells read field rest))

private def partialSelectedProductSide (source : CheckedKeyedNumberProductOperand model)
    (document : CheckedDocument model) (view : CheckedPartialPreliminary model)
    (scope : ValidationRelevanceScope) (outer : Env)
    (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell)) :
    Except CheckedAddressingError (Option (ResolvedValueListSide .number)) := do
  let selection := source.source.selection.indexSource
  match ← selection.selectPartial view outer read with
  | none => pure none
  | some (.unknown cause) | some (.poison cause) => pure (some { cells := [.unknown cause], hasUninstantiatedTail := false, hasHaving := false })
  | some .empty =>
      if !(← source.star.productExtentRelevant scope outer (some selection.group.level) |>.mapError .addressing) then
        return none
      pure (some { cells := [], hasUninstantiatedTail := true, hasHaving := false })
  | some (.value environment) =>
      if !(← source.star.productExtentRelevant scope environment |>.mapError .addressing) then return none
      let resolved ← source.star.path.resolveInCapacity document.source.toDocument environment |>.mapError .addressing
      let cells ← partialProductCells read source.field.id resolved.environments
      pure (some { cells, hasUninstantiatedTail := resolved.domain.hasOpenTail, hasHaving := false })

private def partialProductRows (left right : CheckedStarNumberSource model)
    (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell)) :
    List Env → Except CheckedAddressingError (List ResolvedNumericProductRow)
  | [] => pure []
  | environment :: rest => do
      let leftCell ← partialProductCell read environment left.field.id
      match leftCell with
      | .unknown _ => pure [{ left := leftCell, right := .empty }]
      | _ =>
          let rightCell ← partialProductCell read environment right.field.id
          match rightCell with
          | .unknown _ => pure [{ left := leftCell, right := rightCell }]
          | _ => pure ({ left := leftCell, right := rightCell } :: (← partialProductRows left right read rest))

/-- Both product forms use declared extent for relevance and physical extent for values.
Selection and reached cell reads retain call-local unavailability (spec/07 §4, spec/10 §5). -/
def evaluatePartialDocument (source : CheckedNumericProductAggregate model)
    (document : CheckedDocument model) (outer : Env) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell)) :
    Except CheckedAddressingError PartialValidationNumberAggregateResult := do
  match source with
  | .row source =>
      if !(← source.left.source.productExtentRelevant scope outer |>.mapError .addressing) ||
          !(← source.right.source.productExtentRelevant scope outer |>.mapError .addressing) then return .nonRelevant
      let resolved ← source.left.source.path.resolveInCapacity document.source.toDocument outer |>.mapError .addressing
      let rows ← partialProductRows source.left source.right read resolved.environments
      pure (.evaluated (evalNumericProductAggregate {
        rows, leftSigned := source.left.field.info.signed, rightSigned := source.right.field.info.signed
        hasUninstantiatedTail := resolved.domain.hasOpenTail }))
  | .selected source =>
      let view ← document.applyPartialGeneratedPreliminaryForScope scope |>.mapError .indexPreliminary
      let some left ← partialSelectedProductSide source.left document view scope outer read | return .nonRelevant
      if let .error cause := left.available then return .evaluated (.unknown cause)
      let some right ← partialSelectedProductSide source.right document view scope outer read | return .nonRelevant
      pure (.evaluated (evalIndependentNumericProductAggregate left right
        source.left.field.info.signed source.right.field.info.signed))

end CheckedNumericProductAggregate
end A12Kernel
