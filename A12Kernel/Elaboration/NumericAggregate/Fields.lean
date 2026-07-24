import A12Kernel.Elaboration.NumericSource
import A12Kernel.Elaboration.NumericStar
import A12Kernel.Elaboration.NumberEntityList
import A12Kernel.Semantics.NumericAggregate

/-! # Checked Number aggregate lowering

The established direct route resolves one unfiltered list of at least two distinct nonrepeatable Number fields into the aggregate atom used by checked numeric expressions. The ordinary entity-list route reuses the shared checked direct/plain-star/filtered-star source, resolves each slot lazily in authored order, and delegates the resulting cells through one resolver-parametric scan to the same aggregate folds. `SumOfProducts` instead checks exactly two same-group Number stars at the lowest repeatable level, resolves their shared topology once, and exposes full/partial validation plus a phase-indexed checked-cell fold. The full-validation faces of both checked sources reach generated computation validation through its bounded addressed context; `SumOfProducts` also reaches ordinary addressed rules through the same immutable checked-document projection. Group operands, rule-level partial integration, and concrete syntax remain outside.
-/

namespace A12Kernel

/-- Fail-closed errors owned by this aggregate-field lowering boundary. -/
inductive NumericAggregateElabError where
  | resolve (error : ResolveError)
  | tooFewFields
  | duplicateField (field : FieldId)
  | fieldKindMismatch (path : List String) (actual : SurfaceScalarKind)
  | incoherentCore
  deriving Repr, DecidableEq

/-- Compatibility name for the shared partial all-rows aggregate result. -/
abbrev PartialValidationNumberAggregateResult :=
  PartialValidationAggregateResult

/-- A parser-independent `SumOfProducts` pair. Its two operands are fields, not ordinary entity-list slots: filters, groups, and direct fields are unrepresentable here. -/
structure SurfaceNumericProductAggregate where
  left : SurfaceStarFieldPath
  right : SurfaceStarFieldPath
  deriving Repr, DecidableEq

/-- Fail-closed errors specific to the paired-row aggregate boundary. -/
inductive NumericProductAggregateElabError where
  | source (error : StarNumberElabError)
  | differentGroups (left right : GroupPath)
  | wildcardNotLowest (path : List String)
  | incompatibleTopology
  deriving Repr, DecidableEq

/-- Two Number-star declarations certified against one model and one identical lowest-repeatable-star plan. Runtime row alignment follows from this shared plan rather than from zipping independently expanded lists. -/
structure CheckedNumericProductAggregate (model : FlatModel) where
  left : CheckedStarNumberSource model
  right : CheckedStarNumberSource model
  sameGroup : left.source.declaration.groupPath = right.source.declaration.groupPath
  lowestStar : left.source.path.firstStar + 1 = left.source.path.axes.length
  samePath : left.source.path = right.source.path

private def CheckedStarNumberSource.starsOnlyLowest
    (checked : CheckedStarNumberSource model) : Bool :=
  checked.source.path.firstStar + 1 == checked.source.path.axes.length

/-- Check both fields through the established Number-star owner, then require the Kernel's same-group and lowest-star pair shape. One validated model supplies the common model-zone and non-starred ancestors are supplied once by the later outer environment. -/
def elaborateNumericProductAggregate (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceNumericProductAggregate) :
    Except NumericProductAggregateElabError
      (CheckedNumericProductAggregate model) := do
  let left ← elaborateStarNumberSource model declaringGroup authored.left
    |>.mapError .source
  let right ← elaborateStarNumberSource model declaringGroup authored.right
    |>.mapError .source
  if hGroup : left.source.declaration.groupPath =
      right.source.declaration.groupPath then
    if hLeft : left.starsOnlyLowest then
      if hRight : right.starsOnlyLowest then
        if hPath : left.source.path = right.source.path then
          pure {
            left
            right
            sameGroup := hGroup
            lowestStar := by simpa [CheckedStarNumberSource.starsOnlyLowest] using hLeft
            samePath := hPath }
        else
          throw .incompatibleTopology
      else
        throw (.wildcardNotLowest right.source.declaration.path)
    else
      throw (.wildcardNotLowest left.source.declaration.path)
  else
    throw (.differentGroups left.source.declaration.groupPath
      right.source.declaration.groupPath)

namespace CheckedNumericProductAggregate

/-- `SumOfProducts` adds the two exact declaration scales, exactly like one checked multiplication. -/
def scaleSummary (checked : CheckedNumericProductAggregate model) :
    NumericScaleSummary :=
  NumericScaleSummary.binary .multiply
    (NumericScaleSummary.field checked.left.field.info.scale)
    (NumericScaleSummary.field checked.right.field.info.scale)

/-- Classify both declarations at each environment of the one shared canonical topology. -/
def selectedSideAt (checked : CheckedNumericProductAggregate model)
    (phase : Phase) (resolved : ResolvedStarTopology)
    (read : Env → FieldId → CheckedCell) : ResolvedNumericProductSide :=
  { rows := resolved.environments.map fun environment => {
      left := checked.left.checkedValueListCellAt phase read environment
      right := checked.right.checkedValueListCellAt phase read environment }
    leftSigned := checked.left.field.info.signed
    rightSigned := checked.right.field.info.signed
    hasUninstantiatedTail := resolved.domain.hasOpenTail }

/-- Resolve the common topology once and evaluate the paired-row fold in the requested phase. -/
def evaluateAt (checked : CheckedNumericProductAggregate model)
    (phase : Phase) (document : Document) (outer : Env)
    (read : Env → FieldId → CheckedCell) :
    Except StarAddressingError NumericOperand := do
  let resolved ← checked.left.source.path.resolve document outer
  pure (evalNumericProductAggregate (checked.selectedSideAt phase resolved read))

/-- Classify one product operand from the immutable checked input while retaining path-owned over-repetition. -/
private def checkedDocumentValueListCellAt
    (source : CheckedStarNumberSource model) (phase : Phase)
    (document : CheckedDocument model) (environment : Env) :
    Except CheckedAddressingError (ValueListCell .number) := do
  let addressed ← document.addressedCell environment source.field.id
  pure (source.checkedValueListCell phase addressed.cell environment)

/-- Resolve the product's one certified topology against the immutable checked input, then read each left/right pair in kernel encounter order. -/
def evaluateCheckedDocumentAt (checked : CheckedNumericProductAggregate model)
    (phase : Phase) (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError NumericOperand := do
  let resolved ←
    (checked.left.source.path.resolve document.source.toDocument outer)
      |>.mapError .addressing
  let rows ← resolved.environments.mapM fun environment => do
    let left ←
      checkedDocumentValueListCellAt checked.left phase document environment
    let right ←
      checkedDocumentValueListCellAt checked.right phase document environment
    pure { left, right }
  pure (evalNumericProductAggregate {
    rows
    leftSigned := checked.left.field.info.signed
    rightSigned := checked.right.field.info.signed
    hasUninstantiatedTail := resolved.domain.hasOpenTail
  })

/-- Check either owned declaration from raw storage without inventing a third policy. -/
private def checkedRawCell (checked : CheckedNumericProductAggregate model)
    (read : Env → FieldId → RawCell) (environment : Env)
    (field : FieldId) : CheckedCell :=
  if field == checked.left.field.id then
    checked.left.source.declaration.checkRaw (read environment field)
  else if field == checked.right.field.id then
    checked.right.source.declaration.checkRaw (read environment field)
  else
    malformedCheckedCell

/-- Full validation checks raw cells through the two certified declarations and uses the validation face of formal invalidity. -/
def evaluateValidation (checked : CheckedNumericProductAggregate model)
    (document : Document) (outer : Env)
    (read : Env → FieldId → RawCell) :
    Except StarAddressingError NumericOperand :=
  checked.evaluateAt .validation document outer (checked.checkedRawCell read)

/-- Partial validation requires wildcard or ancestor coverage for both fields before either declaration is read. -/
def evaluatePartial (checked : CheckedNumericProductAggregate model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → RawCell) :
    Except StarAddressingError PartialValidationNumberAggregateResult := do
  let resolved ← checked.left.source.path.resolve document outer
  if checked.left.source.allRowsRelevant scope &&
      checked.right.source.allRowsRelevant scope then
    pure (.evaluated (evalNumericProductAggregate
      (checked.selectedSideAt .validation resolved (checked.checkedRawCell read))))
  else
    pure .nonRelevant

end CheckedNumericProductAggregate

/-- A nonempty resolved field list certified against one flat model. -/
structure CheckedNumericAggregateFields (model : FlatModel) where
  first : FlatNumberField
  rest : List FlatNumberField
  hasMultipleFields : rest.isEmpty = false
  uniqueFields : ({ first, rest : ResolvedNumericAggregateFields }).hasUniqueFields = true
  modelWellFormed : model.validate.isOk = true
  fieldsWellFormed :
    (model.admitsField (.number first) &&
      rest.all fun field => model.admitsField (.number field)) = true

namespace CheckedNumericAggregateFields

def fields (checked : CheckedNumericAggregateFields model) : List FlatNumberField :=
  checked.first :: checked.rest

def resolvedFields (checked : CheckedNumericAggregateFields model) :
    ResolvedNumericAggregateFields :=
  { first := checked.first, rest := checked.rest }

end CheckedNumericAggregateFields

namespace ResolvedNumericAggregateFields

private def classifyObservation : CellObservation → ValueListCell .number
  | .empty => .empty
  | .value (.num amount) => .present amount
  | .value _ => .unknown .malformed
  | .unknown cause | .poison cause => .unknown cause

/-- Construct the common resolved subset from one phase-specific cell observer, preserving authored field order. -/
def resolvedValueSide (source : ResolvedNumericAggregateFields)
    (observe : FieldId → CellObservation) : ResolvedValueListSide .number :=
  { cells := source.fields.map fun field => classifyObservation (observe field.id)
    hasUninstantiatedTail := false
    hasHaving := false }

/-- Retain every source declaration's signedness over the same phase-specific observations. -/
def resolvedSumSide (source : ResolvedNumericAggregateFields)
    (observe : FieldId → CellObservation) : ResolvedNumericSumSide :=
  { cells := source.fields.map fun field =>
      { cell := classifyObservation (observe field.id)
        declarationSigned := field.info.signed }
    uninstantiatedSignedness := []
    hasHaving := false }

/-- Evaluate one resolved direct field-list aggregate through the established aggregate folds. -/
def evaluate (source : ResolvedNumericAggregateFields) (op : NumericAggregateOp)
    (observe : FieldId → CellObservation) : NumericOperand :=
  match op with
  | .sum => evalDeclaredNumericSumAggregate (source.resolvedSumSide observe)
  | .minimum => evalNumericExtremumAggregate .minimum
      (source.resolvedValueSide observe)
  | .maximum => evalNumericExtremumAggregate .maximum
      (source.resolvedValueSide observe)
  | .distinctCount => evalNumericDistinctCountAggregate
      (source.resolvedValueSide observe)

def referencesField (source : ResolvedNumericAggregateFields)
    (field : FieldId) : Bool :=
  source.fields.any fun candidate => candidate.id == field

def allRelevant (source : ResolvedNumericAggregateFields)
    (isRelevant : FlatRelevance) : Bool :=
  source.fields.all fun field => isRelevant field.id

end ResolvedNumericAggregateFields

private def FlatModel.resolveNumericAggregateDeclaration (model : FlatModel)
    (declaringGroup : GroupPath) (reference : SurfaceFieldPath) :
    Except NumericAggregateElabError FlatFieldDecl :=
  (model.resolveNonrepeatableFieldUnchecked declaringGroup reference).mapError .resolve

private def numericAggregateField (declaration : FlatFieldDecl) :
    Except NumericAggregateElabError FlatNumberField :=
  match declaration.toNumberField? with
  | some field => pure field
  | none =>
      throw (.fieldKindMismatch declaration.path declaration.policy.kind.surfaceKind)

private def FlatModel.resolveNumericAggregateDeclarations (model : FlatModel)
    (declaringGroup : GroupPath) :
    List SurfaceFieldPath → Except NumericAggregateElabError (List FlatFieldDecl)
  | [] => pure []
  | reference :: remaining => do
      pure ((← model.resolveNumericAggregateDeclaration declaringGroup reference) ::
        (← model.resolveNumericAggregateDeclarations declaringGroup remaining))

private def numericAggregateFields :
    List FlatFieldDecl → Except NumericAggregateElabError (List FlatNumberField)
  | [] => pure []
  | declaration :: remaining => do
      pure ((← numericAggregateField declaration) ::
        (← numericAggregateFields remaining))

/-- Validate the model once, require at least two direct fields, resolve every source in authored order, and certify the complete Number list. -/
def elaborateNumericAggregateFields (model : FlatModel) (declaringGroup : GroupPath)
    (authored : SurfaceNumericAggregateFields) :
    Except NumericAggregateElabError (CheckedNumericAggregateFields model) :=
  match hModel : model.validate with
  | .error error => .error (.resolve error)
  | .ok () =>
      match authored.rest with
      | [] => .error .tooFewFields
      | secondReference :: remainingReferences => do
          let firstDeclaration ←
            model.resolveNumericAggregateDeclaration declaringGroup authored.first
          let secondDeclaration ←
            model.resolveNumericAggregateDeclaration declaringGroup secondReference
          let remainingDeclarations ← model.resolveNumericAggregateDeclarations declaringGroup
            remainingReferences
          let restDeclarations := secondDeclaration :: remainingDeclarations
          match ResolvedNumericAggregateFields.firstDuplicateFieldId?
              ((firstDeclaration :: restDeclarations).map (·.id)) with
          | some field => throw (.duplicateField field)
          | none => do
              let first ← numericAggregateField firstDeclaration
              let second ← numericAggregateField secondDeclaration
              let remaining ← numericAggregateFields remainingDeclarations
              let rest := second :: remaining
              let resolved : ResolvedNumericAggregateFields := { first, rest }
              if hUnique : resolved.hasUniqueFields = true then
                if hFields :
                    (model.admitsField (.number first) &&
                      rest.all fun field => model.admitsField (.number field)) = true then
                  pure {
                    first
                    rest
                    hasMultipleFields := rfl
                    uniqueFields := hUnique
                    modelWellFormed := by
                      rw [hModel]
                      rfl
                    fieldsWellFormed := hFields
                  }
                else
                  throw .incoherentCore
              else
                throw .incoherentCore

namespace CheckedNumericAggregateFields

/-- Construct the common resolved subset: explicit nonrepeatable cells in authored order, no uninstantiated source, and no filter. -/
def resolvedValueSide (checked : CheckedNumericAggregateFields model)
    (raw : RawFlatContext) : ResolvedValueListSide .number :=
  let context := model.checkContext raw
  checked.resolvedFields.resolvedValueSide context.observeValidationAt

/-- Retain each source declaration's signedness for `Sum` polarity. -/
def resolvedSumSide (checked : CheckedNumericAggregateFields model)
    (raw : RawFlatContext) : ResolvedNumericSumSide :=
  let context := model.checkContext raw
  checked.resolvedFields.resolvedSumSide context.observeValidationAt

/-- Evaluate `Sum` through the shared phase-parameterized aggregate dispatcher. -/
def evaluateSum (checked : CheckedNumericAggregateFields model)
    (raw : RawFlatContext) : NumericOperand :=
  let context := model.checkContext raw
  checked.resolvedFields.evaluate .sum context.observeValidationAt

/-- Evaluate direct `MinValue` or `MaxValue` through the same aggregate dispatcher. -/
def evaluateExtremum (checked : CheckedNumericAggregateFields model)
    (op : NumericExtremumOp) (raw : RawFlatContext) : NumericOperand :=
  let context := model.checkContext raw
  match op with
  | .minimum => checked.resolvedFields.evaluate .minimum context.observeValidationAt
  | .maximum => checked.resolvedFields.evaluate .maximum context.observeValidationAt

end CheckedNumericAggregateFields

namespace CheckedNumericStarSource

/-- Evaluate one checked Number star through the existing declaration-signed Sum semantics. -/
def evaluateSum (checked : CheckedNumericStarSource model)
    (raw : RawSingleGroupContext) : Except NumericStarContextError NumericOperand := do
  checked.validateContext raw
  pure (evalNumericSumAggregate checked.field.info.signed (checked.resolvedValueSide raw))

/-- Evaluate one checked Number star through the existing extremum semantics. -/
def evaluateExtremum (checked : CheckedNumericStarSource model)
    (op : NumericExtremumOp) (raw : RawSingleGroupContext) :
    Except NumericStarContextError NumericOperand := do
  checked.validateContext raw
  pure (evalNumericExtremumAggregate op (checked.resolvedValueSide raw))

end CheckedNumericStarSource

end A12Kernel
