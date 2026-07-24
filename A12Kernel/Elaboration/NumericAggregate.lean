import A12Kernel.Elaboration.NumericSource
import A12Kernel.Elaboration.NumericStar
import A12Kernel.Elaboration.NumberEntityList
import A12Kernel.Semantics.NumericAggregate

/-! # Checked Number aggregate lowering

The established direct route resolves one unfiltered list of at least two distinct nonrepeatable Number fields into the aggregate atom used by checked numeric expressions. The ordinary entity-list route reuses the shared checked direct/plain-star/filtered-star source, resolves each slot lazily in authored order, and delegates the resulting cells through one resolver-parametric scan to the same aggregate folds. `SumOfProducts` instead checks exactly two same-group Number stars at the lowest repeatable level, resolves their shared topology once, and exposes full/partial validation plus a phase-indexed checked-cell fold. The full-validation faces of both checked sources reach generated computation validation through its bounded addressed context. Group operands, rule-level partial integration, wider whole-rule addressed orchestration, and concrete syntax remain outside.
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

private def appendNumericSumSide
    (left right : ResolvedNumericSumSide) : ResolvedNumericSumSide :=
  { cells := left.cells ++ right.cells
    uninstantiatedSignedness :=
      left.uninstantiatedSignedness ++ right.uninstantiatedSignedness
    hasHaving := left.hasHaving || right.hasHaving }

private structure ResolvedNumberEntityAggregateSides where
  values : ResolvedValueListSide .number := {
    cells := [], hasUninstantiatedTail := false, hasHaving := false }
  sum : ResolvedNumericSumSide := {
    cells := [], uninstantiatedSignedness := [], hasHaving := false }

namespace ResolvedNumberEntityAggregateSides

private def append (accumulated : ResolvedNumberEntityAggregateSides)
    (declarationSigned : Bool) (side : ResolvedValueListSide .number) :
    ResolvedNumberEntityAggregateSides :=
  { values := accumulated.values.append side
    sum := appendNumericSumSide accumulated.sum
      (side.toNumericSumSide declarationSigned) }

private def evaluate (accumulated : ResolvedNumberEntityAggregateSides)
    (op : NumericAggregateOp) : NumericOperand :=
  match op with
  | .sum => evalDeclaredNumericSumAggregate accumulated.sum
  | .minimum => evalNumericExtremumAggregate .minimum accumulated.values
  | .maximum => evalNumericExtremumAggregate .maximum accumulated.values
  | .distinctCount => evalNumericDistinctCountAggregate accumulated.values

end ResolvedNumberEntityAggregateSides

namespace CheckedNumberEntityField

/-- Classify one checked direct slot through the declaration-owned Number reader at the caller's phase. -/
def resolvedAggregateSideAt (checked : CheckedNumberEntityField model)
    (phase : Phase) (context : FlatContext) : ResolvedValueListSide .number :=
  { cells := [checked.field.valueListCellAt phase context]
    hasUninstantiatedTail := false
    hasHaving := false }

/-- Validation specialization retained for established aggregate consumers. -/
def resolvedAggregateSide (checked : CheckedNumberEntityField model)
    (context : FlatContext) : ResolvedValueListSide .number :=
  checked.resolvedAggregateSideAt .validation context

end CheckedNumberEntityField

namespace CheckedNumberEntityOperand

private def resolveCheckedDocumentNumberCells
    (document : CheckedDocument model) (phase : Phase)
    (field : FlatNumberField) :
    List Env → List (ValueListCell .number) →
      Except CheckedAddressingError
        (Sum (List (ValueListCell .number)) NumericOperand)
  | [], reversed => pure (.inl reversed.reverse)
  | environment :: remaining, reversed => do
      match ← document.numberValueListCellAt phase environment field with
      | .unknown cause => pure (.inr (.unknown cause))
      | cell =>
          resolveCheckedDocumentNumberCells document phase field
            remaining (cell :: reversed)

private def resolvedCheckedDocumentSide
    (document : CheckedDocument model) (phase : Phase)
    (field : FlatNumberField)
    (environments : List Env) (hasUninstantiatedTail hasHaving : Bool) :
    Except CheckedAddressingError
      (Sum (ResolvedValueListSide .number) NumericOperand) := do
  match ← resolveCheckedDocumentNumberCells document phase field
      environments [] with
  | .inl cells => pure (.inl { cells, hasUninstantiatedTail, hasHaving })
  | .inr result => pure (.inr result)

/-- Resolve exactly one authored slot. Plain and filtered stars reuse the general checked topology and filter owners; direct fields reuse the checked flat Number reader. -/
def resolvedAggregateSide (checked : CheckedNumberEntityOperand model)
    (document : Document) (outer : Env) (direct : FlatContext)
    (filterRead : Env → FieldId → CheckedCell)
    (starRead : Env → FieldId → RawCell) :
    Except StarAddressingError (ResolvedValueListSide .number) :=
  match checked with
  | .field source => pure (source.resolvedAggregateSide direct)
  | .star source => source.resolvedValueSide document outer starRead
  | .starHaving source =>
      source.resolvedValueSide document outer filterRead starRead

/-- Resolve one full-validation aggregate slot from a caller-prepared checked view. Direct and repeated cells therefore share one validation phase without resampling declaration checks. -/
def resolvedValidationAggregateSideIn
    (checked : CheckedNumberEntityOperand model)
    (document : Document) (outer : Env) (direct : FlatContext)
    (read : Env → FieldId → CheckedCell) :
    Except StarAddressingError (ResolvedValueListSide .number) :=
  match checked with
  | .field source =>
      pure (source.resolvedAggregateSideAt .validation direct)
  | .star source => do
      let resolved ← source.source.path.resolve document outer
      pure (resolved.toResolvedSide
        (source.checkedValueListCellAt .validation read))
  | .starHaving source =>
      source.source.source.resolvedValidationHavingValueListSide
        document outer source.having read
        (source.source.checkedValueListCellAt .validation read)

/-- Resolve one aggregate slot at computation phase. Filtered stars use the runtime iterator's one-kept-successor lookahead and stop at the first reached filter or target poison; plain stars and direct fields preserve the same checked-cell classification without validation's unknown-as-drop projection. -/
def resolvedComputationAggregateSide
    (checked : CheckedNumberEntityOperand model)
    (document : Document) (outer : Env) (direct : FlatContext)
    (filterRead starRead : Env → FieldId → CheckedCell) :
    Except StarAddressingError
      (Sum (ResolvedValueListSide .number) NumericOperand) :=
  match checked with
  | .field source =>
      pure (.inl (source.resolvedAggregateSideAt .computation direct))
  | .star source => do
      let resolved ← source.source.path.resolve document outer
      pure (.inl (resolved.toResolvedSide
        (source.checkedValueListCellAt .computation starRead)))
  | .starHaving source => do
      let resolved ← source.source.source.path.resolve document outer
      let filterContext : CorrelationContext := { read := filterRead }
      let consume := fun cells environment =>
        match source.source.checkedValueListCellAt .computation
            starRead environment with
        | .unknown cause => .inr cause
        | cell => .inl (cell :: cells)
      match source.having.scanComputation filterContext outer consume
          resolved.environments [] with
      | .exhausted reversed =>
          pure (.inl {
            cells := reversed.reverse
            hasUninstantiatedTail := resolved.domain.hasOpenTail
            hasHaving := true })
      | .terminated cause | .poison cause =>
          pure (.inr (.unknown cause))

/-- Resolve one validation aggregate slot from the immutable checked document. Validation filters evaluate every candidate before the first target classification; target reads then stop at the first formal cause. -/
def resolvedCheckedDocumentValidationAggregateSide
    (checked : CheckedNumberEntityOperand model)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError
      (Sum (ResolvedValueListSide .number) NumericOperand) :=
  do
    let side :=
      (← checked.resolveCheckedValidationOperand document outer)
        |>.valueListSideAt .validation
    match side.available with
    | .error cause => pure (.inr (.unknown cause))
    | .ok () => pure (.inl side)

/-- Resolve one computation aggregate slot from the same checked document. A filtered slot retains one-kept-successor lookahead and keeps structural target/filter failure outside formal poison. -/
def resolvedCheckedDocumentComputationAggregateSide
    (checked : CheckedNumberEntityOperand model)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError
      (Sum (ResolvedValueListSide .number) NumericOperand) :=
  match checked with
  | .field source =>
      resolvedCheckedDocumentSide document .computation source.field
        [[]] false false
  | .star source => do
      let resolved ←
        (source.source.path.resolve document.source.toDocument outer)
          |>.mapError .addressing
      resolvedCheckedDocumentSide document .computation source.field
        resolved.environments resolved.domain.hasOpenTail false
  | .starHaving source => do
      let resolved ←
        (source.source.source.path.resolve document.source.toDocument outer)
          |>.mapError .addressing
      let consume := fun cells environment => do
        match ← document.numberValueListCellAt .computation environment
            source.source.field with
        | .unknown cause => pure (.inr cause)
        | cell => pure (.inl (cell :: cells))
      match ← source.having.scanComputationResolving
          document.resolvingCorrelationContext outer consume
          resolved.environments [] with
      | .exhausted reversed =>
          pure (.inl {
            cells := reversed.reverse
            hasUninstantiatedTail := resolved.domain.hasOpenTail
            hasHaving := true })
      | .terminated cause | .poison cause =>
          pure (.inr (.unknown cause))

/-- Resolve one unfiltered partial-validation slot from the checked document. Direct nonrelevance precedes its cell query; star topology precedes the established all-rows gate; a local filter remains a rule-level skip. -/
def resolvedCheckedDocumentPartialAggregateSide
    (checked : CheckedNumberEntityOperand model)
    (document : CheckedDocument model) (outer : Env)
    (scope : ValidationRelevanceScope) :
    Except CheckedAddressingError
      (Sum (ResolvedValueListSide .number)
        PartialValidationNumberAggregateResult) :=
  match checked with
  | .field source =>
      if scope.coversCell model source.declaration.path [] then do
        match ← resolvedCheckedDocumentSide document .validation source.field
            [[]] false false with
        | .inl side => pure (.inl side)
        | .inr result => pure (.inr (.evaluated result))
      else
        pure (.inr .nonRelevant)
  | .star source => do
      let resolved ←
        (source.source.path.resolve document.source.toDocument outer)
          |>.mapError .addressing
      if source.source.allRowsRelevant scope then do
        match ← resolvedCheckedDocumentSide document .validation source.field
            resolved.environments resolved.domain.hasOpenTail false with
        | .inl side => pure (.inl side)
        | .inr result => pure (.inr (.evaluated result))
      else
        pure (.inr .nonRelevant)
  | .starHaving _ => pure (.inr .skippedHaving)

/-- Resolve one partial-validation aggregate slot. Direct fields require their concrete cell; ordinary stars require complete wildcard/ancestor coverage and retain the established topology-produced side unchanged. Filtered slots return the rule-level skip marker without evaluating their filter. -/
def resolvedPartialAggregateSide (checked : CheckedNumberEntityOperand model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (direct : FlatContext) (starRead : Env → FieldId → RawCell) :
    Except StarAddressingError
      (Sum (ResolvedValueListSide .number)
        PartialValidationNumberAggregateResult) :=
  match checked with
  | .field source =>
      if scope.coversCell model source.declaration.path [] then
        pure (.inl (source.resolvedAggregateSide direct))
      else
        pure (.inr .nonRelevant)
  | .star source => do
      match ← source.resolvedPartialAllRowsValueSide document outer scope starRead with
      | .nonRelevant => pure (.inr .nonRelevant)
      | .relevant side => pure (.inl side)
  | .starHaving _ => pure (.inr .skippedHaving)

end CheckedNumberEntityOperand

namespace CheckedNumberEntitySource

/-- Run the sole authored-order aggregate scan after the caller selects the phase-specific operand resolver. Validation and computation therefore share termination, declaration metadata, accumulation, and final operator dispatch. -/
private def evaluateAggregateWith (checked : CheckedNumberEntitySource model)
    (op : NumericAggregateOp)
    (resolve : CheckedNumberEntityOperand model →
      Except Error
        (Sum (ResolvedValueListSide .number) NumericOperand)) :
    Except Error NumericOperand := do
  match ← scanResolvedValueListOperands
      (state := ResolvedNumberEntityAggregateSides)
      (terminal := NumericOperand)
      resolve
      (fun cause => .unknown cause)
      (fun accumulated operand side =>
        accumulated.append operand.declarationSigned side)
      checked.operands {} with
  | .inl accumulated => pure (accumulated.evaluate op)
  | .inr result => pure result

/-- Evaluate a checked ordinary Number entity-list aggregate in authored slot order. Each wildcard occurrence resolves independently. A formally unavailable reached cell returns immediately, so no later star topology, filter, or target reader is sampled. -/
def evaluateAggregate (checked : CheckedNumberEntitySource model)
    (op : NumericAggregateOp) (document : Document) (outer : Env)
    (directRead : RawFlatContext)
    (filterRead : Env → FieldId → CheckedCell)
    (starRead : Env → FieldId → RawCell) :
    Except StarAddressingError NumericOperand :=
  let direct := model.checkContext directRead
  checked.evaluateAggregateWith op fun operand => do
    pure (.inl (← operand.resolvedAggregateSide document outer direct
      filterRead starRead))

/-- Evaluate the same full-validation fold over one caller-prepared checked scalar/repeatable view. Every slot preserves authored order, validation-phase UNKNOWN, declaration-specific missing polarity, and structural address failure. -/
def evaluateValidationAggregateIn (checked : CheckedNumberEntitySource model)
    (op : NumericAggregateOp) (document : Document) (outer : Env)
    (direct : FlatContext) (read : Env → FieldId → CheckedCell) :
    Except StarAddressingError NumericOperand := do
  checked.evaluateAggregateWith op fun operand => do
    pure (.inl (← operand.resolvedValidationAggregateSideIn
      document outer direct read))

/-- Evaluate a checked ordinary Number entity-list aggregate at computation phase. Operand slots remain authored-order lazy, and each filtered star delegates to the shared one-kept-successor iterator rather than selecting its complete row set eagerly. -/
def evaluateComputationAggregate (checked : CheckedNumberEntitySource model)
    (op : NumericAggregateOp) (document : Document) (outer : Env)
    (directRead : FieldId → CheckedCell)
    (filterRead starRead : Env → FieldId → CheckedCell) :
    Except StarAddressingError NumericOperand :=
  let direct : FlatContext := { read := directRead }
  checked.evaluateAggregateWith op fun operand =>
    operand.resolvedComputationAggregateSide document outer direct
      filterRead starRead

/-- Evaluate validation-phase aggregate accumulation from one immutable model-certified checked document. -/
def evaluateCheckedDocumentValidationAggregate
    (checked : CheckedNumberEntitySource model)
    (op : NumericAggregateOp) (document : CheckedDocument model)
    (outer : Env) : Except CheckedAddressingError NumericOperand :=
  checked.evaluateAggregateWith op fun operand =>
    operand.resolvedCheckedDocumentValidationAggregateSide document outer

/-- Evaluate computation-phase aggregate accumulation from the same checked document without changing filter or poison timing. -/
def evaluateCheckedDocumentComputationAggregate
    (checked : CheckedNumberEntitySource model)
    (op : NumericAggregateOp) (document : CheckedDocument model)
    (outer : Env) : Except CheckedAddressingError NumericOperand :=
  checked.evaluateAggregateWith op fun operand =>
    operand.resolvedCheckedDocumentComputationAggregateSide document outer

/-- Run the common partial aggregate fold after the caller selects a raw or checked-document operand resolver. The source-wide filter skip remains before every resolver call. -/
def evaluatePartialAggregateWith
    (checked : CheckedNumberEntitySource model) (op : NumericAggregateOp)
    (resolve : CheckedNumberEntityOperand model →
      Except Error (Sum (ResolvedValueListSide .number)
        PartialValidationNumberAggregateResult)) :
    Except Error PartialValidationNumberAggregateResult :=
  if checked.hasHaving then
    pure .skippedHaving
  else do
    match ← scanResolvedValueListOperands
        (state := ResolvedNumberEntityAggregateSides)
        (terminal := PartialValidationNumberAggregateResult)
        resolve
        (fun cause => .evaluated (.unknown cause))
        (fun accumulated operand side =>
          accumulated.append operand.declarationSigned side)
        checked.operands {} with
    | .inl accumulated => pure (.evaluated (accumulated.evaluate op))
    | .inr result => pure result

/-- Evaluate an unfiltered checked Number aggregate under partial validation. A locally visible `Having` skips the rule before topology, relevance, or reads. Otherwise direct slots use concrete relevance and every star uses the established all-rows wildcard/ancestor gate, with the same authored-order early termination as full validation. A containing whole condition must still discover filters across every branch before invoking any leaf. -/
def evaluatePartialAggregate (checked : CheckedNumberEntitySource model)
    (op : NumericAggregateOp) (document : Document) (outer : Env)
    (scope : ValidationRelevanceScope) (directRead : RawFlatContext)
    (starRead : Env → FieldId → RawCell) :
    Except StarAddressingError PartialValidationNumberAggregateResult :=
  checked.evaluatePartialAggregateWith op fun operand =>
    operand.resolvedPartialAggregateSide document outer scope
      (model.checkContext directRead) starRead

/-- Evaluate partial aggregate accumulation from the immutable checked document with the same filter-skip and relevance gates. -/
def evaluateCheckedDocumentPartialAggregate
    (checked : CheckedNumberEntitySource model)
    (op : NumericAggregateOp) (document : CheckedDocument model)
    (outer : Env) (scope : ValidationRelevanceScope) :
    Except CheckedAddressingError PartialValidationNumberAggregateResult :=
  checked.evaluatePartialAggregateWith op fun operand =>
    operand.resolvedCheckedDocumentPartialAggregateSide document outer scope

/-- Evaluate numeric `NumberOfValueInFields` without an addressed document exactly when every checked operand is direct. This scalar compatibility path never invents topology for a repeatable source. -/
def evaluateDirectValueCountAt? (checked : CheckedNumberEntitySource model)
    (expected : Rat) (phase : Phase) (context : FlatContext) :
    Option NumericOperand := do
  let (first, rest) ← checked.directFields?
  pure (evalValueCountAggregate expected {
    cells := (first :: rest).map fun field => {
      cell := field.valueListCellAt phase context
      selectedByHaving := false }
    hasUninstantiatedTail := false
    hasHaving := false })

/-- Run `NumberOfValueInFields` over the existing checked Number entity-list route. Unlike the other aggregate folds, this accumulator retains whether each matching cell came through a filter because only such a current match can later disappear. -/
private def evaluateValueCountWith (checked : CheckedNumberEntitySource model)
    (expected : Rat)
    (resolve : CheckedNumberEntityOperand model →
      Except Error
        (Sum (ResolvedValueListSide .number) NumericOperand)) :
    Except Error NumericOperand := do
  match ← scanResolvedValueListOperands
      (state := ResolvedValueCountSide .number)
      (terminal := NumericOperand)
      resolve
      (fun cause => .unknown cause)
      (fun accumulated _ side => accumulated.appendResolved side)
      checked.operands ResolvedValueCountSide.empty with
  | .inl accumulated => pure (evalValueCountAggregate expected accumulated)
  | .inr result => pure result

/-- Evaluate numeric `NumberOfValueInFields` in full validation from one already-prepared checked scalar/repeatable view. -/
def evaluateValueCountValidationIn (checked : CheckedNumberEntitySource model)
    (expected : Rat) (document : Document) (outer : Env)
    (direct : FlatContext) (read : Env → FieldId → CheckedCell) :
    Except StarAddressingError NumericOperand :=
  checked.evaluateValueCountWith expected fun operand => do
    pure (.inl (← operand.resolvedValidationAggregateSideIn
      document outer direct read))

/-- Evaluate numeric `NumberOfValueInFields` at computation phase. Filtered slots retain the existing one-kept-successor scan and propagate the first reached filter or target cause. -/
def evaluateValueCountComputation (checked : CheckedNumberEntitySource model)
    (expected : Rat) (document : Document) (outer : Env)
    (directRead : FieldId → CheckedCell)
    (filterRead starRead : Env → FieldId → CheckedCell) :
    Except StarAddressingError NumericOperand :=
  let direct : FlatContext := { read := directRead }
  checked.evaluateValueCountWith expected fun operand =>
    operand.resolvedComputationAggregateSide document outer direct
      filterRead starRead

/-- Evaluate validation-phase numeric value count through the checked-document aggregate resolver, retaining per-selected-cell filter provenance. -/
def evaluateCheckedDocumentValueCountValidation
    (checked : CheckedNumberEntitySource model)
    (expected : Rat) (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError NumericOperand :=
  checked.evaluateValueCountWith expected fun operand =>
    operand.resolvedCheckedDocumentValidationAggregateSide document outer

/-- Evaluate computation-phase numeric value count through the same resolver and its one-kept-successor filter traversal. -/
def evaluateCheckedDocumentValueCountComputation
    (checked : CheckedNumberEntitySource model)
    (expected : Rat) (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError NumericOperand :=
  checked.evaluateValueCountWith expected fun operand =>
    operand.resolvedCheckedDocumentComputationAggregateSide document outer

/-- Run the common partial value-count fold over a raw or checked-document operand resolver. -/
def evaluatePartialValueCountWith
    (checked : CheckedNumberEntitySource model) (expected : Rat)
    (resolve : CheckedNumberEntityOperand model →
      Except Error (Sum (ResolvedValueListSide .number)
        PartialValidationNumberAggregateResult)) :
    Except Error PartialValidationNumberAggregateResult :=
  if checked.hasHaving then
    pure .skippedHaving
  else do
    match ← scanResolvedValueListOperands
        (state := ResolvedValueCountSide .number)
        (terminal := PartialValidationNumberAggregateResult)
        resolve
        (fun cause => .evaluated (.unknown cause))
        (fun accumulated _ side => accumulated.appendResolved side)
        checked.operands ResolvedValueCountSide.empty with
    | .inl accumulated =>
        pure (.evaluated (evalValueCountAggregate expected accumulated))
    | .inr result => pure result

/-- Evaluate the unfiltered numeric value count under partial validation. A locally visible filter skips the rule before topology, relevance, or target reads, matching the other entity-list aggregate leaves. -/
def evaluatePartialValueCount (checked : CheckedNumberEntitySource model)
    (expected : Rat) (document : Document) (outer : Env)
    (scope : ValidationRelevanceScope) (directRead : RawFlatContext)
    (starRead : Env → FieldId → RawCell) :
    Except StarAddressingError PartialValidationNumberAggregateResult :=
  checked.evaluatePartialValueCountWith expected fun operand =>
    operand.resolvedPartialAggregateSide document outer scope
      (model.checkContext directRead) starRead

/-- Evaluate partial numeric value count from the immutable checked document without changing per-cell filter provenance or partial gates. -/
def evaluateCheckedDocumentPartialValueCount
    (checked : CheckedNumberEntitySource model)
    (expected : Rat) (document : CheckedDocument model)
    (outer : Env) (scope : ValidationRelevanceScope) :
    Except CheckedAddressingError PartialValidationNumberAggregateResult :=
  checked.evaluatePartialValueCountWith expected fun operand =>
    operand.resolvedCheckedDocumentPartialAggregateSide document outer scope

end CheckedNumberEntitySource

end A12Kernel
