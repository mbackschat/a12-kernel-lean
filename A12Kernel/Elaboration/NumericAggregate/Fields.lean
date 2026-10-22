import A12Kernel.Elaboration.NumericSource
import A12Kernel.Elaboration.NumericStar
import A12Kernel.Elaboration.NumberEntityList
import A12Kernel.Semantics.NumericAggregate

/-! # Checked Number aggregate lowering

The established direct route resolves one unfiltered list of at least two distinct nonrepeatable Number fields into the aggregate atom used by checked numeric expressions. The ordinary entity-list route reuses the shared checked direct/plain-star/filtered-star source, resolves each slot lazily in authored order, and delegates the resulting cells through one resolver-parametric scan to the same aggregate folds. `SumOfProducts` instead checks exactly two unfiltered Number stars whose fields have the same immediate owning group and whose lowest-repeatable topology is identical, requires every unstarred repeatable ancestor to lie in the declaring scope, resolves that shared topology once, and exposes full/partial validation plus a phase-indexed checked-cell fold. The owning group may be a fixed descendant of the starred group. The full-validation faces of both checked sources reach generated computation validation through its bounded addressed context; unfiltered Number aggregates also reach ordinary partial rules through the call-local partial-view route, while `SumOfProducts` uses the shared declared-capacity relevance judgment and call-local partial reads in `NumericAggregate.Products`. Group operands and concrete syntax remain outside.
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

/-- Number-only result for the call-local partial-view aggregate route. Extent relevance and ordinary aggregate outcomes retain the shared carrier, while cause-free read unavailability remains separate without widening token or value-count APIs. -/
inductive PartialValidationNumberAggregateViewResult where
  | silentlyUnavailable
  | result (result : PartialValidationNumberAggregateResult)
  deriving Repr, DecidableEq

/-- Products need every declared coordinate, not only physical rows. A missing selected parent
requires a wildcard there; finite lower capacity can be covered by concrete identifiers
(spec/07 §4, partial-product capacity matrix, 2026-10-06). -/
def CheckedStarFieldPath.productExtentRelevant (source : CheckedStarFieldPath model)
    (scope : ValidationRelevanceScope) (outer : Env)
    (missingParent : Option RepeatableLevel := none) : Except StarAddressingError Bool :=
  scope.coversDeclaredFieldExtent model source.declaration.path source.reopenedScope outer missingParent

/-- A parser-independent `SumOfProducts` pair. Each operand retains its authored wildcard path and an optional correlated filter; the checked carrier accepts only two unfiltered Number paths with the measured lowest-level star shape. Groups remain unrepresentable here. -/
structure SurfaceNumericProductAggregate where
  left : SurfaceStarFieldPath
  right : SurfaceStarFieldPath
  leftHaving : Option SurfaceCorrelatedHaving := none
  rightHaving : Option SurfaceCorrelatedHaving := none
  leftKey : Option SurfaceSemanticIndexKey := none
  rightKey : Option SurfaceSemanticIndexKey := none
  deriving Repr, DecidableEq

/-- Fail-closed errors specific to the paired-row aggregate boundary. -/
inductive NumericProductAggregateElabError where
  | source (error : StarNumberElabError)
  | differentGroups (left right : GroupPath)
  | noWildcard (path : List String)
  /-- A repeatable level the operand reads per row, from a rule whose error field lies outside the
  declaring group, so the declaring group binds none of it. -/
  | levelOutsideRuleGroup (path : List String) (unbound : UnboundOperandLevel)
  | wildcardOnlyAtLowestLevel (path : List String)
  | wildcardAtLowestLevelRequired
  | repeatableLevelRequired
  | incompatibleTopology
  | keyed (error : KeyedEntityExtentError)
  deriving Repr, DecidableEq

/-- Exact Kernel class for each measured `SumOfProducts` refusal. Unresolved paths, kind errors, and the defensive topology branch remain deliberately unmapped. -/
def NumericProductAggregateElabError.diagnostic? :
    NumericProductAggregateElabError → Option KernelStaticDiagnostic
  | .differentGroups _ _ => some .differentGroups
  | .noWildcard _ => some .noWildcard
  | .levelOutsideRuleGroup _ unbound => unbound.diagnostic?
  | .wildcardOnlyAtLowestLevel _ => some .wildcardOnlyAtLowestLevelAllowed
  | .wildcardAtLowestLevelRequired => some .wildcardAtLowestLevelRequired
  | .repeatableLevelRequired => some .repeatableLevelRequired
  | .source (.path (.containmentBelowStar unbound)) => unbound.diagnostic?
  | .source _ | .incompatibleTopology | .keyed _ => none

/-- Two Number-star declarations certified against one model, one immediate owning group, one declaring scope that binds every unstarred repeatable ancestor, and one identical lowest-repeatable-star plan. Runtime row alignment follows from this shared plan rather than from zipping independently expanded lists. -/
structure CheckedRowNumericProductAggregate (model : FlatModel) where
  declaringGroup : GroupPath
  left : CheckedStarNumberSource model
  right : CheckedStarNumberSource model
  sameGroup : left.source.declaration.groupPath = right.source.declaration.groupPath
  lowestStar : left.source.path.firstStar + 1 = left.source.path.axes.length
  samePath : left.source.path = right.source.path
  bindingScopeBound :
    left.source.bindingScope.isPrefixOf
      (model.repeatableScopeForGroupPath declaringGroup) = true

private structure CheckedNumericProductOperand (model : FlatModel)
    (declaringGroup : GroupPath) where
  source : CheckedStarNumberSource model
  lowestStar : source.source.path.firstStar + 1 = source.source.path.axes.length
  bindingScopeBound :
    source.source.bindingScope.isPrefixOf
      (model.repeatableScopeForGroupPath declaringGroup) = true

private inductive NumericProductOperandShape (model : FlatModel)
    (declaringGroup : GroupPath) where
  | fixed (declaration : FlatFieldDecl)
  | starred (checked : CheckedNumericProductOperand model declaringGroup)

private def NumericProductOperandShape.groupPath :
    NumericProductOperandShape model declaringGroup → GroupPath
  | .fixed declaration => declaration.groupPath
  | .starred checked => checked.source.source.declaration.groupPath

/-- One operand as the reference reader leaves it: a field on no repeatable level, or a star path
the declaring scope binds above its first star. The reader answers as each operand is read — a name
resolving to nothing, containment below a star or outside the rule group, a repeatable level left
unstarred — so its classes come before the operator's own gates, which ask the pair. -/
private inductive NumericProductOperandRead (model : FlatModel) (declaringGroup : GroupPath) where
  | fixed (declaration : FlatFieldDecl)
  /-- An unstarred field whose every repeatable level the rule already binds, by its declaring group
  or by the error field or computation target holding the level: the reader admits the per-row
  read, and the operator's star gate refuses the missing lowest star. -/
  | unstarredBound (declaration : FlatFieldDecl)
  | starred (source : CheckedStarFieldPath model)
      (bindingScopeBound :
        source.bindingScope.isPrefixOf (model.repeatableScopeForGroupPath declaringGroup) = true)

private def NumericProductOperandRead.declaration :
    NumericProductOperandRead model declaringGroup → FlatFieldDecl
  | .fixed declaration => declaration
  | .unstarredBound declaration => declaration
  | .starred source _ => source.declaration

/-- Refuse a per-row read by containment when the rule's error field lies outside the declaring
group: the walk then binds none of the declaring group's levels
([`unboundReadLevel?`](../Flat/Model.lean)), measured on this operator's pairs
([inbound](../../../docs/sources/inbound-handbacks.md#inbound-2026-09-25e-sum-of-products-reach)). Inside it the
declaring group's binding is asked as before. -/
private def requireReadInsideRuleGroup (model : FlatModel)
    (declaringGroup writtenGroup : GroupPath) (path : List String) (scope : List RepeatableLevel) :
    Except NumericProductAggregateElabError Unit :=
  match WrittenFieldPlacement.of declaringGroup writtenGroup,
      model.unboundReadLevel? declaringGroup writtenGroup scope with
  | .outside, some unbound => throw (.levelOutsideRuleGroup path unbound)
  | _, _ => pure ()

private def readNumericProductOperand (model : FlatModel)
    (declaringGroup writtenGroup : GroupPath) (authored : SurfaceStarFieldPath) :
    Except NumericProductAggregateElabError (NumericProductOperandRead model declaringGroup) := do
  let declaration ← model.resolveFieldDeclaration declaringGroup authored.toFieldPath
    |>.mapError fun error => .source (.path (.resolve error))
  let read : Except StarPathElabError (CheckedStarFieldPath model) :=
    (elaborateStarFieldPath model declaringGroup authored).mapError
      (·.placeBelowStar model declaringGroup writtenGroup)
  let declaringScope := model.repeatableScopeForGroupPath declaringGroup
  match read with
  | .error (.missingWildcard _) =>
      if declaration.repeatableScope.isEmpty then pure (.fixed declaration)
      -- Bound by the rule, the class is the operator's own and needs no star anywhere in the pair
      -- ([inbound](../../../docs/sources/inbound-handbacks.md#src-inbound-2026-10-18), `SPEC-2026-10-14-08`).
      else if declaration.repeatableScope.all fun level => declaringScope.contains level ||
          (model.unboundOperandLevel declaringGroup writtenGroup level).writtenBound then
        pure (.unstarredBound declaration)
      else
        requireReadInsideRuleGroup model declaringGroup writtenGroup declaration.path
          declaration.repeatableScope
        throw (.noWildcard declaration.path)
  | .error (.iterationBelowWildcard path) => throw (.noWildcard path)
  | .error error => throw (.source (.path error))
  | .ok source =>
      requireReadInsideRuleGroup model declaringGroup writtenGroup source.declaration.path
        source.bindingScope
      if hBound : source.bindingScope.isPrefixOf
          (model.repeatableScopeForGroupPath declaringGroup) = true then
        pure (.starred source hBound)
      else
        throw (.noWildcard source.declaration.path)

/-- The operator's filter and star gates for one operand: a filtered operand and one leaving its
bound lowest level unstarred both lack the required lowest star, and only the path's lowest
repeatable level may be starred, a level the declaring scope binds counted too. -/
private def NumericProductOperandRead.requireLowestStar (having : Option SurfaceCorrelatedHaving) :
    NumericProductOperandRead model declaringGroup → Except NumericProductAggregateElabError Unit
  | operand => do
      if having.isSome then throw .wildcardAtLowestLevelRequired
      match operand with
      | .fixed _ => pure ()
      | .unstarredBound _ => throw .wildcardAtLowestLevelRequired
      | .starred source _ =>
          if source.path.firstStar + 1 = source.path.axes.length then pure ()
          else throw (.wildcardOnlyAtLowestLevel source.declaration.path)

/-- The Number question, asked of an operand only once the stars have passed. -/
private def NumericProductOperandRead.toShape :
    NumericProductOperandRead model declaringGroup →
      Except NumericProductAggregateElabError (NumericProductOperandShape model declaringGroup)
  | .fixed declaration =>
      match declaration.toNumberField? with
      | some _ => pure (.fixed declaration)
      | none => throw (.source (.fieldNotNumber declaration.path))
  | .unstarredBound _ => throw .wildcardAtLowestLevelRequired
  | .starred source hBound =>
      match hField : source.declaration.toNumberField? with
      | none => throw (.source (.fieldNotNumber source.declaration.path))
      | some field =>
          if hLowest : source.path.firstStar + 1 = source.path.axes.length then
            pure (.starred {
              source := { source, field, fieldOwned := hField }
              lowestStar := hLowest
              bindingScopeBound := hBound })
          else
            throw (.wildcardOnlyAtLowestLevel source.declaration.path)

/-- Read both operands, then ask the operator's chain in the Kernel's order: the owning groups, each
operand's filter and stars from the left, the Number question, and last whether any repeatable level
is crossed. The left-to-right order is measured with both operands starring two levels and one
filter ([inbound](../../../docs/sources/inbound-handbacks.md#src-inbound-2026-10-18)). Owning
groups before the stars, the filter before the stars and the stars before the Number question are
measured on a pair read from outside its fields' groups
([inbound](../../../docs/sources/inbound-handbacks.md#inbound-2026-09-25e-sum-of-products-reach)); owning groups before
the filter and before the repeatable level are measured separately
([inbound](../../../docs/sources/inbound-handbacks.md#inbound-2026-09-21-corrections)). Where the filter stands against
the repeatable-level gate is not measured, since only a filtered operand on no repeatable level would
separate them. -/
def elaborateRowNumericProductAggregate (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceNumericProductAggregate)
    (writtenGroup : GroupPath := declaringGroup) :
    Except NumericProductAggregateElabError
      (CheckedRowNumericProductAggregate model) := do
  if authored.leftKey.isSome || authored.rightKey.isSome then throw .incompatibleTopology
  let leftRead ← readNumericProductOperand model declaringGroup writtenGroup authored.left
  let rightRead ← readNumericProductOperand model declaringGroup writtenGroup authored.right
  if leftRead.declaration.groupPath != rightRead.declaration.groupPath then
    throw (.differentGroups leftRead.declaration.groupPath rightRead.declaration.groupPath)
  -- The filter and star gates are asked operand by operand from the left, so the left operand's
  -- stars answer before the right operand's filter is read (spec/07 §4).
  leftRead.requireLowestStar authored.leftHaving
  rightRead.requireLowestStar authored.rightHaving
  let left ← leftRead.toShape
  let right ← rightRead.toShape
  if hGroup : left.groupPath = right.groupPath then
    match hLeft : left, hRight : right with
    | .fixed _, .fixed _ => throw .repeatableLevelRequired
    | .starred left, .starred right =>
        if hPath : left.source.source.path = right.source.source.path then
          pure {
            declaringGroup
            left := left.source
            right := right.source
            sameGroup := by
              simpa [hLeft, hRight, NumericProductOperandShape.groupPath] using hGroup
            lowestStar := left.lowestStar
            samePath := hPath
            bindingScopeBound := left.bindingScopeBound }
        else
          throw .incompatibleTopology
    | _, _ => throw .incompatibleTopology
  else
    throw (.differentGroups left.groupPath right.groupPath)

namespace CheckedRowNumericProductAggregate

/-- `SumOfProducts` adds the two exact declaration scales, exactly like one checked multiplication. -/
def scaleSummary (checked : CheckedRowNumericProductAggregate model) :
    NumericScaleSummary :=
  NumericScaleSummary.binary .multiply
    (NumericScaleSummary.field checked.left.field.info.scale)
    (NumericScaleSummary.field checked.right.field.info.scale)

/-- Classify both declarations at each environment of the one shared canonical topology. -/
def selectedSideAt (checked : CheckedRowNumericProductAggregate model)
    (phase : Phase) (resolved : ResolvedStarTopology)
    (read : Env → FieldId → CheckedCell) : ResolvedNumericProductSide :=
  { rows := resolved.environments.map fun environment => {
      left := checked.left.checkedValueListCellAt phase read environment
      right := checked.right.checkedValueListCellAt phase read environment }
    leftSigned := checked.left.field.info.signed
    rightSigned := checked.right.field.info.signed
    hasUninstantiatedTail := resolved.domain.hasOpenTail }

/-- Resolve the common topology's in-capacity extent once and evaluate the paired-row fold in the requested phase, an over-limit pair contributing nothing on either arm ([checkpoint](../../../docs/sources/computation-scheduling-probes.md#src-row-star-scans)). -/
def evaluateAt (checked : CheckedRowNumericProductAggregate model)
    (phase : Phase) (document : Document) (outer : Env)
    (read : Env → FieldId → CheckedCell) :
    Except StarAddressingError NumericOperand := do
  let resolved ← checked.left.source.path.resolveInCapacity document outer
  pure (evalNumericProductAggregate (checked.selectedSideAt phase resolved read))

/-- Classify one product operand from the immutable checked input while retaining path-owned over-repetition. -/
private def checkedDocumentValueListCellAt
    (source : CheckedStarNumberSource model) (phase : Phase)
    (document : CheckedDocument model) (environment : Env) :
    Except CheckedAddressingError (ValueListCell .number) := do
  let addressed ← document.addressedCell environment source.field.id
  pure (source.checkedValueListCell phase addressed.cell environment)

/-- Resolve the in-capacity extent of the product's one certified topology against the immutable checked input, then read each left/right pair in kernel encounter order. -/
def evaluateCheckedDocumentAt (checked : CheckedRowNumericProductAggregate model)
    (phase : Phase) (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError NumericOperand := do
  let resolved ←
    (checked.left.source.path.resolveInCapacity document.source.toDocument outer)
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
private def checkedRawCell (checked : CheckedRowNumericProductAggregate model)
    (read : Env → FieldId → RawCell) (environment : Env)
    (field : FieldId) : CheckedCell :=
  if field == checked.left.field.id then
    checked.left.source.declaration.checkRaw (read environment field)
  else if field == checked.right.field.id then
    checked.right.source.declaration.checkRaw (read environment field)
  else
    malformedCheckedCell

/-- Full validation checks raw cells through the two certified declarations and uses the validation face of formal invalidity. -/
def evaluateValidation (checked : CheckedRowNumericProductAggregate model)
    (document : Document) (outer : Env)
    (read : Env → FieldId → RawCell) :
    Except StarAddressingError NumericOperand :=
  checked.evaluateAt .validation document outer (checked.checkedRawCell read)

/-- Partial products share the declared-capacity gate with independently selected products;
the numeric fold still consumes only instantiated rows (spec/07 §4). -/
def evaluatePartial (checked : CheckedRowNumericProductAggregate model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → RawCell) :
    Except StarAddressingError PartialValidationNumberAggregateResult := do
  if !(← checked.left.source.productExtentRelevant scope outer) ||
      !(← checked.right.source.productExtentRelevant scope outer) then return .nonRelevant
  let resolved ← checked.left.source.path.resolveInCapacity document outer
  pure (.evaluated (evalNumericProductAggregate
    (checked.selectedSideAt .validation resolved (checked.checkedRawCell read))))

end CheckedRowNumericProductAggregate

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
  ({ values := source.resolvedValueSide observe, sum := source.resolvedSumSide observe } :
    ResolvedNumberEntityAggregateSides).evaluate op

def referencesField (source : ResolvedNumericAggregateFields)
    (field : FieldId) : Bool :=
  source.fields.any fun candidate => candidate.id == field

def allRelevant (source : ResolvedNumericAggregateFields)
    (isRelevant : FlatRelevance) : Bool :=
  source.fields.all fun field => isRelevant field.id

end ResolvedNumericAggregateFields

private def FlatModel.resolveNumericAggregateDeclaration (model : FlatModel)
    (declaringGroup writtenGroup : GroupPath) (reference : SurfaceFieldPath) :
    Except NumericAggregateElabError FlatFieldDecl :=
  (model.resolveNonrepeatableFieldUnchecked declaringGroup reference writtenGroup).mapError .resolve

private def numericAggregateField (declaration : FlatFieldDecl) :
    Except NumericAggregateElabError FlatNumberField :=
  match declaration.toNumberField? with
  | some field => pure field
  | none =>
      throw (.fieldKindMismatch declaration.path declaration.policy.kind.surfaceKind)

private def FlatModel.resolveNumericAggregateDeclarations (model : FlatModel)
    (declaringGroup writtenGroup : GroupPath) :
    List SurfaceFieldPath → Except NumericAggregateElabError (List FlatFieldDecl)
  | [] => pure []
  | reference :: remaining => do
      pure ((← model.resolveNumericAggregateDeclaration declaringGroup writtenGroup reference) ::
        (← model.resolveNumericAggregateDeclarations declaringGroup writtenGroup remaining))

private def numericAggregateFields :
    List FlatFieldDecl → Except NumericAggregateElabError (List FlatNumberField)
  | [] => pure []
  | declaration :: remaining => do
      pure ((← numericAggregateField declaration) ::
        (← numericAggregateFields remaining))

/-- Validate the model once, require at least two direct fields, resolve every source in authored order, and certify the complete Number list. -/
def elaborateNumericAggregateFields (model : FlatModel) (declaringGroup : GroupPath)
    (authored : SurfaceNumericAggregateFields) (writtenGroup : GroupPath) :
    Except NumericAggregateElabError (CheckedNumericAggregateFields model) :=
  match hModel : model.validate with
  | .error error => .error (.resolve error)
  | .ok () =>
      match authored.rest with
      | [] => .error .tooFewFields
      | secondReference :: remainingReferences => do
          let firstDeclaration ←
            model.resolveNumericAggregateDeclaration declaringGroup writtenGroup authored.first
          let secondDeclaration ←
            model.resolveNumericAggregateDeclaration declaringGroup writtenGroup secondReference
          let remainingDeclarations ← model.resolveNumericAggregateDeclarations declaringGroup
            writtenGroup remainingReferences
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
