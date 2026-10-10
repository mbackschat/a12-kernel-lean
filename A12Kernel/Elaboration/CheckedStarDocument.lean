import A12Kernel.Elaboration.SemanticIndex
import A12Kernel.Elaboration.RuleIterationDomain
import A12Kernel.Elaboration.ConstructedDateEvaluation
import A12Kernel.Semantics.CustomCondition
import A12Kernel.Elaboration.CheckedGroupPresence
import A12Kernel.Elaboration.StarPath
import A12Kernel.Semantics.Correlation
import A12Kernel.Semantics.NumericAggregate

/-! # Checked-document projection over one resolved starred field

This boundary joins the immutable checked input to the existing checked star path and topology without reconstructing either owner. It is deliberately one-field-wide: authored multi-operand ordering, filters, relevance, and consumer-specific classification remain with their established owners and SG2.
-/

namespace A12Kernel

/-- Missing filter coordinates read empty; concrete coordinates retain the caller's phase and
completed-target overlay. No row is added to the source document (KF528). -/
def FlatModel.filterRead (model : FlatModel) (document : Document)
    (read : Env → FieldId → CheckedCell) (environment : Env) (field : FieldId) : CheckedCell :=
  match (model.lookupUniqueId field).toOption with
  | none => malformedCheckedCell
  | some declaration => match (environment.pathForScope declaration.repeatableScope).toOption with
      | none => malformedCheckedCell
      | some path =>
          if (repeatableAncestorRowsFor declaration.repeatableScope path).all document.instantiatedRows.contains
          then read environment field else checkAdmittedRawCell .empty


/-- Raw-document consumers retain filter failures in their existing addressing channel. Missing
capabilities refuse at the reached leaf rather than turning a failed filter into UNKNOWN. -/
def CorrelationContext.asStarResolving (context : CorrelationContext) :
    ResolvingCorrelationContext StarAddressingError :=
  let failure : CorrelationRuntimeFault → StarAddressingError
    | .calendarUnavailable => .unsupportedDateCalendar
    | .valueFailure => .temporalValueFailure
    | .worldUnavailable => .worldUnavailable
    | .typeValidityValueFailure => .typeValidityValueFailure
    | .stringExpressionUnavailable => .stringExpressionUnavailable
    | .storedTextUnavailable field => .storedTextUnavailable field
    | .groupUnavailable path => .unsupportedGroupOperand path
  { read := fun env field => pure (context.read env field)
    storedText := context.storedText
    numberText := context.numberText
    world := context.world
    bindingError := EnvBindingError.toStarAddressingError
    stringExpressionUnavailable := .stringExpressionUnavailable
    unsupportedDateCalendar := .unsupportedDateCalendar
    temporalValueFailure := .temporalValueFailure
    worldUnavailable := .worldUnavailable
    typeValidityValueFailure := .typeValidityValueFailure
    groupUnavailable := .unsupportedGroupOperand
    storedTextUnavailable := .storedTextUnavailable
    groups := context.groups.map fun groups => {
      validation := fun env reference => (groups.validation env reference).mapError failure
      computation := fun env source => (groups.computation env source).mapError failure
      fieldExtent := fun path env depth field => (groups.fieldExtent path env depth field).mapError failure
      groupExtent? := groups.groupExtent?.map fun extent path env selection =>
        (extent path env selection).mapError failure } }

inductive CheckedAddressingError where
  | temporalValueFailure
  | worldUnavailable
  | typeValidityValueFailure
  | customCondition (cause : CustomConditionLookupError)
  | unsupportedIndexedFillQuantifier
  | semanticIndex (cause : SemanticIndexContextError)
  | indexPreliminary (cause : CheckedIndexPreliminaryError)
  | stringExpression (cause : StringComputationFault)
  | temporalUnavailable
  | constructedDate (cause : ConstructedDateEvaluationFault)
  | addressing (cause : StarAddressingError)
  | group (cause : CheckedGroupPresenceError)
  | field (field : FieldId) (cause : ResolveError)
  | environment (cause : EnvBindingError)
  | document (cause : CheckedDocumentError)
  | rowEnvironment (cause : ActualRowEnvironmentError)
  | checkedDocumentRequired (path : GroupPath)
  | repetitionNotUniqueResult (row : Env)
  | partialUnavailable (row : Env) (field : FieldId)
  | filteredFieldFillComputation
  /-- A certified operand's stored payload contradicted the declaration that certified it. No
  checked certificate can produce one, so this class exists to be *reported* rather than skipped:
  a family whose standalone evaluation names such a payload and whose condition-leaf evaluation
  silently dropped it would be two accounts of one certificate. -/
  | operandPayload (address : CellAddr)
  deriving Repr, DecidableEq

def CheckedAddressingError.isFilterValueFailure : CheckedAddressingError → Bool
  | .temporalValueFailure | .typeValidityValueFailure
  | .stringExpression .emptyPattern => true
  | .addressing error => error.isFilterValueFailure
  | _ => false

/-- A model-independent computation context asks its checked document to resolve a column;
the document retains index preparation and exact selected addresses. -/
abbrev SemanticIndexColumnReader := RepeatableGroupDecl → FieldId → Env →
  Except CheckedAddressingError ResolvedSemanticIndexColumn

/-- Read a certified key and target through one phase-aware selection path. The column reader
retains current computed payloads; `spec/08` §4.2 owns per-lookup versus per-column failure. -/
def CheckedSemanticIndexSource.observeColumnWith (source : CheckedSemanticIndexSource model)
    (phase : Phase) (readColumn : SemanticIndexColumnReader) (outer : Env)
    (read : FieldId → CheckedCell) (stored : FieldId → Option String) :
    Except CheckedAddressingError CellObservation := do
  let column ← readColumn source.group source.targetDeclaration.id outer
  let key ← source.observeCurrentKey phase read stored |>.mapError .semanticIndex
  pure (column.lookupObservationForIndex phase source.numericIndex key)

/-- Select a concrete row through the phase-aware index column without reading its target.
A scalar-only column cannot supply a row and is a structural failure, not an absent key. -/
def CheckedSemanticIndexSource.selectEnvironmentWith (source : CheckedSemanticIndexSource model)
    (phase : Phase) (readColumn : SemanticIndexColumnReader) (outer : Env)
    (read : FieldId → CheckedCell) (stored : FieldId → Option String) :
    Except CheckedAddressingError (CellObservation Env) := do
  let column ← readColumn source.group source.indexDeclaration.id outer
  let key ← source.observeCurrentKey phase read stored |>.mapError .semanticIndex
  match column.lookupEnvironment phase source.numericIndex key with
  | .value (some environment) => pure (.value environment)
  | .value none => throw (.checkedDocumentRequired source.group.path)
  | .empty => pure .empty
  | .unknown cause => pure (.unknown cause)
  | .poison cause => pure (.poison cause)

/-- Compatibility name for the original one-star projection API. -/
abbrev CheckedStarDocumentError := CheckedAddressingError

/-- One topology-produced field instance with its complete environment, derived physical address, exact stored payload, and cached checked cell. `none` stored text is physical absence; `some ""` is a present empty cell. -/
structure CheckedAddressedCell where
  environment : Env
  address : CellAddr
  stored : Option String
  cell : CheckedCell
  deriving Repr, DecidableEq

/-- The original hierarchical topology plus the checked cells read in exactly its canonical environment order. The constructor is private so callers cannot pair an unrelated topology and cell list. -/
structure ResolvedCheckedStarField where
  private mk ::
  topology : ResolvedStarTopology
  cells : List CheckedAddressedCell

/-- Kind-neutral addressed content for one checked entity-list operand. Family owners retain the typed declaration and project these cached cells; this core owns only canonical topology, addressing, filter selection, omitted-tail extent, and positional relevance. -/
structure ResolvedCheckedEntityOperandCore where
  private mk ::
  topology : Option ResolvedStarTopology
  addressedCells : List CheckedAddressedCell
  hasUninstantiatedTail : Bool
  hasHaving : Bool
  hasNonRelevant : Bool

namespace ResolvedCheckedEntityOperandCore

/-- A direct or starred operand masked by partial-validation relevance. -/
def nonRelevant : ResolvedCheckedEntityOperandCore := {
  topology := none
  addressedCells := []
  hasUninstantiatedTail := false
  hasHaving := false
  hasNonRelevant := true
}

/-- A filtered operand suppressed by the owning partial-validation rule gate. -/
def skippedHaving : ResolvedCheckedEntityOperandCore := {
  topology := none
  addressedCells := []
  hasUninstantiatedTail := false
  hasHaving := true
  hasNonRelevant := false
}

/-- Project away cells beneath a declared-capacity violation. The checked document and base topology retain those formal cells, while star and group operand cores already leave their over-limit rows out when they resolve. -/
def inCapacityAddressedCells (resolved : ResolvedCheckedEntityOperandCore) :
    List CheckedAddressedCell :=
  resolved.addressedCells.filter fun addressed =>
    !addressed.cell.findings.contains .overRepetition

end ResolvedCheckedEntityOperandCore

/-- The in-capacity environments at which a group operand reaches one declaration of repeatable scope
`scope`, the operand fixing the scope's first `boundCount` levels at `outer`'s bindings and reopening
every deeper one. The reopened levels resolve as a star does, through `StarPath.resolveInCapacity`, so
a group operand and a star share one extent and one canonical row order; a scope `outer` fixes
completely is its one row when that row is instantiated and in capacity. Every group operand's cell
walk, on the checked document and on the reader route, takes its rows from here; a fixed group below a
star and a group count's bound instance read their own instance environments instead. A scope the model
declares no repeatable axes for, which a certified operand cannot carry, is refused as the deepest
level's invalid repeatability. -/
def FlatModel.groupOperandExtent (model : FlatModel) (document : Document) (outer : Env)
    (boundCount : Nat) (scope : List RepeatableLevel) : Except StarAddressingError (List Env × Bool) := do
  if scope.isEmpty then return ([[]], false)
  let axes ← match model.repeatableAxesForScope? scope with
    | some axes => pure axes
    | none => throw (.invalidRepeatability (scope.getLast?.getD 0))
  let (environments, omitted) ← StarAxes.resolveOperandExtent axes document outer boundCount
  if scope.length ≤ boundCount && environments.isEmpty then
    let path ← (outer.pathForScope scope).mapError (·.toStarAddressingError)
    -- A bound declaration still has one declared slot when its in-capacity row is absent.
    -- Fill predicates must agree with its direct-field spelling (spec/07 §5); the row walk
    -- remains empty so consumers that ignore omissions retain their instantiated domain.
    return (environments, !StarAxes.environmentOverLimit axes (scope.zip path))
  return (environments, omitted)

def FlatModel.groupOperandEnvironments (model : FlatModel) (document : Document) (outer : Env)
    (boundCount : Nat) (scope : List RepeatableLevel) : Except StarAddressingError (List Env) :=
  Prod.fst <$> model.groupOperandExtent document outer boundCount scope

/-- Whether any repeatable scope a group operand reopens retains **declared but uninstantiated**
capacity at the operand's own depth, read off the same star topology `groupOperandEnvironments`
resolves. A scope no deeper than that depth contributes nothing: `outer` fixes all of its levels. -/
def FlatModel.groupOperandUninstantiatedTail (model : FlatModel) (document : Document) (outer : Env)
    (boundCount : Nat) (scopes : List (List RepeatableLevel)) : Except StarAddressingError Bool := do
  let tails ← scopes.eraseDups.mapM fun scope => do
    if scope.length ≤ boundCount then return false
    let axes ← match model.repeatableAxesForScope? scope with
      | some axes => pure axes
      | none => throw (.invalidRepeatability (scope.getLast?.getD 0))
    return (← ({ axes, firstStar := boundCount } : StarPath).resolveTopology document outer).domain.hasOpenTail
  return tails.any id

/-- Every row a group operand's declarations reach, declaration-major: each declaration paired with
each of its environments, so a consumer reads each cell through the declaration that stored it. The
checked document's walk and the reader route's both take their rows from here. -/
def FlatModel.groupOperandRows (model : FlatModel) (document : Document) (outer : Env)
    (boundCount : Nat) (declarations : List α) (scope : α → List RepeatableLevel) :
    Except StarAddressingError (List (α × Env)) := do
  let rows ← declarations.mapM fun declaration => do
    let environments ← model.groupOperandEnvironments document outer boundCount (scope declaration)
    pure (environments.map (declaration, ·))
  pure rows.flatten

/-- A group operand's rows on the reader route, with whether any of its scopes leaves declared
capacity open. -/
def FlatModel.groupOperandReads (model : FlatModel) (document : Document) (outer : Env)
    (boundCount : Nat) (declarations : List α) (scope : α → List RepeatableLevel) :
    Except StarAddressingError (List (α × Env) × Bool) := do
  pure (← model.groupOperandRows document outer boundCount declarations scope,
    ← model.groupOperandUninstantiatedTail document outer boundCount (declarations.map scope))

namespace CheckedDocument

/-- Resolve one model-owned field instance to its exact address without reading its cell. -/
def cellAddress (_checked : CheckedDocument model)
    (environment : Env) (field : FieldId) :
    Except CheckedAddressingError CellAddr := do
  let declaration ←
    (model.lookupUniqueId field).mapError (.field field)
  let path ←
    (environment.pathForScope declaration.repeatableScope)
      |>.mapError .environment
  pure { field, path }

/-- Read one model-owned field instance through a caller-supplied exact-address view. -/
def checkedCellWithRead (checked : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (environment : Env) (field : FieldId) :
    Except CheckedAddressingError CheckedCell := do
  let address ← checked.cellAddress environment field
  read address |>.mapError .document

/-- Retain exact spelling for a supplied checked cell: unchanged cells use stored input and
changed text-bearing payloads carry it themselves. Parsed temporal values cannot recover spelling
(spec/07 temporal uniqueness and spec/08 exact index identity). -/
def storedTextForCell (checked : CheckedDocument model) (address : CellAddr)
    (cell : CheckedCell) : Option String :=
  if (checked.read address).toOption == some cell then
    checked.storedTextAt address
  else match cell.parsed with
    | some (.str text) | some (.enum text) | some (.partialDate text) => some text
    | _ => none

/-- A changed parsed-only payload requires a document overlay; reusing backing text would select
by a stale key (spec/08 exact index identity). -/
def storedTextWithRead (checked : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (environment : Env) (field : FieldId) : Option String := do
  let address ← (checked.cellAddress environment field).toOption
  checked.storedTextForCell address (← (read address).toOption)

/-- Formal Number text belongs to its checked placement (spec/09 §3). An unchanged read may
reuse it; a changed parsed rational needs an overlay carrying its own text, never a stale spelling. -/
def numberTextWithRead (checked : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (environment : Env) (field : FieldId) : Option String := do
  let address ← (checked.cellAddress environment field).toOption
  let cell ← (read address).toOption
  if (checked.read address).toOption != some cell then none
  else (← (checked.readNumberFormalText address).toOption).parsed

/-- Keep generated index preparation while reading selected computation payloads from the current
dependency view. An index field itself uses its prepared cell because computation targets cannot
be index fields (`spec/09`). -/
def resolveSemanticIndexColumnWith (checked : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell) : SemanticIndexColumnReader :=
  fun group target outer => do
    let preliminary ← checked.applySelectedFullIndexPreliminary group.indexField.toList
      |>.mapError .indexPreliminary
    let column ← preliminary.resolveIndexColumn group outer
      |>.mapError (CheckedAddressingError.semanticIndex ∘ SemanticIndexContextError.checkedColumn)
    column.toSemanticIndexColumnWith
      (if group.indexField == some target then preliminary.readComputation else read) target
      |>.mapError (CheckedAddressingError.semanticIndex ∘ SemanticIndexContextError.checkedColumn)

/-- Supply prepared columns without binding selected target reads to the immutable document. -/
def indexedComputationFillContext (checked : CheckedDocument model) : ComputationFillContext :=
  { checked.computationFillContext with
    indexColumn := fun level outer => do
      let group ← model.repeatableGroupAtLevel? level
      let index ← group.indexField
      (checked.resolveSemanticIndexColumnWith checked.read group index outer).toOption }

def indexedComputationContextAt (checked : CheckedDocument model) (environment : Env) : ScalarComputationContext :=
  { checked.computationContextAt environment with addressed := some checked.indexedComputationFillContext }

def indexedScalarComputationContext (checked : CheckedDocument model) (world : World) : ScalarComputationContext :=
  { checked.scalarComputationContext world with addressed := some checked.indexedComputationFillContext }

/-- One field's checked cell at an environment through a caller-supplied exact-address view, the
computation scans' read. An address the environment cannot form reads as malformed: each scanning
carrier's binding certificate makes that unreachable, so no semantic channel carries it. -/
def computationCellAt (checked : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (environment : Env) (field : FieldId) : CheckedCell :=
  match checked.checkedCellWithRead read environment field with
  | .ok cell => cell
  | .error _ => malformedCheckedCell

/-- Retain one model-owned field instance under its exact immutable address and stored payload while observing its checked cell through a caller-supplied exact-address view. -/
def addressedCellWithRead (checked : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (environment : Env) (field : FieldId) :
    Except CheckedAddressingError CheckedAddressedCell := do
  let address ← checked.cellAddress environment field
  let cell ← (read address).mapError .document
  pure {
    environment
    address
    stored := checked.storedTextAt address
    cell
  }

/-- Read one model-owned field instance from a complete environment. The declaration selects its named repeatable scope; environment order and unrelated deeper bindings cannot change the address. -/
def addressedCell (checked : CheckedDocument model)
    (environment : Env) (field : FieldId) :
    Except CheckedAddressingError CheckedAddressedCell :=
  checked.addressedCellWithRead checked.read environment field

private def validationAddressedCellWithRows (checked : CheckedDocument model)
    (rows : List RepeatableLevel → Except ActualRowEnvironmentError (List Env))
    (environment : Env) (field : FieldId) :
    Except CheckedAddressingError CheckedAddressedCell := do
  let declaration ←
    (model.lookupUniqueId field).mapError (.field field)
  let path ←
    (environment.pathForScope declaration.repeatableScope)
      |>.mapError .environment
  let address : CellAddr := { field, path }
  if declaration.repeatableScope.isEmpty then
    checked.addressedCell environment field
  else
    let validationRows ←
      (rows declaration.repeatableScope)
        |>.mapError .rowEnvironment
    let projected := declaration.repeatableScope.zip path
    let physical :=
      (repeatableAncestorRowsFor declaration.repeatableScope path).all
        checked.source.instantiatedRows.contains
    if !validationRows.contains projected || physical then
      checked.addressedCell environment field
    else
      let overLimit ← match model.addressOverLimit?
          declaration.repeatableScope path with
        | some overLimit => pure overLimit
        | none => throw (.document
            (.incoherentRepeatableScope declaration.repeatableScope))
      pure {
        environment
        address
        stored := none
        cell := (checkAdmittedRawCell .empty).withOverRepetitionIf overLimit
      }

/-- The legacy nested/partial validation view admits only its own implicit descendants. -/
def validationAddressedCell (checked : CheckedDocument model)
    (environment : Env) (field : FieldId) :
    Except CheckedAddressingError CheckedAddressedCell :=
  checked.validationAddressedCellWithRows checked.validationRowEnvironments environment field

/-- Full validation admits exactly the shared rule domain's implicit coordinates while
preserving physical checked cells and structural failures outside that domain. -/
def fullValidationAddressedCell (checked : CheckedDocument model)
    (environment : Env) (field : FieldId) :
    Except CheckedAddressingError CheckedAddressedCell :=
  checked.validationAddressedCellWithRows checked.fullValidationRowEnvironments environment field

end CheckedDocument

/-- Group filters use the same exact-address view as fields. Enumerating model-owned positions includes values computed into previously absent cells; immutable rows still own structural content (spec/02 and spec/09). -/
def FlatModel.correlationGroupsWithRead (model : FlatModel) (document : Document)
    (read : Env → FieldId → Except CheckedAddressingError CheckedCell) :
    CorrelationGroupReads CheckedAddressingError where
  groupExtent? := some fun _ environment path =>
    (path.inCapacityEnvironments document environment).mapError .addressing
  validation environment reference := do
    let base ← (model.groupPresenceInputFromSlice document.instantiatedRows [] reference.path environment .fullyRelevant false).mapError .group
    let addressPrefix ← (environment.pathForScope (model.repeatableScopeForGroupPath reference.path)).mapError .environment
    let cells ← (model.groupSubtreeFields reference.path).mapM fun declaration => do
      let environments ← if declaration.repeatableScope.isEmpty then pure [[]]
        else (model.actualRowEnvironments document.instantiatedRows declaration.repeatableScope).mapError .rowEnvironment
      let selected := environments.filter fun env => addressPrefix.isPrefixOf (env.map (·.2))
      selected.mapM fun env => read env declaration.id
    pure ({ base with descendantCells := cells.flatten }.derive)
  computation environment source :=
    source.content.readWith document read .environment environment
  fieldExtent _ environment boundCount field := do
    let declaration ← (model.lookupUniqueId field).mapError (.field field)
    (model.groupOperandExtent document environment boundCount declaration.repeatableScope).mapError .addressing

private def FlatModel.correlationFieldExtent (model : FlatModel) (document : Document)
    (unavailable : GroupPath → Error) (path : GroupPath) (environment : Env) (boundCount : Nat)
    (field : FieldId) : Except Error (List Env × Bool) := do
  let declaration ← (model.lookupUniqueId field).mapError (fun _ => unavailable path)
  (model.groupOperandExtent document environment boundCount declaration.repeatableScope).mapError (fun _ => unavailable path)

/-- Model ownership supplies extent topology while the caller retains its phase-specific cell
view. The semantic-only adapter cannot infer a field's repeatable scope from its id. -/
def CorrelationContext.withModelComputationGroups (context : CorrelationContext)
    (model : FlatModel) (document : Document) : CorrelationContext :=
  let context := context.withComputationGroups document
  { context with groups := context.groups.map fun groups =>
    { groups with
      groupExtent? := some fun path environment selection =>
        (selection.inCapacityEnvironments document environment).mapError (fun _ => .groupUnavailable path)
      fieldExtent := model.correlationFieldExtent document CorrelationRuntimeFault.groupUnavailable } }

def ResolvingCorrelationContext.withModelComputationGroups (context : ResolvingCorrelationContext Error)
    (model : FlatModel) (document : Document) : ResolvingCorrelationContext Error :=
  let context := context.withComputationGroups document
  { context with groups := context.groups.map fun groups =>
    { groups with
      groupExtent? := some fun path environment selection =>
        (selection.inCapacityEnvironments document environment).mapError (fun _ => context.groupUnavailable path)
      fieldExtent := model.correlationFieldExtent document context.groupUnavailable } }

namespace CheckedDocument

def correlationGroupsWithRead (checked : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell) :
    CorrelationGroupReads CheckedAddressingError :=
  model.correlationGroupsWithRead checked.source.toDocument (checked.checkedCellWithRead read)

/-- Correlation reads through one caller-supplied exact-address view and preserve field/address failures separately from semantic UNKNOWN or computation poison. -/
def resolvingCorrelationContextWithRead (checked : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (world : Option World := none) :
    ResolvingCorrelationContext CheckedAddressingError where
  read environment field :=
    checked.checkedCellWithRead read environment field
  storedText := checked.storedTextWithRead read
  numberText := checked.numberTextWithRead read
  storedTextUnavailable := CheckedAddressingError.addressing ∘ StarAddressingError.storedTextUnavailable
  stringExpressionUnavailable := .addressing .stringExpressionUnavailable
  unsupportedDateCalendar := .temporalUnavailable
  temporalValueFailure := .temporalValueFailure
  worldUnavailable := .worldUnavailable
  typeValidityValueFailure := .typeValidityValueFailure
  groupUnavailable := .checkedDocumentRequired
  groups := some (checked.correlationGroupsWithRead read)
  world := world
  bindingError := .environment

/-- Correlation reads from the same immutable checked input. -/
def resolvingCorrelationContext (checked : CheckedDocument model)
    (world : Option World := none) :
    ResolvingCorrelationContext CheckedAddressingError :=
  { read := fun environment field =>
      (checked.fullValidationAddressedCell environment field).map (·.cell)
    storedText := checked.storedTextIn
    numberText := checked.computationFillContext.numberText
    storedTextUnavailable := CheckedAddressingError.addressing ∘ StarAddressingError.storedTextUnavailable
    stringExpressionUnavailable := .addressing .stringExpressionUnavailable
    unsupportedDateCalendar := .temporalUnavailable
    temporalValueFailure := .temporalValueFailure
    worldUnavailable := .worldUnavailable
    typeValidityValueFailure := .typeValidityValueFailure
    groupUnavailable := .checkedDocumentRequired
    groups := some (checked.correlationGroupsWithRead checked.read)
    world := world
    bindingError := .environment }

/-- Resolve one direct entity-list occurrence through the same model-owned address query as every starred occurrence. -/
def resolveCheckedDirectEntityOperandCoreAt
    (checked : CheckedDocument model) (outer : Env) (field : FieldId) :
    Except CheckedAddressingError ResolvedCheckedEntityOperandCore := do
  let addressed ← checked.fullValidationAddressedCell outer field
  pure {
    topology := none
    addressedCells := [addressed]
    hasUninstantiatedTail := false
    hasHaving := false
    hasNonRelevant := false
  }

/-- The scalar instance: a direct operand read at the document root. A nonrepeatable declaration
addresses identically at every environment, so this is the same single-cell read every caller
performed before the row-aware form existed. -/
def resolveCheckedDirectEntityOperandCore
    (checked : CheckedDocument model) (field : FieldId) :
    Except CheckedAddressingError ResolvedCheckedEntityOperandCore :=
  checked.resolveCheckedDirectEntityOperandCoreAt [] field

/-- Walk a group operand's `(row × field)` extent, keeping each reached cell beside the payload its owning declaration carries.

    The pairing is the point. A carrier whose cell *meaning* depends on the declaration that stored the cell cannot recover it from a flat cell list: the token family's Enumeration slot reads through that declaration's own resolved projection, so two Enumeration declarations in one subtree classify the same stored text differently. Handing the payload back from the walk that produced the cell keeps that association structural instead of reconstructing it by field-identifier lookup, which would need a total fallback for a cell that cannot occur.

    `()` is the honest payload for a carrier whose projection is declaration-independent; `resolveCheckedGroupEntityOperandCore` below is exactly that instance.

    Only in-capacity rows are walked: the Kernel leaves an over-limit row out of a group operand's domain on every consumer measured, fixed and starred, on full and partial validation ([checkpoint](../../docs/sources/group-list-and-capacity-probes.md#src-group-capacity-consumers)), exactly as a star's operand stream does. A consumer that needs the physical rows reads the topology instead.

    `boundCount` is the **operand's own depth**, not the rule's. Levels above it stay fixed at `outer`'s bindings; every level from there down is enumerated whatever the rule iterates. Both halves are load-bearing and each fails differently: reading the depth off the rule would pin an operand that names an ancestor of the rule's group to the rule's row, and ignoring `outer` altogether would let a starred operand under a *bound* repeatable ancestor compare rows the star never reopened. -/
def resolveCheckedGroupEntityOperandPairs
    (checked : CheckedDocument model) (outer : Env) (boundCount : Nat)
    (slots : List (FlatFieldDecl × α)) :
    Except CheckedAddressingError (List (α × CheckedAddressedCell)) := do
  let rows ← (model.groupOperandRows checked.source.toDocument outer boundCount slots
    (·.1.repeatableScope)).mapError .addressing
  rows.mapM fun ((declaration, payload), environment) => do
    pure (payload, ← checked.addressedCell environment declaration.id)

/-- Whether any repeatable declaration this group operand reopens retains **declared but
uninstantiated** capacity, at the operand's own depth.

    The walk below enumerates only instantiated rows, so it cannot see this capacity itself and asks
    here. The tail is a fact about the operand, not about one consumer: kernel 30.8.1 keeps a
    `NumberOfValueInFields` over a group growable while a reopened row is still missing, on the
    Number and String arms as on the Boolean one
    ([checkpoint](../../docs/sources/group-list-and-capacity-probes.md#src-below-star-group-runtime)), and the temporal extrema's
    `given` flag reads the same omitted tail.

    A scope no deeper than the operand's own depth contributes nothing: every one of its levels is
    fixed by `outer`, so there is no reopened tail to be open. -/
def resolveCheckedGroupUninstantiatedTail
    (checked : CheckedDocument model) (outer : Env) (boundCount : Nat)
    (declarations : List FlatFieldDecl) :
    Except CheckedAddressingError Bool :=
  (model.groupOperandUninstantiatedTail checked.source.toDocument outer boundCount
    (declarations.map (·.repeatableScope))).mapError .addressing

/-- The `(row × field)` extent a group-scope operand reaches: every declaration in the group's subtree, at every instantiated row of that declaration's repeatable scope **below the operand's own depth**.

    **The enumeration comes from the model's repeatability and never from a star plan.** `spec/07` marks the scope rule as an observed contract rather than a derived one and warns that an implementation reusing its star machinery, or reading the extent off the rule's own iterating group or binding depth, gets it wrong. The environment is consulted only to fix the levels *above* the operand, never to choose the depth: a rule authored on a repeatable group whose operand names an ancestor still reaches that ancestor's whole extent.

    Cells are emitted declaration-major in stable model declaration order, with each declaration's canonical row order inside it. Fixed-group token `FirstFilledValue` observes declaration order; its terminal single-level starred-group fragment observes that every row of one declaration precedes every row of the next. Set-valued consumers remain insensitive to the order. A filter cannot attach to a group operand, so every cell is unfiltered.

    Only instantiated in-capacity rows are enumerated, so `hasUninstantiatedTail` comes from the declared
    capacity those rows leave open rather than from the walk. -/
def resolveCheckedGroupEntityOperandCore
    (checked : CheckedDocument model) (outer : Env) (boundCount : Nat)
    (declarations : List FlatFieldDecl) :
    Except CheckedAddressingError ResolvedCheckedEntityOperandCore := do
  let paired ← checked.resolveCheckedGroupEntityOperandPairs outer boundCount
    (declarations.map fun declaration => (declaration, ()))
  let hasUninstantiatedTail ←
    checked.resolveCheckedGroupUninstantiatedTail outer boundCount declarations
  pure {
    topology := none
    addressedCells := paired.map Prod.snd
    hasUninstantiatedTail
    hasHaving := false
    hasNonRelevant := false
  }


end CheckedDocument

/-- Observe a selected key in its phase's coordinate domain, preserving preliminary overlays.
Full validation may supply implicit coordinates; computation retains physical addressing
(spec/07 §1 and spec/08 §4.1–4.2). -/
def CheckedSemanticIndexSource.observePreparedKey (source : CheckedSemanticIndexSource model)
    (preliminary : CheckedIndexPreliminary model) (outer : Env) (phase : Phase) :
    Except CheckedAddressingError CellObservation := do
  let keyCell ← match source.key with
    | .literal .. => pure (checkAdmittedRawCell .empty)
    | .field declaration =>
        match phase with
        | .validation => do
            -- Full-rule coordinates can be implicit; retain the existing validation domain and preliminary overlays (spec/07 §1, spec/08 §4.1).
            let addressed ← preliminary.base.fullValidationAddressedCell outer declaration.id
            pure (preliminary.annotateCell addressed.address
              (preliminary.stagedCell addressed.address addressed.cell))
        | .computation => do
            let address ← preliminary.base.cellAddress outer declaration.id
            preliminary.readAuthoredValidation address |>.mapError .document
  source.observeCurrentKey phase (fun _ => keyCell)
    (preliminary.base.storedTextIn outer) |>.mapError .semanticIndex

/-- Full validation reads the selected target through the same checked preliminary column as counts.
The index owns generated findings; the document owns the current key spelling (`spec/08` §4.2). -/
def CheckedSemanticIndexSource.observeDocument (source : CheckedSemanticIndexSource model)
    (document : CheckedDocument model) (outer : Env) (phase : Phase) :
    Except CheckedAddressingError CellObservation := do
  let preliminary ← document.applySelectedFullIndexPreliminary [source.indexDeclaration.id]
    |>.mapError .indexPreliminary
  let column ← source.resolvePreliminaryColumn preliminary outer |>.mapError .semanticIndex
  let key ← source.observePreparedKey preliminary outer phase
  pure (column.lookupObservationForIndex phase source.numericIndex key)


namespace CheckedStarFieldPath

private def addressedCell (source : CheckedStarFieldPath model)
    (checked : CheckedDocument model) (environment : Env) :
    Except CheckedStarDocumentError CheckedAddressedCell :=
  checked.addressedCell environment source.declaration.id

/-- Resolve topology's in-capacity extent against the immutable checked document and observe each concrete leaf once through a caller-supplied exact-address view. Every caller is a computation-arm `FirstFilledValue`, which leaves an over-limit row out rather than reading it as poison ([checkpoint](../../docs/sources/computation-scheduling-probes.md#src-first-filled-capacity)). Exact environment and address remain owned by the immutable document; each leaf's stored text is its placement's, so a value an earlier plan step overlaid reads with its own rendering. -/
def resolveCheckedFieldWithRead (source : CheckedStarFieldPath model)
    (checked : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (outer : Env) :
    Except CheckedStarDocumentError ResolvedCheckedStarField := do
  let topology ←
    (source.path.resolveInCapacity checked.source.toDocument outer).mapError .addressing
  let cells ← topology.environments.mapM fun environment =>
    checked.addressedCellWithRead read environment source.declaration.id
  pure { topology, cells }

/-- Resolve the existing topology against the immutable checked document and read each concrete leaf once. No declared tail is materialized as an address, and every topology or document failure stays structural. -/
def resolveCheckedField (source : CheckedStarFieldPath model)
    (checked : CheckedDocument model) (outer : Env) :
    Except CheckedStarDocumentError ResolvedCheckedStarField :=
  source.resolveCheckedFieldWithRead checked checked.read outer

/-- Enumerate the finite declared slots under the bound prefix. `none` preserves missing capacity
as unavailable information. The filtered field-fill grid (2026-10-03) separates this domain from
instantiated topology and the cache-bounded filter domain. Ordinary full-validation coordinates
may themselves be declared empty slots (spec/07 §1); no physical row is required or created. -/
def declaredEnvironments? (source : CheckedStarFieldPath model)
    (_checked : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError (Option (List Env)) :=
  source.path.declaredEnvironments? outer |>.mapError .addressing

/-- Visit bounded filter coordinates without treating them as physical rows. The cache view is
whole-document for validation and programme-restricted for computation (KF528). Ordinary full
validation can bind a declared empty outer coordinate (spec/07 §1); binding legality does not
require that coordinate to be a stored row. -/
def filterEnvironments (source : CheckedStarFieldPath model)
    (checked : CheckedDocument model) (outer : Env) (sparse : Bool := true) :
    Except CheckedAddressingError (List Env) :=
  model.filterEnvironments source.path
    (checked.filterRows.getD checked.source.instantiatedRows) outer sparse |>.mapError .addressing

/-- Sparse-capable consumers retain the policy alongside candidates so filter rejection can
preserve initialization/reset search rather than collapsing to occupied physical leaves. -/
def filterTraversal (source : CheckedStarFieldPath model)
    (checked : CheckedDocument model) (outer : Env) (mode : FilterTraversalMode := .sparse) :
    Except CheckedAddressingError FilterTraversal :=
  model.filterTraversal source.path
    (checked.filterRows.getD checked.source.instantiatedRows) outer mode |>.mapError .addressing

/-- The caller selects traversal policy and payload consumption; the shared iterator owns
successor lookahead. Uniqueness and membership use the same addressed validation reads. -/
def scanValidationCells (source : CheckedStarFieldPath model)
    (having : CorrelatedHaving) (document : CheckedDocument model) (outer : Env)
    (consume : State → CheckedAddressedCell → State ⊕ Result)
    (state : State) (mode : FilterTraversalMode) (world : Option World := none) :
    Except CheckedAddressingError (State ⊕ Result) := do
  let traversal ← source.filterTraversal document outer mode
  let result ← having.scanValidationResolving
    (document.resolvingCorrelationContextWithRead document.readDeclared world) outer
    (fun state row => do
      let cell ← document.addressedCellWithRead document.readDeclared row source.declaration.id
      pure (consume state cell)) traversal.candidates state traversal.occupancy
  match result with
  | .exhausted next => pure (.inl next)
  | .terminated result => pure (.inr result)
  | .poison _ => throw (.checkedDocumentRequired source.declaration.path)

/-- Kernel `feldWerteNichtEindeutig` uses dense successor lookahead and stops at a duplicate.
The carrier supplies only its checked comparison identity (spec/07 §5). -/
def scanValidationUniqueness (source : CheckedStarFieldPath model)
    (having : CorrelatedHaving) (document : CheckedDocument model) (outer : Env)
    (classify : CheckedAddressedCell → ValueListCell kind)
    (state : ValuesNotUniqueScanState kind) (world : Option World := none) :
    Except CheckedAddressingError (ValuesNotUniqueScanState kind ⊕ Polarity) :=
  source.scanValidationCells having document outer (fun state cell => state.step true (classify cell))
    state .dense world

/-- Resolve one full-validation starred entity-list occurrence. Optional checked-filter ownership remains with the typed caller; this function owns the common filter-before-addressing projection and preserves reached failures structurally. -/
def resolveCheckedValidationEntityOperandCore
    (source : CheckedStarFieldPath model)
    (checked : CheckedDocument model) (outer : Env)
    (having : Option CorrelatedHaving)
    (world : Option World := none) (traversalMode : FilterTraversalMode := .requireSmall) :
    Except CheckedAddressingError ResolvedCheckedEntityOperandCore := do
  let topology ←
    (source.path.resolveInCapacity checked.source.toDocument outer).mapError .addressing
  let selected ← match having with
    | none => pure topology.environments
    | some condition => do
        let traversal ← source.filterTraversal checked outer traversalMode
        condition.selectEnvironmentsResolving
          (checked.resolvingCorrelationContextWithRead checked.readDeclared world) outer
          traversal.candidates traversal.occupancy
  let addressedCells ← selected.mapM fun environment =>
    checked.addressedCellWithRead (if having.isSome then checked.readDeclared else checked.read)
      environment source.declaration.id
  pure {
    topology := some topology
    addressedCells
    hasUninstantiatedTail := topology.domain.hasOpenTail
    hasHaving := having.isSome
    hasNonRelevant := false
  }

/-- Resolve one unfiltered starred occurrence under partial-validation relevance. Candidates are the in-capacity extent while only relevant concrete cells are addressed, and incomplete extent stays on this exact operand. -/
def resolveCheckedPartialValidationEntityOperandCore
    (source : CheckedStarFieldPath model)
    (checked : CheckedDocument model) (outer : Env)
    (scope : ValidationRelevanceScope) :
    Except CheckedAddressingError ResolvedCheckedEntityOperandCore := do
  let topology ←
    (source.path.resolveInCapacity checked.source.toDocument outer).mapError .addressing
  let relevant := topology.environments.filter fun environment =>
    source.cellRelevant scope environment
  let addressedCells ← relevant.mapM (source.addressedCell checked)
  pure {
    topology := some topology
    addressedCells
    hasUninstantiatedTail := topology.domain.hasOpenTail
    hasHaving := false
    hasNonRelevant := !source.valueListExtentRelevant scope outer
  }

end CheckedStarFieldPath

/-- Keep prepared index cells for an index-field target; other payloads use the current overlay.
Missing preparation or row identity is structural failure, never an empty selected value. -/
def ScalarComputationContext.semanticIndexColumnReader (context : ScalarComputationContext) : SemanticIndexColumnReader :=
  fun group target outer => do
    let some addressed := context.addressed | throw (.checkedDocumentRequired group.path)
    let some column := addressed.indexColumn group.level outer | throw (.checkedDocumentRequired group.path)
    if group.indexField == some target then return column
    let entries ← column.entries.mapM fun entry => do
      let some environment := entry.environment | throw (.checkedDocumentRequired group.path)
      pure { entry with target := addressed.read environment target }
    pure { column with entries }

/-- Existing checked evaluators may already own the prepared-column resolver. Retain its index
entries in the addressed context so nested temporal reads share the current payload overlay. -/
def ScalarComputationContext.withIndexColumnReader (context : ScalarComputationContext) (model : FlatModel)
    (column : SemanticIndexColumnReader) : ScalarComputationContext :=
  { context with addressed := context.addressed.map fun addressed =>
      { addressed with indexColumn := fun level outer => do
          let group ← model.repeatableGroupAtLevel? level
          let index ← group.indexField
          (column group index outer).toOption } }

end A12Kernel
