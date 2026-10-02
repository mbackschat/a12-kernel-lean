import A12Kernel.Elaboration.CheckedDocument
import A12Kernel.Elaboration.CheckedGroupPresence
import A12Kernel.Elaboration.StarPath
import A12Kernel.Semantics.Correlation

/-! # Checked-document projection over one resolved starred field

This boundary joins the immutable checked input to the existing checked star path and topology without reconstructing either owner. It is deliberately one-field-wide: authored multi-operand ordering, filters, relevance, and consumer-specific classification remain with their established owners and SG2.
-/

namespace A12Kernel

inductive CheckedAddressingError where
  | addressing (cause : StarAddressingError)
  | group (cause : CheckedGroupPresenceError)
  | field (field : FieldId) (cause : ResolveError)
  | environment (cause : EnvBindingError)
  | document (cause : CheckedDocumentError)
  | rowEnvironment (cause : ActualRowEnvironmentError)
  | checkedDocumentRequired (path : GroupPath)
  | repetitionNotUniqueResult (row : Env)
  | partialUnavailable (row : Env) (field : FieldId)
  /-- A certified operand's stored payload contradicted the declaration that certified it. No
  checked certificate can produce one, so this class exists to be *reported* rather than skipped:
  a family whose standalone evaluation names such a payload and whose condition-leaf evaluation
  silently dropped it would be two accounts of one certificate. -/
  | operandPayload (address : CellAddr)
  deriving Repr, DecidableEq

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
def FlatModel.groupOperandEnvironments (model : FlatModel) (document : Document) (outer : Env)
    (boundCount : Nat) (scope : List RepeatableLevel) : Except StarAddressingError (List Env) := do
  if scope.isEmpty then return [[]]
  let axes ← match model.repeatableAxesForScope? scope with
    | some axes => pure axes
    | none => throw (.invalidRepeatability (scope.getLast?.getD 0))
  if boundCount < scope.length then
    return (← ({ axes, firstStar := boundCount } : StarPath).resolveInCapacity document outer).environments
  let path ← (outer.pathForScope scope).mapError (·.toStarAddressingError)
  let environment := scope.zip path
  let instantiated := document.instantiatedRows.any fun row =>
    row.group == scope.getLast?.getD 0 && row.path == path
  return if instantiated && !StarAxes.environmentOverLimit axes environment then [environment] else []

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

/-- Read a field in a validation-produced row environment. Concrete addresses use the immutable checked document unchanged. An exact implicit nested-validation environment supplies a clean absent cell without creating physical row or stored content; an arbitrary missing environment still fails structurally. -/
def validationAddressedCell (checked : CheckedDocument model)
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
      (checked.validationRowEnvironments declaration.repeatableScope)
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

/-- Correlation reads through one caller-supplied exact-address view and preserve field/address failures separately from semantic UNKNOWN or computation poison. -/
def resolvingCorrelationContextWithRead (checked : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell) :
    ResolvingCorrelationContext CheckedAddressingError where
  read environment field :=
    checked.checkedCellWithRead read environment field
  bindingError := .environment

/-- Correlation reads from the same immutable checked input. -/
def resolvingCorrelationContext (checked : CheckedDocument model) :
    ResolvingCorrelationContext CheckedAddressingError :=
  checked.resolvingCorrelationContextWithRead checked.read

/-- Resolve one direct entity-list occurrence through the same model-owned address query as every starred occurrence. -/
def resolveCheckedDirectEntityOperandCoreAt
    (checked : CheckedDocument model) (outer : Env) (field : FieldId) :
    Except CheckedAddressingError ResolvedCheckedEntityOperandCore := do
  let addressed ← checked.validationAddressedCell outer field
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
  let perDeclaration ← slots.mapM fun (declaration, payload) => do
    let environments ← (model.groupOperandEnvironments checked.source.toDocument outer boundCount
      declaration.repeatableScope).mapError .addressing
    let cells ← environments.mapM (checked.addressedCell · declaration.id)
    pure (cells.map fun cell => (payload, cell))
  pure perDeclaration.flatten

/-- Whether any repeatable declaration this group operand reopens retains **declared but
uninstantiated** capacity, at the operand's own depth.

    The walk below enumerates only instantiated rows, so it cannot see this capacity itself and asks
    here. The tail is a fact about the operand, not about one consumer: kernel 30.8.1 keeps a
    `NumberOfValueInFields` over a group growable while a reopened row is still missing, on the
    Number and String arms as on the Boolean one
    ([checkpoint](../../docs/SOURCES.md#src-below-star-group-runtime)), and the temporal extrema's
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

/-- Resolve one full-validation starred entity-list occurrence. Optional checked-filter ownership remains with the typed caller; this function owns the common filter-before-addressing projection and preserves reached failures structurally. -/
def resolveCheckedValidationEntityOperandCore
    (source : CheckedStarFieldPath model)
    (checked : CheckedDocument model) (outer : Env)
    (having : Option CorrelatedHaving) :
    Except CheckedAddressingError ResolvedCheckedEntityOperandCore := do
  let topology ←
    (source.path.resolveInCapacity checked.source.toDocument outer).mapError .addressing
  let selected ← match having with
    | none => pure topology.environments
    | some condition =>
        condition.selectEnvironmentsResolving
          checked.resolvingCorrelationContext outer topology.environments
  let addressedCells ← selected.mapM (source.addressedCell checked)
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

end A12Kernel
