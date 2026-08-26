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

/-- Project away cells beneath a declared-capacity violation for consumers whose selected star domain excludes over-limit rows. The checked document and base topology retain those formal cells; each consumer must opt into this narrower evaluation domain explicitly. -/
def inCapacityAddressedCells (resolved : ResolvedCheckedEntityOperandCore) :
    List CheckedAddressedCell :=
  resolved.addressedCells.filter fun addressed =>
    !addressed.cell.findings.contains .overRepetition

end ResolvedCheckedEntityOperandCore

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

/-- Read one model-owned field instance from a complete environment. The declaration selects its named repeatable scope; environment order and unrelated deeper bindings cannot change the address. -/
def addressedCell (checked : CheckedDocument model)
    (environment : Env) (field : FieldId) :
    Except CheckedAddressingError CheckedAddressedCell := do
  let address ← checked.cellAddress environment field
  let cell ← (checked.read address).mapError .document
  pure {
    environment
    address
    stored := checked.source.toDocument.rawCells address
    cell
  }

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

    `boundCount` is the **operand's own depth**, not the rule's. Levels above it stay fixed at `outer`'s bindings; every level from there down is enumerated whatever the rule iterates. Both halves are load-bearing and each fails differently: reading the depth off the rule would pin an operand that names an ancestor of the rule's group to the rule's row, and ignoring `outer` altogether would let a starred operand under a *bound* repeatable ancestor compare rows the star never reopened. -/
def resolveCheckedGroupEntityOperandPairs
    (checked : CheckedDocument model) (outer : Env) (boundCount : Nat)
    (slots : List (FlatFieldDecl × α)) :
    Except CheckedAddressingError (List (α × CheckedAddressedCell)) := do
  let perDeclaration ← slots.mapM fun (declaration, payload) => do
    let bound := declaration.repeatableScope.take boundCount
    let boundPath ← (outer.pathForScope bound).mapError .environment
    let environments ←
      if declaration.repeatableScope.isEmpty then
        pure [([] : Env)]
      else do
        let reached ←
          (checked.actualRowEnvironments declaration.repeatableScope).mapError
            CheckedAddressingError.rowEnvironment
        pure (reached.filter fun environment =>
          environment.take bound.length == bound.zip boundPath)
    let cells ← environments.mapM (checked.addressedCell · declaration.id)
    pure (cells.map fun cell => (payload, cell))
  pure perDeclaration.flatten

/-- The `(row × field)` extent a group-scope operand reaches: every declaration in the group's subtree, at every instantiated row of that declaration's repeatable scope **below the operand's own depth**.

    **The enumeration comes from the model's repeatability and never from a star plan.** `spec/07` marks the scope rule as an observed contract rather than a derived one and warns that an implementation reusing its star machinery, or reading the extent off the rule's own iterating group or binding depth, gets it wrong. The environment is consulted only to fix the levels *above* the operand, never to choose the depth: a rule authored on a repeatable group whose operand names an ancestor still reaches that ancestor's whole extent.

    Cells are emitted declaration-major in stable model declaration order, with each declaration's canonical row order inside it. Fixed-group token `FirstFilledValue` observes declaration order; its terminal single-level starred-group fragment observes that every row of one declaration precedes every row of the next. Set-valued consumers remain insensitive to the order. A filter cannot attach to a group operand, so every cell is unfiltered.

    `hasUninstantiatedTail` is `false` because only instantiated rows are enumerated. A consumer that needs declared-tail fillability must determine it separately: checked Boolean validation does so from every selected declaration's scope, while the measured checked-computation group carriers restrict their admitted shapes and consume only this concrete projection. -/
def resolveCheckedGroupEntityOperandCore
    (checked : CheckedDocument model) (outer : Env) (boundCount : Nat)
    (declarations : List FlatFieldDecl) :
    Except CheckedAddressingError ResolvedCheckedEntityOperandCore := do
  let paired ← checked.resolveCheckedGroupEntityOperandPairs outer boundCount
    (declarations.map fun declaration => (declaration, ()))
  pure {
    topology := none
    addressedCells := paired.map Prod.snd
    hasUninstantiatedTail := false
    hasHaving := false
    hasNonRelevant := false
  }

end CheckedDocument

namespace CheckedStarFieldPath

private def addressedCell (source : CheckedStarFieldPath model)
    (checked : CheckedDocument model) (environment : Env) :
    Except CheckedStarDocumentError CheckedAddressedCell :=
  checked.addressedCell environment source.declaration.id

/-- Resolve the existing topology against the immutable checked document and read each concrete leaf once. No declared tail is materialized as an address, and every topology or document failure stays structural. -/
def resolveCheckedField (source : CheckedStarFieldPath model)
    (checked : CheckedDocument model) (outer : Env) :
    Except CheckedStarDocumentError ResolvedCheckedStarField := do
  let topology ←
    (source.path.resolve checked.source.toDocument outer).mapError .addressing
  let cells ← topology.environments.mapM (source.addressedCell checked)
  pure { topology, cells }

/-- Resolve one full-validation starred entity-list occurrence. Optional checked-filter ownership remains with the typed caller; this function owns the common filter-before-addressing projection and preserves reached failures structurally. -/
def resolveCheckedValidationEntityOperandCore
    (source : CheckedStarFieldPath model)
    (checked : CheckedDocument model) (outer : Env)
    (having : Option CorrelatedHaving) :
    Except CheckedAddressingError ResolvedCheckedEntityOperandCore := do
  let topology ←
    (source.path.resolve checked.source.toDocument outer).mapError .addressing
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

/-- Resolve one unfiltered starred occurrence under partial-validation relevance. Candidate topology remains complete while only relevant concrete cells are addressed, and incomplete extent stays on this exact operand. -/
def resolveCheckedPartialValidationEntityOperandCore
    (source : CheckedStarFieldPath model)
    (checked : CheckedDocument model) (outer : Env)
    (scope : ValidationRelevanceScope) :
    Except CheckedAddressingError ResolvedCheckedEntityOperandCore := do
  let topology ←
    (source.path.resolve checked.source.toDocument outer).mapError .addressing
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
