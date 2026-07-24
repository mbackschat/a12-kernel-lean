import A12Kernel.Elaboration.CheckedDocument
import A12Kernel.Elaboration.StarPath
import A12Kernel.Semantics.Correlation

/-! # Checked-document projection over one resolved starred field

This boundary joins the immutable checked input to the existing checked star path and topology without reconstructing either owner. It is deliberately one-field-wide: authored multi-operand ordering, filters, relevance, and consumer-specific classification remain with their established owners and SG2.
-/

namespace A12Kernel

inductive CheckedAddressingError where
  | addressing (cause : StarAddressingError)
  | field (field : FieldId) (cause : ResolveError)
  | environment (cause : EnvBindingError)
  | document (cause : CheckedDocumentError)
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

end ResolvedCheckedEntityOperandCore

namespace CheckedDocument

/-- Read one model-owned field instance from a complete environment. The declaration selects its named repeatable scope; environment order and unrelated deeper bindings cannot change the address. -/
def addressedCell (checked : CheckedDocument model)
    (environment : Env) (field : FieldId) :
    Except CheckedAddressingError CheckedAddressedCell := do
  let declaration ←
    (model.lookupUniqueId field).mapError (.field field)
  let path ←
    (environment.pathForScope declaration.repeatableScope)
      |>.mapError .environment
  let address : CellAddr := { field, path }
  let cell ← (checked.read address).mapError .document
  pure {
    environment
    address
    stored := checked.source.toDocument.rawCells address
    cell
  }

/-- Correlation reads from the same immutable checked input and preserve field/address failures separately from semantic UNKNOWN or computation poison. -/
def resolvingCorrelationContext (checked : CheckedDocument model) :
    ResolvingCorrelationContext CheckedAddressingError where
  read environment field :=
    (checked.addressedCell environment field).map (·.cell)
  bindingError := .environment

/-- Resolve one direct entity-list occurrence through the same model-owned address query as every starred occurrence. -/
def resolveCheckedDirectEntityOperandCore
    (checked : CheckedDocument model) (field : FieldId) :
    Except CheckedAddressingError ResolvedCheckedEntityOperandCore := do
  let addressed ← checked.addressedCell [] field
  pure {
    topology := none
    addressedCells := [addressed]
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
    hasNonRelevant := !source.allRowsRelevant scope
  }

end CheckedStarFieldPath

end A12Kernel
