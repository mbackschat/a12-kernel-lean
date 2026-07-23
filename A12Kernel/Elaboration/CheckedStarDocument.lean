import A12Kernel.Elaboration.CheckedDocument
import A12Kernel.Elaboration.StarPath

/-! # Checked-document projection over one resolved starred field

This boundary joins the immutable checked input to the existing checked star path and topology without reconstructing either owner. It is deliberately one-field-wide: authored multi-operand ordering, filters, relevance, and consumer-specific classification remain with their established owners and SG2.
-/

namespace A12Kernel

inductive CheckedStarDocumentError where
  | addressing (cause : StarAddressingError)
  | environment (cause : EnvBindingError)
  | document (cause : CheckedDocumentError)
  deriving Repr, DecidableEq

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

namespace CheckedStarFieldPath

private def addressedCell (source : CheckedStarFieldPath model)
    (checked : CheckedDocument model) (environment : Env) :
    Except CheckedStarDocumentError CheckedAddressedCell := do
  let path ←
    (environment.pathForScope source.declaration.repeatableScope)
      |>.mapError .environment
  let address : CellAddr := {
    field := source.declaration.id
    path
  }
  let cell ← (checked.read address).mapError .document
  pure {
    environment
    address
    stored := checked.source.toDocument.rawCells address
    cell
  }

/-- Resolve the existing topology against the immutable checked document and read each concrete leaf once. No declared tail is materialized as an address, and every topology or document failure stays structural. -/
def resolveCheckedField (source : CheckedStarFieldPath model)
    (checked : CheckedDocument model) (outer : Env) :
    Except CheckedStarDocumentError ResolvedCheckedStarField := do
  let topology ←
    (source.path.resolve checked.source.toDocument outer).mapError .addressing
  let cells ← topology.environments.mapM (source.addressedCell checked)
  pure { topology, cells }

end CheckedStarFieldPath

end A12Kernel
