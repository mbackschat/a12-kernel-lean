import A12Kernel.Elaboration.CheckedGroupPresence
import A12Kernel.Elaboration.ValidationRelevance
import A12Kernel.Semantics.Required

/-! # Model-certified generated requiredness

A required field desugars to one generated `mandatoryField` rule ([spec/03 §B](../../spec/03-empty-and-required.md#part-b--4-the-required-property)): `FieldNotFilled(F)` when no repeatable ancestor gates it, otherwise `GroupFilled(G) And FieldNotFilled(F)` with `G` the nearest repeatable ancestor or, under the parent option, the direct parent. The rule runs once per instantiated in-capacity row of the field's own repeatable scope and only where the call's relevance covers the field; a gate reads formally admitted content through the same group-presence slice authored rules use, so a parent whose admitted content lies outside a partial selection does not count as filled ([checkpoint](../../docs/sources/model-structure-and-declaration-probes.md#src-generated-requiredness-k14)). Evaluation reads base checked cells; the validation-scoped `.required` finding is attached only afterwards, to fired addresses.
-/

namespace A12Kernel

inductive CheckedRequiredError where
  | model (error : ResolveError)
  | notRequired (path : List String)
  | requiresGroupGate (path : List String) (groupPath : GroupPath)
  | rows (error : ActualRowEnvironmentError)
  | environment (error : EnvBindingError)
  | document (error : CheckedDocumentError)
  | group (error : CheckedGroupPresenceError)
  deriving Repr, DecidableEq

/-- One generated mandatory evaluation at one exact address, before its finding is attached. -/
structure RequiredEvaluation where
  address : CellAddr
  verdict : Verdict
  deriving Repr, DecidableEq

/-- The addresses that draw a generated `mandatoryField` finding, each an ERROR of type OMISSION
whose error and fill-to-fix pointer are the address itself (`mandatoryFieldMetadata`). -/
def RequiredEvaluation.mandatoryAddresses (evaluations : List RequiredEvaluation) : List CellAddr :=
  evaluations.filterMap fun evaluation =>
    if evaluation.verdict == .fired .omission then some evaluation.address else none

namespace CheckedDocument

/-- Resolve one absolute nonrepeatable required target from the checked document's exact model, evaluate its generated mandatory rule against the immutable base cells, and return the separate authored-validation view. -/
def applyAbsoluteRequiredAt (checked : CheckedDocument model)
    (field : FieldId) : Except CheckedRequiredError AbsoluteRequiredResult := do
  let declaration ← model.lookupUniqueId field |>.mapError .model
  let scope ← model.requirednessScopeFor declaration |>.mapError .model
  match scope with
  | none => throw (.notRequired declaration.path)
  | some .absolute =>
      pure (applyAbsoluteRequired declaration.toPresenceField checked.flatContext)
  | some (.relativeTo groupPath) =>
      throw (.requiresGroupGate declaration.path groupPath)

/-- `FieldNotFilled` on one base cell: empty fires with OMISSION, a value does not, and a formally
unavailable cell is unknown, so an ordinary invalid cell is never relabelled required. -/
private def fieldNotFilledVerdict (cell : CheckedCell) : Verdict :=
  match observeCell .validation cell with
  | .empty => .fired .omission
  | .value _ => .notFired
  | .unknown _ | .poison _ => .unknown

/-- Every generated mandatory evaluation of one validation call, over the base checked cells.
`rows` and `cells` are the call's group-presence slice: the whole document for full validation, the
relevance-filtered rows and placements for a partial call. -/
def requiredEvaluations (checked : CheckedDocument model)
    (relevance : ValidationRelevanceScope) (rows : List RowAddr)
    (cells : List CheckedCellPlacement) :
    Except CheckedRequiredError (List RequiredEvaluation) :=
  model.fields.flatMapM fun declaration => do
    let scope ← model.requirednessScopeFor declaration |>.mapError .model
    match scope with
    | none => pure []
    | some requirement =>
        let environments ← if declaration.repeatableScope.isEmpty then pure [[]]
          else checked.actualRowEnvironments declaration.repeatableScope |>.mapError .rows
        let admitted := environments.filter fun environment =>
          model.addressOverLimit? declaration.repeatableScope (environment.map (·.2)) == some false &&
            relevance.coversCell model declaration.path environment
        admitted.mapM fun environment => do
          let path ← environment.pathForScope declaration.repeatableScope |>.mapError .environment
          let address : CellAddr := { field := declaration.id, path }
          let cell ← checked.read address |>.mapError .document
          let target := fieldNotFilledVerdict cell
          match requirement with
          | .absolute => pure { address, verdict := target }
          | .relativeTo groupPath =>
              let input ← model.groupPresenceInputFromSlice rows cells groupPath environment
                (relevance.groupRelevance model groupPath environment) false |>.mapError .group
              pure { address, verdict := input.derive.groupFilled.conj target }

/-- Full validation's generated mandatory evaluations. -/
def fullRequiredEvaluations (checked : CheckedDocument model) :
    Except CheckedRequiredError (List RequiredEvaluation) :=
  checked.requiredEvaluations .full checked.source.instantiatedRows checked.checkedCells

/-- The document full validation's authored rules read: every fired address carries the
validation-scoped `.required` finding, an absent cell included. Computation phases ignore that
finding, so the overlay changes no computed value. -/
def withRequiredFindings (checked : CheckedDocument model)
    (evaluations : List RequiredEvaluation) : CheckedDocument model :=
  checked.overlayCells [] ((RequiredEvaluation.mandatoryAddresses evaluations).map fun address =>
    match checked.checkedCells.find? (·.address == address) with
    | some placement => { placement with cell := placement.cell.withFinding .required }
    | none => { address, cell := (checkAdmittedRawCell .empty).withFinding .required })

/-- **The document full validation's authored rules run on** (spec/03 §B.2): the checked document
carrying its own generated mandatory findings. -/
def fullValidationDocument (checked : CheckedDocument model) :
    Except CheckedRequiredError (CheckedDocument model) :=
  checked.fullRequiredEvaluations.map checked.withRequiredFindings

end CheckedDocument

end A12Kernel
