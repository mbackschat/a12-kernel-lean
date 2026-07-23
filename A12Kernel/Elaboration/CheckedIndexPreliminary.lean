import A12Kernel.Elaboration.CheckedGroupPresence
import A12Kernel.Semantics.RepetitionNotUnique

/-! # Full-validation index preliminary findings

This boundary derives generated index mandatory and uniqueness findings from one immutable checked document. It retains addressed finding roles separately from the authored-validation cell view because ordinary requiredness is computation-ignored while an empty index remains a distinct later formal-operand fact.
-/

namespace A12Kernel

inductive IndexPreliminaryKind where
  | mandatory
  | unique
  deriving Repr, DecidableEq

namespace IndexPreliminaryKind

def cause : IndexPreliminaryKind → FormalCause
  | .mandatory => .required
  | .unique => .duplicateIndex

def verdict : IndexPreliminaryKind → Verdict
  | .mandatory => .fired .omission
  | .unique => .fired .value

def errorCode : IndexPreliminaryKind → String
  | .mandatory => "mandatoryField"
  | .unique => "uniqueIndex"

end IndexPreliminaryKind

structure IndexPreliminaryFinding where
  address : CellAddr
  kind : IndexPreliminaryKind
  deriving Repr, DecidableEq

inductive CheckedIndexPreliminaryError where
  | document (error : CheckedDocumentError)
  | model (error : ResolveError)
  | unsupportedIndexKind (path : List String) (actual : SurfaceScalarKind)
  | missingStoredValue (address : CellAddr)
  | incoherentValueKind (address : CellAddr)
  deriving Repr, DecidableEq

/-- One later full-validation view over the exact immutable checked input. Findings are extensional by address and kind; list order is not a public message-order contract. -/
structure CheckedIndexPreliminary (model : FlatModel) where
  private mk ::
  base : CheckedDocument model
  findings : List IndexPreliminaryFinding

private structure CheckedIndexCandidate where
  address : CellAddr
  resolved : ResolvedRepetitionKeyRow

private def CheckedDocument.storedAt? (checked : CheckedDocument model)
    (address : CellAddr) : Option String :=
  (checked.source.cells.find? fun input => input.address == address).map (·.stored)

private def CheckedDocument.indexComponentAt (checked : CheckedDocument model)
    (declaration : FlatFieldDecl) (address : CellAddr) :
    Except CheckedIndexPreliminaryError RepetitionKeyComponent := do
  let cell ← checked.read address |>.mapError .document
  match declaration.policy.kind, observeCell .validation cell with
  | _, .empty => pure .empty
  | _, .unknown cause | _, .poison cause => pure (.unknown cause)
  | .number _, .value (.num value) => pure (.present (.number value))
  | .number _, .value _ => throw (.incoherentValueKind address)
  | _, .value _ =>
      match checked.storedAt? address with
      | some stored => pure (.present (.token stored))
      | none => throw (.missingStoredValue address)

private def CheckedDocument.indexCandidates
    (checked : CheckedDocument model) (group : RepeatableGroupDecl)
    (declaration : FlatFieldDecl) :
    Except CheckedIndexPreliminaryError (List CheckedIndexCandidate) :=
  (checked.source.instantiatedRows.filter fun row =>
      row.group == group.level).mapM fun row => do
    let address := { field := declaration.id, path := row.path }
    let component ← checked.indexComponentAt declaration address
    pure {
      address
      resolved := {
        row := (model.repeatableScopeForGroupPath group.path).zip row.path
        key := [component]
      }
    }

private def CheckedIndexCandidates.parentPaths
    (candidates : List CheckedIndexCandidate) : List (List Nat) :=
  candidates.foldl (fun parents candidate =>
    let parent := candidate.address.path.dropLast
    if parents.contains parent then parents else parents ++ [parent]) []

private def indexFindingsForParent
    (candidates : List CheckedIndexCandidate) (parent : List Nat) :
    List IndexPreliminaryFinding :=
  let selected := candidates.filter fun candidate =>
    candidate.address.path.dropLast == parent
  let results := evalRepetitionNotUnique (selected.map (·.resolved))
  (selected.zip results).filterMap fun pair =>
    match pair.1.resolved.key, pair.2.verdict with
    | [.empty], _ => some { address := pair.1.address, kind := .mandatory }
    | _, .fired _ => some { address := pair.1.address, kind := .unique }
    | _, _ => none

private def indexFindingsForGroup
    (candidates : List CheckedIndexCandidate) :
    List IndexPreliminaryFinding :=
  (CheckedIndexCandidates.parentPaths candidates).flatMap
    (indexFindingsForParent candidates)

private def CheckedDocument.indexFindings
    (checked : CheckedDocument model) :
    List RepeatableGroupDecl →
      Except CheckedIndexPreliminaryError (List IndexPreliminaryFinding)
  | [] => pure []
  | group :: groups => do
      let current ← match group.indexField with
        | none => pure []
        | some field => do
            let declaration ← model.lookupUniqueId field |>.mapError .model
            match declaration.policy.kind with
            | .number _ | .string | .enumeration =>
                pure (indexFindingsForGroup
                  (← checked.indexCandidates group declaration))
            | actual =>
                throw (.unsupportedIndexKind declaration.path actual.surfaceKind)
      pure (current ++ (← checked.indexFindings groups))

namespace CheckedIndexPreliminary

def findingAt? (preliminary : CheckedIndexPreliminary model)
    (address : CellAddr) : Option IndexPreliminaryFinding :=
  preliminary.findings.find? fun finding => finding.address == address

def findingKindAt? (preliminary : CheckedIndexPreliminary model)
    (address : CellAddr) : Option IndexPreliminaryKind :=
  (preliminary.findingAt? address).map (·.kind)

/-- Apply this exact addressed preliminary finding to one base cell without changing its placement or parsed payload. -/
def annotateCell (preliminary : CheckedIndexPreliminary model)
    (address : CellAddr) (cell : CheckedCell) : CheckedCell :=
  match preliminary.findingAt? address with
  | none => cell
  | some finding => cell.withFinding finding.kind.cause

/-- Read the cell view seen by authored full-validation rules after index preliminary processing. This is not the computation formal-operand channel. -/
def readAuthoredValidation (preliminary : CheckedIndexPreliminary model)
    (address : CellAddr) : Except CheckedDocumentError CheckedCell := do
  pure (preliminary.annotateCell address (← preliminary.base.read address))

private def placements (preliminary : CheckedIndexPreliminary model) :
    List CheckedCellPlacement :=
  let placed := preliminary.base.checkedCells.map fun placement =>
    { placement with
      cell := preliminary.annotateCell placement.address placement.cell }
  let absent := preliminary.findings.filterMap fun finding =>
    if preliminary.base.checkedCells.any fun placement =>
        placement.address == finding.address then
      none
    else
      some {
        address := finding.address
        cell := (checkAdmittedRawCell .empty).withFinding finding.kind.cause
      }
  placed ++ absent

/-- Reuse the sole resolved group-scope owner with the addressed preliminary cell view, including required findings on physically absent index cells. -/
def groupPresenceInput (preliminary : CheckedIndexPreliminary model)
    (groupPath : GroupPath) (environment : Env)
    (relevance : GroupRelevance) (structuralError : Bool) :
    Except CheckedGroupPresenceError ResolvedGroupPresenceInput :=
  preliminary.base.groupPresenceInputFromCells preliminary.placements
    groupPath environment relevance structuralError

end CheckedIndexPreliminary

namespace CheckedDocument

/-- Run every model-declared index mandatory/uniqueness preliminary rule over the immutable base checked document without mutating it. -/
def applyFullIndexPreliminary (checked : CheckedDocument model) :
    Except CheckedIndexPreliminaryError (CheckedIndexPreliminary model) := do
  pure {
    base := checked
    findings := ← checked.indexFindings model.repeatableGroups
  }

end CheckedDocument

end A12Kernel
