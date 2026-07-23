import A12Kernel.Elaboration.CheckedGroupPresence
import A12Kernel.Elaboration.CheckedRequired
import A12Kernel.Elaboration.StarPath
import A12Kernel.Semantics.RepetitionNotUnique

/-! # Checked full and partial generated-preliminary findings

This boundary derives generated index mandatory and uniqueness findings from one immutable checked document. Its partial view selects index candidates before duplicate construction and combines the existing absolute nonrepeatable required evaluator without merging their roles. An empty ordinary required field remains computation-ignored while an empty index remains a distinct later formal-operand fact.
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
  | unknownRelevantEntity (path : List String)
  | relevantIndexArity (path : List String) (expected actual : Nat)
  | zeroRelevantIndex (path : List String) (position : Nat)
  | nonRelevantAddress (address : CellAddr)
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
    (declaration : FlatFieldDecl) (relevance : ValidationRelevanceScope) :
    Except CheckedIndexPreliminaryError (List CheckedIndexCandidate) :=
  (checked.source.instantiatedRows.filter fun row =>
      let environment :=
        (model.repeatableScopeForGroupPath group.path).zip row.path
      row.group == group.level &&
        relevance.coversCell model declaration.path environment).mapM fun row => do
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
    (checked : CheckedDocument model) (relevance : ValidationRelevanceScope) :
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
                  (← checked.indexCandidates group declaration relevance))
            | actual =>
                throw (.unsupportedIndexKind declaration.path actual.surfaceKind)
      pure (current ++ (← checked.indexFindings relevance groups))

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
    findings := ← checked.indexFindings .full model.repeatableGroups
  }

end CheckedDocument

private def FlatModel.hasRelevantEntityPath (model : FlatModel)
    (path : List String) : Bool :=
  model.hasGroupPath path ||
    model.fields.any fun declaration => declaration.path == path

private def FlatModel.maximumAtRelevantSegment? (model : FlatModel)
    (path : GroupPath) : Option Nat :=
  match model.repeatableGroups.find? fun group => group.path == path with
  | some group => group.repeatability
  | none => some 1

private def RelevantEntityPattern.indicesOverLimit
    (entity : RelevantEntityPattern) (model : FlatModel) :
    Except CheckedIndexPreliminaryError Bool :=
  let rec go (pathPrefix : GroupPath) (position : Nat) :
      List String → List RelevanceIndex →
        Except CheckedIndexPreliminaryError Bool
    | [], [] => pure false
    | segment :: segments, index :: indices => do
        let path := pathPrefix ++ [segment]
        let current ← match index with
          | .all => pure false
          | .concrete 0 => throw (.zeroRelevantIndex entity.path position)
          | .concrete actual =>
              pure (match model.maximumAtRelevantSegment? path with
                | some maximum => actual > maximum
                | none => false)
        pure (current || (← go path (position + 1) segments indices))
    | _, _ => throw (.relevantIndexArity entity.path
        entity.path.length entity.indices.length)
  if entity.path.length != entity.indices.length then
    throw (.relevantIndexArity entity.path
      entity.path.length entity.indices.length)
  else
    go [] 0 entity.path entity.indices

private def FlatModel.normalizeRelevantEntities (model : FlatModel) :
    List RelevantEntityPattern →
      Except CheckedIndexPreliminaryError (List RelevantEntityPattern)
  | [] => pure []
  | entity :: entities => do
      if !model.hasRelevantEntityPath entity.path then
        throw (.unknownRelevantEntity entity.path)
      let ignored ← entity.indicesOverLimit model
      let rest ← model.normalizeRelevantEntities entities
      if ignored then pure rest else pure (entity :: rest)

structure PartialRequiredEvaluation where
  address : CellAddr
  verdict : Verdict
  deriving Repr, DecidableEq

/-- One call-local partial generated-preliminary view. Index and ordinary-required outcomes remain separate, while both annotate the same immutable checked input for authored validation and group-state consumers. -/
structure CheckedPartialPreliminary (model : FlatModel) where
  private mk ::
  relevance : ValidationRelevanceScope
  index : CheckedIndexPreliminary model
  required : List PartialRequiredEvaluation

namespace CheckedPartialPreliminary

/-- Whether the normalized call-local relevance set covers one exact model address. Structural validity remains checked separately by the base read. -/
def isAddressRelevant (view : CheckedPartialPreliminary model)
    (address : CellAddr) : Bool :=
  match model.lookupUniqueId address.field with
  | .error _ => false
  | .ok declaration =>
      view.relevance.coversCell model declaration.path
        (declaration.repeatableScope.zip address.path)

def requiredVerdictAt? (view : CheckedPartialPreliminary model)
    (address : CellAddr) : Option Verdict :=
  (view.required.find? fun evaluation =>
    evaluation.address == address).map (·.verdict)

/-- Apply only the separate absolute-required channel to an already index-annotated cell. -/
def annotateRequiredCell (view : CheckedPartialPreliminary model)
    (address : CellAddr) (cell : CheckedCell) : CheckedCell :=
  match view.requiredVerdictAt? address with
  | some (.fired .omission) => cell.withFinding .required
  | _ => cell

def readAuthoredValidation (view : CheckedPartialPreliminary model)
    (address : CellAddr) :
    Except CheckedIndexPreliminaryError CheckedCell := do
  let cell ← view.index.readAuthoredValidation address |>.mapError .document
  if view.isAddressRelevant address then
    pure (view.annotateRequiredCell address cell)
  else
    throw (.nonRelevantAddress address)

private def placements (view : CheckedPartialPreliminary model) :
    List CheckedCellPlacement :=
  let placed := (view.index.placements.filter fun placement =>
    view.isAddressRelevant placement.address).map fun placement =>
    { placement with
      cell := view.annotateRequiredCell placement.address placement.cell }
  let absent := view.required.filterMap fun evaluation =>
    if evaluation.verdict != .fired .omission ||
        placed.any fun placement => placement.address == evaluation.address then
      none
    else
      some {
        address := evaluation.address
        cell := (checkAdmittedRawCell .empty).withFinding .required
      }
  placed ++ absent

private def relevantEntityCoversRow
    (entity : RelevantEntityPattern) (model : FlatModel)
    (row : RowAddr) : Bool :=
  match model.repeatableGroupAtLevel? row.group with
  | none => false
  | some group =>
      let environment :=
        (model.repeatableScopeForGroupPath group.path).zip row.path
      if entity.path.isPrefixOf group.path then
        entity.coversCell model group.path environment
      else if group.path.isPrefixOf entity.path then
        ({ path := group.path
           indices := entity.indices.take group.path.length } :
          RelevantEntityPattern).coversCell model group.path environment
      else
        false

private def relevanceCoversRow
    (scope : ValidationRelevanceScope) (model : FlatModel)
    (row : RowAddr) : Bool :=
  match scope with
  | .full => true
  | .partialSet entities =>
      entities.any fun entity => relevantEntityCoversRow entity model row

private def relevantRows (view : CheckedPartialPreliminary model) :
    List RowAddr :=
  view.index.base.source.instantiatedRows.filter
    (relevanceCoversRow view.relevance model)

def groupPresenceInput (view : CheckedPartialPreliminary model)
    (groupPath : GroupPath) (environment : Env)
    (relevance : GroupRelevance) (structuralError : Bool) :
    Except CheckedGroupPresenceError ResolvedGroupPresenceInput :=
  view.index.base.groupPresenceInputFromSlice view.relevantRows view.placements
    groupPath environment relevance structuralError

end CheckedPartialPreliminary

namespace CheckedDocument

private def partialRequiredEvaluations (checked : CheckedDocument model)
    (relevance : ValidationRelevanceScope) :
    List FieldId →
      Except CheckedIndexPreliminaryError (List PartialRequiredEvaluation)
  | [] => pure []
  | field :: fields => do
      let rest ← checked.partialRequiredEvaluations relevance fields
      if fields.contains field then
        pure rest
      else
        let declaration ←
          model.resolveNonrepeatableDeclarationById field |>.mapError .model
        let address : CellAddr := { field, path := [] }
        if relevance.coversCell model declaration.path [] then
          let result :=
            applyAbsoluteRequired declaration.toPresenceField checked.flatContext
          pure ({ address, verdict := result.mandatoryVerdict } :: rest)
        else
          pure rest

/-- Build the no-default partial generated-preliminary view from normalized relevant entity patterns. Over-capacity concrete selectors are ignored as the public API requires; malformed or unknown patterns fail explicitly. -/
def applyPartialGeneratedPreliminary (checked : CheckedDocument model)
    (relevantEntities : List RelevantEntityPattern)
    (absoluteRequiredFields : List FieldId) :
    Except CheckedIndexPreliminaryError (CheckedPartialPreliminary model) := do
  let normalized ← model.normalizeRelevantEntities relevantEntities
  let relevance := ValidationRelevanceScope.partialSet normalized
  let index : CheckedIndexPreliminary model := {
    base := checked
    findings := ← checked.indexFindings relevance model.repeatableGroups
  }
  pure {
    relevance
    index
    required := ← checked.partialRequiredEvaluations relevance
      absoluteRequiredFields
  }

end CheckedDocument

end A12Kernel
