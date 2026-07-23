import A12Kernel.Elaboration.StringContext

/-! # Immutable model-certified checked documents

This module starts at the theory's established scalar-parser boundary. A finite input retains physical rows, placed stored text, and the corresponding preclassified scalar input. Construction validates finite topology and placement once, applies the already prepared model-owned checkers once per placed cell, and produces one immutable checked view shared by existing consumers. Processing context, generated findings, relevance, scheduling, and application remain separate.
-/

namespace A12Kernel

/-- One physically placed field plus the parser-boundary classification of its stored text. An absent cell has no entry. -/
structure ClassifiedCellInput where
  address : CellAddr
  stored : String
  raw : RawCell
  deriving Repr, DecidableEq

/-- Finite immutable document data. Rows remain independent of placed cells. -/
structure DocumentData where
  instantiatedRows : List RowAddr
  cells : List ClassifiedCellInput
  deriving Repr, DecidableEq

namespace DocumentData

/-- Compile finite transport data to the established pure lookup view used by addressing semantics. -/
def toDocument (data : DocumentData) : Document where
  instantiatedRows := data.instantiatedRows
  rawCells := fun address =>
    (data.cells.find? fun cell => cell.address == address).map (·.stored)

end DocumentData

inductive CheckedDocumentError where
  | duplicateRow (row : RowAddr)
  | duplicateCell (address : CellAddr)
  | incoherentCell (address : CellAddr)
  | unknownRowGroup (row : RowAddr)
  | invalidRowDepth (row : RowAddr) (expected : Nat)
  | zeroRowIndex (row : RowAddr)
  | missingParentRow (row parent : RowAddr)
  | nonprefixRow (row predecessor : RowAddr)
  | fieldAddress (address : CellAddr) (cause : ResolveError)
  | invalidCellDepth (address : CellAddr) (expected : Nat)
  | zeroCellIndex (address : CellAddr)
  | missingRow (row : RowAddr)
  deriving Repr, DecidableEq

structure CheckedCellPlacement where
  address : CellAddr
  cell : CheckedCell
  deriving Repr, DecidableEq

/-- One exact-model checked input. The source placement remains immutable and every placed cell has one cached base formal-check result. -/
structure CheckedDocument (model : FlatModel) where
  source : DocumentData
  checkedCells : List CheckedCellPlacement
  modelWellFormed : model.validate.isOk = true

private def firstDuplicateRow? : List RowAddr → Option RowAddr
  | [] => none
  | row :: rest =>
      if rest.contains row then some row else firstDuplicateRow? rest

private def firstDuplicateCell? : List ClassifiedCellInput → Option CellAddr
  | [] => none
  | cell :: rest =>
      if rest.any fun candidate => candidate.address == cell.address then
        some cell.address
      else
        firstDuplicateCell? rest

private def FlatModel.repeatableGroupAtLevel? (model : FlatModel)
    (level : RepeatableLevel) : Option RepeatableGroupDecl :=
  model.repeatableGroups.find? fun group => group.level == level

private def parentRow? (scope : List RepeatableLevel) (row : RowAddr) :
    Option RowAddr :=
  match scope.reverse, row.path.reverse with
  | _ :: parentLevel :: _, _ :: _ =>
      some { group := parentLevel, path := row.path.dropLast }
  | _, _ => none

private def predecessorRow? (row : RowAddr) : Option RowAddr :=
  match row.path.reverse with
  | [] => none
  | coordinate :: _ =>
      if coordinate ≤ 1 then none
      else some {
        group := row.group
        path := row.path.dropLast ++ [coordinate - 1]
      }

private def validateRows (model : FlatModel) (rows : List RowAddr) :
    Except CheckedDocumentError Unit := do
  match firstDuplicateRow? rows with
  | some row => throw (.duplicateRow row)
  | none => pure ()
  for row in rows do
    let group ← match model.repeatableGroupAtLevel? row.group with
      | some group => pure group
      | none => throw (.unknownRowGroup row)
    let scope := model.repeatableScopeForGroupPath group.path
    if row.path.length != scope.length then
      throw (.invalidRowDepth row scope.length)
    if row.path.any (· == 0) then
      throw (.zeroRowIndex row)
    match parentRow? scope row with
    | some parent =>
        if !rows.contains parent then throw (.missingParentRow row parent)
    | none => pure ()
    match predecessorRow? row with
    | some predecessor =>
        if !rows.contains predecessor then throw (.nonprefixRow row predecessor)
    | none => pure ()

private def requiredRows : List RepeatableLevel → List Nat → List Nat → List RowAddr
  | [], [], _ => []
  | level :: levels, coordinate :: coordinates, priorPath =>
      let path := priorPath ++ [coordinate]
      { group := level, path } :: requiredRows levels coordinates path
  | _, _, _ => []

private def validateCellAddress (model : FlatModel) (rows : List RowAddr)
    (address : CellAddr) : Except CheckedDocumentError FlatFieldDecl := do
  let declaration ←
    (model.lookupUniqueId address.field).mapError (.fieldAddress address)
  if address.path.length != declaration.repeatableScope.length then
    throw (.invalidCellDepth address declaration.repeatableScope.length)
  if address.path.any (· == 0) then
    throw (.zeroCellIndex address)
  for row in requiredRows declaration.repeatableScope address.path [] do
    if !rows.contains row then throw (.missingRow row)
  pure declaration

private def ClassifiedCellInput.coherent (input : ClassifiedCellInput) : Bool :=
  if input.stored.isEmpty then
    input.raw == .presentEmpty
  else
    match input.raw with
    | .parsed _ | .rejected _ => true
    | .empty | .presentEmpty => false

private def checkPlacedCell
    (prepared : PreparedFlatStringContext model compilePattern)
    (locale : String) (rows : List RowAddr)
    (input : ClassifiedCellInput) :
    Except CheckedDocumentError CheckedCellPlacement := do
  if !input.coherent then throw (.incoherentCell input.address)
  let _ ← validateCellAddress model rows input.address
  let raw : RawFlatContext := {
    read := fun field => if field == input.address.field then input.raw else .empty
  }
  pure {
    address := input.address
    cell := (prepared.checkContext locale raw).read input.address.field
  }

/-- Validate finite placement and cache every placed cell through the exact prepared model context. -/
def checkDocument (prepared : PreparedFlatStringContext model compilePattern)
    (locale : String) (source : DocumentData) :
    Except CheckedDocumentError (CheckedDocument model) := do
  validateRows model source.instantiatedRows
  match firstDuplicateCell? source.cells with
  | some address => throw (.duplicateCell address)
  | none => pure ()
  let checkedCells ← source.cells.mapM
    (checkPlacedCell prepared locale source.instantiatedRows)
  pure {
    source
    checkedCells
    modelWellFormed := prepared.patterns.modelWellFormed
  }

namespace CheckedDocument

/-- Query one model-legal address. Absence is a clean empty checked cell; malformed addressing remains an explicit structural error. -/
def read (checked : CheckedDocument model) (address : CellAddr) :
    Except CheckedDocumentError CheckedCell := do
  let _ ← validateCellAddress model checked.source.instantiatedRows address
  match checked.checkedCells.find? fun placement => placement.address == address with
  | some placement => pure placement.cell
  | none => pure (checkAdmittedRawCell .empty)

/-- Existing nonrepeatable evaluators consume the same checked cells. Their checked plans cannot request repeatable fields; a forged request fails closed. -/
def flatContext (checked : CheckedDocument model) : FlatContext where
  read field :=
    match checked.read { field, path := [] } with
    | .ok cell => cell
    | .error _ => malformedCheckedCell

end CheckedDocument

end A12Kernel
