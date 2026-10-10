import A12Kernel.Elaboration.CheckedIndexPreliminary
import A12Kernel.Semantics.MessageCacheOrder
import A12Kernel.Semantics.CustomFieldTypeVocabulary

namespace A12Kernel

inductive CheckedMessageCacheError where
  | model (error : ResolveError)
  | document (error : CheckedDocumentError)
  | binding (error : EnvBindingError)
  | customAdmission (field : FieldId)
  | missingCapacity (group : GroupPath)
  | unknownGroup (group : RepeatableLevel)
  | coordinateRange
  | missingInternalName (field : FieldId)
  | hostOrder (error : MessageCacheOrderError)
  deriving Repr, DecidableEq

/-- Model-wide internal names, including reservations for authored suffix-shaped names. Lexical full-path order is measured in UTF-16 units, independently of declaration order. -/
def FlatModel.messageFieldNames (model : FlatModel) : List (FieldId × String) := Id.run do
  let names := model.fields.map (·.name)
  let ordered := model.fields.mergeSort fun left right =>
    compare (messageNameUnits (String.intercalate "/" left.path))
      (messageNameUnits (String.intercalate "/" right.path)) != .gt
  let mut assigned : List (FieldId × String) := []
  for declaration in ordered do
    let name := if (names.filter (· == declaration.name)).length == 1 then declaration.name
      else
        let reserved := names ++ assigned.map Prod.snd
        let suffix := ((List.range (reserved.length + 1)).find? fun index =>
          !reserved.contains s!"{declaration.name}_{index}").getD 0
        s!"{declaration.name}_{suffix}"
    assigned := assigned ++ [(declaration.id, name)]
  return assigned

private def fullCoordinates (model : FlatModel) (path : GroupPath) (environment : Env) :
    Except CheckedMessageCacheError (List Nat) :=
  path.zipIdx.mapM fun (_, depth) => do
    let coordinate ← match model.repeatableGroups.find? (·.path == path.take (depth + 1)) with
      | none => pure 1
      | some group => environment.bindingAt group.level |>.mapError .binding
    if coordinate > 2147483647 then throw .coordinateRange
    pure coordinate

private def messageKey (declaration : FlatFieldDecl) (cell : CheckedCell)
    (stored : Option String) : Option SemanticIndexKey :=
  match declaration.policy.kind, observeCell .validation cell with
  | .number _, .value (.num value) => some (.number value)
  | .number _, _ => none
  | _, .value _ => stored.map .text
  | _, _ => none

/-- Base formal admission supplies keys before generated uniqueness findings hide duplicate values. -/
def CheckedDocument.messageKeyAt? (checked : CheckedDocument model)
    (address : CellAddr) : Option SemanticIndexKey := do
  let declaration ← (model.lookupUniqueId address.field).toOption
  let cell ← (checked.read address).toOption
  messageKey declaration cell (checked.storedTextAt address)

/-- Dynamic reference queries use the authored-rule view, including defaults and generated invalidity; cache population uses the earlier base view. -/
def CheckedIndexPreliminary.messageQueryKeyAt? (preliminary : CheckedIndexPreliminary model)
    (address : CellAddr) : Option SemanticIndexKey := do
  let declaration ← (model.lookupUniqueId address.field).toOption
  let cell ← (preliminary.readAuthoredValidation address).toOption
  messageKey declaration cell (preliminary.defaultStoredAt? address |>.orElse fun _ =>
    preliminary.base.storedTextAt address)

private def associationAt (model : FlatModel) (address : CellAddr)
    (key : SemanticIndexKey) : Option MessageIndexInsertion := do
  let group ← model.repeatableGroups.find? (·.indexField == some address.field)
  let row ← address.path.getLast?
  pure { group := group.level, parentPath := address.path.dropLast, row, key }

private def populationForScope (checked : CheckedDocument model)
    (relevance : ValidationRelevanceScope) :
    Except CheckedMessageCacheError (List MessageCachePopulationEntry) := do
  let names := model.messageFieldNames
  let mut population := []
  for row in checked.source.instantiatedRows do
    let some group := model.repeatableGroupAtLevel? row.group
      | throw (.unknownGroup row.group)
    let some maximum := group.repeatability | throw (.missingCapacity group.path)
    let scope := model.repeatableScopeForGroupPath group.path
    let some overLimit := model.addressOverLimit? scope row.path
      | throw (.missingCapacity group.path)
    let environment := scope.zip row.path
    let relevant := match relevance with
      | .full => true
      | .partialSet entities => entities.any (·.touchesGroup model group.path environment)
    if maximum > 1 && !overLimit && relevant then
      let coordinates ← fullCoordinates model group.path (scope.zip row.path)
      population := population ++ [{ hash := messageIdentifierHash ("/" ++ String.intercalate "/" group.path) coordinates }]
  for placement in checked.checkedCells do
    let declaration ← model.lookupUniqueId placement.address.field |>.mapError .model
    let environment := declaration.repeatableScope.zip placement.address.path
    if !relevance.coversCell model declaration.path environment then continue
    if !placement.cell.rawPresent || (placement.storedText.getD "").isEmpty then continue
    -- Cache admission of test-range findings differs from the registered checker's unavailable-cell result; collapsing them would discard a hash contribution (SG7).
    if placement.cell.findings.any (fun cause => match cause with
        | .registeredCustomValidation rejection => rejection.projectCode == CustomFieldType.testRangeCode
        | _ => false) then
      throw (.customAdmission declaration.id)
    if !placement.cell.findings.isEmpty then continue
    let some (_, name) := names.find? (·.1 == declaration.id)
      | throw (.missingInternalName declaration.id)
    let coordinates ← fullCoordinates model declaration.path
      (declaration.repeatableScope.zip placement.address.path)
    population := population ++ [{
      hash := messageIdentifierHash name coordinates
      association := (checked.messageKeyAt? placement.address).bind
        (associationAt model placement.address) }]
  return population

/-- Full-validation population before index defaults and generated findings. Unrelated admitted fields and in-capacity group placeholders retain their hash contribution. -/
def CheckedDocument.messageCachePopulation (checked : CheckedDocument model) :
    Except CheckedMessageCacheError (List MessageCachePopulationEntry) :=
  populationForScope checked .full

/-- Partial population admits relevant cells and touched ancestor groups before host ordering.
The checked view owns normalized relevance and globals (spec/10 §5). -/
def CheckedPartialPreliminary.messageCachePopulation (view : CheckedPartialPreliminary model) :
    Except CheckedMessageCacheError (List MessageCachePopulationEntry) :=
  populationForScope view.index.base view.relevance

/-- Derive a lookup-equivalent cache where the capacity envelope and bucket history settle every association. Kernel document traversal visits each group’s physical rows in ascending order; unrelated field order remains unspecified. Full-validation index defaults are appended after the original population, independently of its hash capacity. -/
def CheckedIndexPreliminary.deriveMessageCache (preliminary : CheckedIndexPreliminary model) :
    Except CheckedMessageCacheError MessageIndexCache := do
  let population ← preliminary.base.messageCachePopulation
  let cache ← deriveMessageIndexCache population .ascendingPhysical |>.mapError .hostOrder
  let defaults := preliminary.base.indexCacheDefaults.filterMap fun entry =>
    associationAt model entry.address (.text entry.stored)
  return { insertions := cache.insertions ++ defaults }

/-- Partial calls never append full-validation index defaults; duplicate associations still
come from base formal admission before generated findings (spec/04 and spec/10). -/
def CheckedPartialPreliminary.deriveMessageCache (view : CheckedPartialPreliminary model) :
    Except CheckedMessageCacheError MessageIndexCache := do
  let population ← view.messageCachePopulation
  deriveMessageIndexCache population .ascendingPhysical |>.mapError .hostOrder

/-- Prepare full-call lookup without requiring unrelated host-sensitive associations to settle. Strict whole-cache materialization remains available through `deriveMessageCache`. -/
def CheckedIndexPreliminary.messageCacheContext (preliminary : CheckedIndexPreliminary model) :
    Except CheckedMessageCacheError MessageIndexContext := do
  let population ← preliminary.base.messageCachePopulation
  let defaults := preliminary.base.indexCacheDefaults.filterMap fun entry =>
    associationAt model entry.address (.text entry.stored)
  return .derived population .ascendingPhysical defaults

/-- Partial lookup retains the complete call-local hash population and never applies full-call defaults. -/
def CheckedPartialPreliminary.messageCacheContext (view : CheckedPartialPreliminary model) :
    Except CheckedMessageCacheError MessageIndexContext := do
  return .derived (← view.messageCachePopulation) .ascendingPhysical []

/-- Structural queries retain partial unavailability independently of the admitted cache. -/
def CheckedPartialPreliminary.messageQueryKeyAt? (view : CheckedPartialPreliminary model)
    (address : CellAddr) : Option SemanticIndexKey := do
  let declaration ← (model.lookupUniqueId address.field).toOption
  let read ← (view.readAuthoredValidation address).toOption
  match read with
  | .silentlyUnavailable => none
  | .checked cell => messageKey declaration cell (view.index.base.storedTextAt address)

end A12Kernel
