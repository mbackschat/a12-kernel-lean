import A12Kernel.Elaboration.KeyedEntityExtent

namespace A12Kernel

/-- Partial lookup uses only relevant index cells; a concrete inventory of existing rows does
not decide an absent key (spec/10 §5, retained keyed-partial-read matrix). `none` retains call-local
unavailability separately from formal invalidity and from a known empty selection. -/
def CheckedSemanticIndexSource.selectPartial (source : CheckedSemanticIndexSource model)
    (view : CheckedPartialPreliminary model) (outer : Env)
    (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell)) :
    Except CheckedAddressingError (Option (CellObservation Env)) := do
  let keyCell ← match source.key with
    | .literal .. => pure (checkAdmittedRawCell .empty)
    | .field declaration =>
        if !view.relevance.coversField model declaration.id [] then return none
        match ← read [] declaration.id with
        | none => return none
        | some cell => pure cell
  let key ← source.observeCurrentKey .validation (fun _ => keyCell)
    (view.index.base.storedTextIn []) |>.mapError .semanticIndex
  let column ← view.index.resolveIndexColumn source.group outer
    (includeAddress := fun address => view.isAddressRelevant address && !view.silentlyUnavailable.contains address)
      |>.mapError (CheckedAddressingError.semanticIndex ∘ SemanticIndexContextError.checkedColumn)
  let selected ← column.toSemanticIndexColumn view.index source.indexDeclaration.id
    |>.mapError (CheckedAddressingError.semanticIndex ∘ SemanticIndexContextError.checkedColumn)
  match selected.lookupEnvironment .validation source.numericIndex key with
  | .value (some environment) => pure (some (.value environment))
  | .value none => throw (.checkedDocumentRequired source.group.path)
  | .unknown cause => pure (some (.unknown cause))
  | .poison cause => pure (some (.poison cause))
  | .empty =>
      let parent ← outer.pathForScope source.indexDeclaration.repeatableScope.dropLast |>.mapError .environment
      let silentlyUnavailable := view.silentlyUnavailable.any fun address =>
        address.field == source.indexDeclaration.id && address.path.dropLast == parent
      if silentlyUnavailable || !view.relevance.coversValueListExtent model source.indexDeclaration.path
          source.indexDeclaration.repeatableScope.dropLast [source.group.level] outer then
        pure none
      else pure (some .empty)

/-- A selected field is relevant at its resolved coordinate; missing selection uses the separate
wildcard-extent judgment and never fabricates a physical row (spec/10 §5). -/
def CheckedSemanticIndexSource.observePartialDocument (source : CheckedSemanticIndexSource model)
    (document : CheckedDocument model) (scope : ValidationRelevanceScope) (outer : Env)
    (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell)) :
    Except CheckedAddressingError (Option CellObservation) := do
  let view ← document.applyPartialGeneratedPreliminaryForScope scope |>.mapError .indexPreliminary
  match ← source.selectPartial view outer read with
  | none => pure none
  | some .empty =>
      if view.relevance.coversValueListExtent model source.targetDeclaration.path
          source.indexDeclaration.repeatableScope.dropLast [source.group.level] outer then
        pure (some .empty)
      else pure none
  | some (.unknown cause) => pure (some (.unknown cause))
  | some (.poison cause) => pure (some (.poison cause))
  | some (.value environment) =>
      if !view.relevance.coversField model source.targetDeclaration.id environment then return none
      pure ((← read environment source.targetDeclaration.id).map (observeCell .validation))

end A12Kernel
