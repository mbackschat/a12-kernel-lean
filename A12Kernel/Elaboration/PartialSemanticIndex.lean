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

/-- Resolve only selection and topology without reading targets; consumers retain their own extent
gate and cell scan. Missing selection requires wildcard target coverage (spec/10 §5). -/
def resolvePartialSelectedAddresses
    (source : Sum (CheckedSemanticIndexSource model) (CheckedKeyedEntityExtent model))
    (document : CheckedDocument model) (scope : ValidationRelevanceScope) (outer : Env)
    (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell))
    (extentRelevant : FlatFieldDecl → List RepeatableLevel → List RepeatableLevel → Env → Bool := fun _ _ _ _ => true) :
    Except CheckedAddressingError
      (Option (CellObservation (List (FlatFieldDecl × Env) × Bool))) := do
  let view ← document.applyPartialGeneratedPreliminaryForScope scope |>.mapError .indexPreliminary
  let selection := match source with | .inl selected => selected | .inr selected => selected.selection.indexSource
  match ← selection.selectPartial view outer read with
  | none => pure none
  | some (.unknown cause) => pure (some (.unknown cause))
  | some (.poison cause) => pure (some (.poison cause))
  | some .empty =>
      let declarations := match source with | .inl selected => [selected.targetDeclaration] | .inr selected => selected.declarations
      let bound := selection.indexDeclaration.repeatableScope.dropLast
      if !declarations.all (fun declaration => view.relevance.coversValueListExtent model
          declaration.path bound (declaration.repeatableScope.drop bound.length) outer &&
          extentRelevant declaration bound (declaration.repeatableScope.drop bound.length) outer) then return none
      let omitted := match source with
        | .inl _ => false
        | .inr selected => match selected.target with | .group _ => true | _ => false
      pure (some (.value ([], omitted)))
  | some (.value environment) =>
      let declarations := match source with | .inl selected => [selected.targetDeclaration] | .inr selected => selected.declarations
      let bound := selection.indexDeclaration.repeatableScope
      if !declarations.all (fun declaration => extentRelevant declaration bound
          (declaration.repeatableScope.drop bound.length) environment) then return none
      match source with
      | .inl selected => pure (some (.value ([(selected.targetDeclaration, environment)], false)))
      | .inr selected =>
          let rows ← selected.rows document.source.toDocument environment |>.mapError .addressing
          pure (some (.value (rows.flatMap (fun (declaration, environments, _) =>
            environments.map (declaration, ·)), rows.any (·.2.2))))

end A12Kernel
