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
        if !view.relevance.coversField model declaration.id outer then return none
        let available ← match read outer declaration.id with
          | .error (.partialUnavailable _ _) => pure none
          | result => result
        match available with
        | none => return none
        | some cell => pure cell
  let stored := fun field => do
    let address ← (view.index.base.cellAddress outer field).toOption
    view.index.base.storedTextForCell address keyCell
  let key ← source.observeCurrentKey .validation (fun _ => keyCell) stored |>.mapError .semanticIndex
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
def CheckedSemanticIndexSource.readPartialDocumentCell (source : CheckedSemanticIndexSource model)
    (document : CheckedDocument model) (scope : ValidationRelevanceScope) (outer : Env)
    (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell)) :
    Except CheckedAddressingError (Option (CellObservation (Env × CheckedCell))) := do
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
      discard <| document.cellAddress environment source.targetDeclaration.id
      pure ((← read environment source.targetDeclaration.id).map fun cell => .value (environment, cell))

/-- Classify the shared selected-cell read only after relevance and address selection are settled. -/
def CheckedSemanticIndexSource.observePartialDocument (source : CheckedSemanticIndexSource model)
    (document : CheckedDocument model) (scope : ValidationRelevanceScope) (outer : Env)
    (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell)) :
    Except CheckedAddressingError (Option CellObservation) := do
  match ← source.readPartialDocumentCell document scope outer read with
  | none => pure none
  | some .empty => pure (some .empty)
  | some (.unknown cause) => pure (some (.unknown cause))
  | some (.poison cause) => pure (some (.poison cause))
  | some (.value (_, cell)) => pure (some (observeCell .validation cell))

/-- The available concrete extent and its completeness are independent: partial list quantifiers
can use a witness even when no identifier covers every reopened row (spec/10 §5). -/
structure PartialSelectedExtent where
  addresses : List (FlatFieldDecl × Env)
  hasUninstantiatedTail : Bool
  extentRelevant : Bool

/-- Resolve selection and topology while retaining concrete witnesses under incomplete extent.
Missing selection still needs independent wildcard target coverage (spec/10 §5). -/
def resolvePartialSelectedExtent
    (source : Sum (CheckedSemanticIndexSource model) (CheckedKeyedEntityExtent model))
    (document : CheckedDocument model) (scope : ValidationRelevanceScope) (outer : Env)
    (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell))
    (extentRelevant : FlatFieldDecl → List RepeatableLevel → List RepeatableLevel → Env → Bool := fun _ _ _ _ => true)
    (requireComplete : Bool := false) :
    Except CheckedAddressingError
      (Option (CellObservation PartialSelectedExtent)) := do
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
      pure (some (.value { addresses := [], hasUninstantiatedTail := omitted, extentRelevant := true }))
  | some (.value environment) =>
      let declarations := match source with | .inl selected => [selected.targetDeclaration] | .inr selected => selected.declarations
      let bound := selection.indexDeclaration.repeatableScope
      let complete := declarations.all (fun declaration => extentRelevant declaration bound
          (declaration.repeatableScope.drop bound.length) environment)
      if requireComplete && !complete then return none
      match source with
      | .inl selected => pure (some (.value { addresses := [(selected.targetDeclaration, environment)], hasUninstantiatedTail := false, extentRelevant := complete }))
      | .inr selected =>
          let rows ← selected.rows document.source.toDocument environment |>.mapError .addressing
          pure (some (.value {
            addresses := rows.flatMap fun (declaration, environments, _) => environments.map (declaration, ·)
            hasUninstantiatedTail := rows.any (·.2.2), extentRelevant := complete }))

/-- Count and aggregate consumers require complete extent before scanning; prefix consumers use
an always-true extent predicate and retain their call-local per-cell gate. -/
def resolvePartialSelectedAddresses
    (source : Sum (CheckedSemanticIndexSource model) (CheckedKeyedEntityExtent model))
    (document : CheckedDocument model) (scope : ValidationRelevanceScope) (outer : Env)
    (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell))
    (extentRelevant : FlatFieldDecl → List RepeatableLevel → List RepeatableLevel → Env → Bool := fun _ _ _ _ => true) :
    Except CheckedAddressingError
      (Option (CellObservation (List (FlatFieldDecl × Env) × Bool))) := do
  match ← resolvePartialSelectedExtent source document scope outer read extentRelevant (requireComplete := true) with
  | none => pure none
  | some .empty => pure (some .empty)
  | some (.unknown cause) => pure (some (.unknown cause))
  | some (.poison cause) => pure (some (.poison cause))
  | some (.value extent) => pure (if extent.extentRelevant then
      some (.value (extent.addresses, extent.hasUninstantiatedTail)) else none)

end A12Kernel
