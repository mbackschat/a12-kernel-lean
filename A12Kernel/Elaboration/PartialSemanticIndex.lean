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
  let selected ← column.toSemanticIndexColumn view.index source.indexDeclaration.id outer
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
  /-- The declarations whose selected extent keeps an uninstantiated tail, for `Sum`'s
  per-declaration missing direction (spec/10 §4). -/
  omitted : List FlatFieldDecl := []

/-- Consumer-specific extent judgment: list quantifiers cover declared slots, whereas counts and aggregates retain their own predicate (spec/10 §5). -/
inductive PartialSelectedExtentCoverage where
  | consumer (test : FlatFieldDecl → List RepeatableLevel → List RepeatableLevel → Env → Bool)
  | declaredSlots

/-- Resolve selection and topology while retaining concrete witnesses under incomplete extent.
Missing selection requires wildcard coverage at the indexed parent; the consumer decides lower-slot coverage and absent-star omission (spec/10 §5). -/
def resolvePartialSelectedExtent
    (source : Sum (CheckedSemanticIndexSource model) (CheckedKeyedEntityExtent model))
    (document : CheckedDocument model) (scope : ValidationRelevanceScope) (outer : Env)
    (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell))
    (coverage : PartialSelectedExtentCoverage := .consumer (fun _ _ _ _ => true))
    (requireComplete : Bool := false) (missingStarIsOmitted : Bool := false) :
    Except CheckedAddressingError
      (Option (CellObservation PartialSelectedExtent)) := do
  let view ← document.applyPartialGeneratedPreliminaryForScope scope |>.mapError .indexPreliminary
  let selection := match source with | .inl selected => selected | .inr selected => selected.selection.indexSource
  let complete (declarations : List FlatFieldDecl) (bound : List RepeatableLevel)
      (environment : Env) (missingParent : Option RepeatableLevel) : Except CheckedAddressingError Bool :=
    declarations.allM fun declaration => do
      let reopened := declaration.repeatableScope.drop bound.length
      match coverage with
      | .consumer test => pure (
          (missingParent.isNone || view.relevance.coversValueListExtent model declaration.path bound reopened environment) &&
          test declaration bound reopened environment)
      | .declaredSlots =>
          view.relevance.coversDeclaredFieldExtent model declaration.path reopened environment missingParent |>.mapError .addressing
  match ← selection.selectPartial view outer read with
  | none => pure none
  | some (.unknown cause) => pure (some (.unknown cause))
  | some (.poison cause) => pure (some (.poison cause))
  | some .empty =>
      let declarations := match source with | .inl selected => [selected.targetDeclaration] | .inr selected => selected.declarations
      let bound := selection.indexDeclaration.repeatableScope.dropLast
      if !(← complete declarations bound outer (some selection.group.level)) then return none
      let omitted := match source with
        | .inl _ => false
        | .inr selected => match selected.target with | .group _ => true | _ => missingStarIsOmitted
      pure (some (.value { addresses := [], hasUninstantiatedTail := omitted, extentRelevant := true
                           omitted := if omitted then declarations else [] }))
  | some (.value environment) =>
      let declarations := match source with | .inl selected => [selected.targetDeclaration] | .inr selected => selected.declarations
      let bound := selection.indexDeclaration.repeatableScope
      let complete ← complete declarations bound environment none
      if requireComplete && !complete then return none
      match source with
      | .inl selected => pure (some (.value { addresses := [(selected.targetDeclaration, environment)], hasUninstantiatedTail := false, extentRelevant := complete }))
      | .inr selected =>
          let rows ← selected.rows document.source.toDocument environment |>.mapError .addressing
          pure (some (.value {
            addresses := rows.flatMap fun (declaration, environments, _) => environments.map (declaration, ·)
            hasUninstantiatedTail := rows.any (·.2.2), extentRelevant := complete
            omitted := (rows.filter (·.2.2)).map (·.1) }))

/-- Count and aggregate consumers require complete extent before scanning; prefix consumers use
an always-true extent predicate and retain their call-local per-cell gate. -/
def resolvePartialSelectedAddresses
    (source : Sum (CheckedSemanticIndexSource model) (CheckedKeyedEntityExtent model))
    (document : CheckedDocument model) (scope : ValidationRelevanceScope) (outer : Env)
    (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell))
    (extentRelevant : FlatFieldDecl → List RepeatableLevel → List RepeatableLevel → Env → Bool := fun _ _ _ _ => true)
    (missingStarIsOmitted : Bool := false) :
    Except CheckedAddressingError
      (Option (CellObservation (List (FlatFieldDecl × Env) × Bool))) := do
  match ← resolvePartialSelectedExtent source document scope outer read (.consumer extentRelevant) (requireComplete := true)
      (missingStarIsOmitted := missingStarIsOmitted) with
  | none => pure none
  | some .empty => pure (some .empty)
  | some (.unknown cause) => pure (some (.unknown cause))
  | some (.poison cause) => pure (some (.poison cause))
  | some (.value extent) => pure (if extent.extentRelevant then
      some (.value (extent.addresses, extent.hasUninstantiatedTail)) else none)

end A12Kernel
