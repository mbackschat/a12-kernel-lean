import A12Kernel.Elaboration.TokenEntityGroup

/-! # Checked String/Enumeration entity lists

This boundary certifies the shared field entity-list shape as the Kernel's String/Enumeration token family. The common stored-only surface remains shared by distinct count and first-filled consumers, while the checked field/star representation can retain an exact category projection for a consumer whose syntax admits one. Caller-supplied checked cells let a prepared custom String participate without resampling its validator. Individual consumers retain their own authoring, evaluation, relevance, empty-result, and phase-projection rules.

A group-scope slot is retained by [`TokenEntityGroup`](TokenEntityGroup.lean) and enters here as a fourth operand shape. It is the reason the operand-level projection queries below are **list**-valued: a group reaches many declarations, and a token cell's meaning depends on the declaration that stored it, so an accessor returning one operand for a whole slot would encode a hidden one-declaration assumption.
-/

namespace A12Kernel

/-- String/ordinary stored-Enumeration consumers use the common field entity-list shape. -/
abbrev SurfaceTokenEntityOperand := SurfaceFieldEntityOperand

/-- A nonempty authored token-family entity-list source. -/
abbrev SurfaceTokenEntitySource := SurfaceFieldEntitySource

/-- One projection-bearing token slot retains the exact stored/category selection on a direct or starred field reference. -/
inductive SurfaceProjectedTokenEntityOperand where
  | field (source : SurfaceTextFieldOperand)
  | star (source : SurfaceStarFieldPath)
      (projectionRef : EnumerationProjectionRef)
  | starHaving (source : SurfaceStarFieldPath)
      (projectionRef : EnumerationProjectionRef)
      (having : SurfaceCorrelatedHaving)
  deriving Repr, DecidableEq

/-- A nonempty projection-bearing token-family entity list. -/
structure SurfaceProjectedTokenEntitySource where
  first : SurfaceProjectedTokenEntityOperand
  rest : List SurfaceProjectedTokenEntityOperand
  deriving Repr, DecidableEq

/-- The exact stored/category selection carried by one checked token operand. String has no Enumeration projection, so this is a property of the operand rather than of the slot that authored it. -/
def FlatTextFieldOperand.projectionRef? :
    FlatTextFieldOperand → Option EnumerationProjectionRef
  | .string _ => none
  | .enumeration operand => some operand.projectionRef

/-- One direct nonrepeatable String or stored/category Enumeration declaration. -/
structure CheckedTokenField (model : FlatModel) where
  declaration : FlatFieldDecl
  projectionRef : EnumerationProjectionRef
  operand : FlatTextFieldOperand
  profile : DirectComparableField
  operandOwned :
    declaration.toTokenFieldComparison? projectionRef = some (operand, profile)
  admitted : model.admitsField operand.field = true

/-- One starred String or stored/category Enumeration declaration with its exact optional checked filter. -/
structure CheckedTokenStarSource (model : FlatModel) where
  source : CheckedStarFieldPath model
  projectionRef : EnumerationProjectionRef
  operand : FlatTextFieldOperand
  profile : DirectComparableField
  operandOwned :
    source.declaration.toTokenFieldComparison? projectionRef =
      some (operand, profile)
  declaringGroup : GroupPath
  filter : Option (CheckedStarHaving model source declaringGroup)

/-- One checked token-family slot retains its direct owner, its general starred owner, or the certified expansion of an authored group scope. -/
inductive CheckedTokenEntityOperand (model : FlatModel) where
  | field (source : CheckedTokenField model)
  | star (source : CheckedTokenStarSource model)
  | group (source : CheckedTokenEntityGroup model)

namespace CheckedTokenEntityOperand

structure DirectReference where
  field : FieldId
  projection : Option EnumerationProjectionRef
  deriving Repr, DecidableEq

def directReference? : CheckedTokenEntityOperand model →
    Option DirectReference
  | .field source =>
      some {
        field := source.operand.field.id
        projection := source.operand.projectionRef? }
  | .star _ | .group _ => none

/-- Whether one authored slot satisfies the multiple-operand requirement by itself. A star denotes a row set and a group denotes a field scope, so both are already-many; this is deliberately weaker than "is a star". -/
def isAlreadyMany : CheckedTokenEntityOperand model → Bool
  | .field _ => false
  | .star _ | .group _ => true

def hasHaving : CheckedTokenEntityOperand model → Bool
  | .field _ | .group _ => false
  | .star source => source.filter.isSome

/-- The retained group slot, for a consumer that must re-render or analyse the authored operand. -/
def groupSlot? :
    CheckedTokenEntityOperand model → Option (CheckedTokenEntityGroup model)
  | .group source => some source
  | .field _ | .star _ => none

/-- Every checked String/Enumeration operand this slot reads through. A field-denoting slot carries exactly one; a group carries its whole certified expansion, because a group declares no operand of its own and two Enumeration declarations under it resolve different projections. -/
def tokenOperands :
    CheckedTokenEntityOperand model → List FlatTextFieldOperand
  | .field source => [source.operand]
  | .star source => [source.operand]
  | .group source => source.slots.map (·.operand)

/-- The stored/category selection of each operand the slot reads through, in the same order. -/
def projectionRefs (checked : CheckedTokenEntityOperand model) :
    List (Option EnumerationProjectionRef) :=
  checked.tokenOperands.map FlatTextFieldOperand.projectionRef?

def referencesField (checked : CheckedTokenEntityOperand model)
    (field : FieldId) : Bool :=
  match checked with
  | .field source => source.operand.field.id == field
  | .star source =>
      source.operand.field.id == field ||
        match source.filter with
        | none => false
        | some having => having.condition.referencesField field
  | .group source => source.referencesField field

end CheckedTokenEntityOperand

private def firstDuplicateDirectTokenReference? :
    List (CheckedTokenEntityOperand model) →
      Option CheckedTokenEntityOperand.DirectReference
  | [] => none
  | operand :: remaining =>
      match operand.directReference? with
      | none => firstDuplicateDirectTokenReference? remaining
      | some reference =>
          if remaining.any fun candidate =>
              candidate.directReference? == some reference then
            some reference
          else
            firstDuplicateDirectTokenReference? remaining

def firstDuplicateDirectTokenField? :
    List (CheckedTokenEntityOperand model) → Option FieldId
  | operands =>
      match firstDuplicateDirectTokenReference? operands with
      | some duplicate => some duplicate.field
      | none => none

/-- A checked homogeneous token-family list. Wildcard occurrences remain independent; the shared shape has already excluded repeated direct references, repeated fixed groups, and strict overlap. -/
structure CheckedTokenEntitySource (model : FlatModel) where
  first : CheckedTokenEntityOperand model
  rest : List (CheckedTokenEntityOperand model)
  modelWellFormed : model.validate.isOk = true
  requiredMultiplicity : (first.isAlreadyMany || !rest.isEmpty) = true
  uniqueDirectOperands :
    firstDuplicateDirectTokenField? (first :: rest) = none

namespace CheckedTokenEntitySource

def operands (checked : CheckedTokenEntitySource model) :
    List (CheckedTokenEntityOperand model) :=
  checked.first :: checked.rest

def hasHaving (checked : CheckedTokenEntitySource model) : Bool :=
  checked.operands.any (fun operand => operand.hasHaving)

def referencesField (checked : CheckedTokenEntitySource model)
    (field : FieldId) : Bool :=
  checked.operands.any (fun operand => operand.referencesField field)

end CheckedTokenEntitySource

inductive TokenEntityElabError where
  | shape (error : FieldEntityShapeElabError)
  | fieldKindMismatch (path : List String) (actual : SurfaceScalarKind)
  | rawStringValue (path : List String)
  | enumerationOperand (path : List String) (error : EnumerationOperandError)
  | having (error : CorrelationElabError)
  /-- A group-scope slot the token family cannot certify. Its two arms are representation limits rather than Kernel gates, and the consumer that runs the shared whole-list kind and category scans first classifies a mixed subtree there instead. -/
  | group (error : TokenEntityGroupError)
  | incoherentCore
  deriving Repr, DecidableEq

private def checkedTokenOperand? (declaration : FlatFieldDecl)
    (projectionRef : EnumerationProjectionRef) :
    Option (FlatTextFieldOperand × DirectComparableField) :=
  declaration.toTokenFieldComparison? projectionRef

def certifyDirectTokenOperand (model : FlatModel)
    (declaration : FlatFieldDecl)
    (projectionRef : EnumerationProjectionRef := .stored) :
    Except TokenEntityElabError (CheckedTokenField model) :=
  match hOperand : checkedTokenOperand? declaration projectionRef with
  | none =>
      match declaration.policy.kind, projectionRef with
      | .enumeration, .category name =>
          throw (.enumerationOperand declaration.path (.unknownCategory name))
      | _, _ =>
          if declaration.isRawString then
            throw (.rawStringValue declaration.path)
          else
            throw (.fieldKindMismatch declaration.path
              declaration.policy.kind.surfaceKind)
  | some (operand, profile) =>
      if hAdmitted : model.admitsField operand.field = true then
        pure {
          declaration
          projectionRef
          operand
          profile
          operandOwned := hOperand
          admitted := hAdmitted }
      else
        throw .incoherentCore

def certifyStarTokenOperand (declaringGroup : GroupPath)
    (source : CheckedStarFieldPath model)
    (having : Option SurfaceCorrelatedHaving)
    (projectionRef : EnumerationProjectionRef := .stored) :
    Except TokenEntityElabError
      (CheckedTokenStarSource model) :=
  match hOperand : checkedTokenOperand? source.declaration projectionRef with
  | none =>
      match source.declaration.policy.kind, projectionRef with
      | .enumeration, .category name =>
          throw (.enumerationOperand source.declaration.path
            (.unknownCategory name))
      | _, _ =>
          if source.declaration.isRawString then
            throw (.rawStringValue source.declaration.path)
          else
            throw (.fieldKindMismatch source.declaration.path
              source.declaration.policy.kind.surfaceKind)
  | some (operand, profile) => do
      let filter ← match having with
        | none => pure none
        | some authored =>
            pure (some (← elaborateStarHavingCore model declaringGroup source authored
              |>.mapError .having))
      pure {
        source
        projectionRef
        operand
        profile
        operandOwned := hOperand
        declaringGroup
        filter }

private def certifyTokenEntityOperand (model : FlatModel)
    (declaringGroup : GroupPath) : ResolvedFieldEntityOperand model →
      Except TokenEntityElabError (CheckedTokenEntityOperand model)
  | .field declaration _ =>
      do pure (.field (← certifyDirectTokenOperand model declaration))
  | .star source =>
      do pure (.star (← certifyStarTokenOperand declaringGroup source none))
  | .starHaving source having =>
      do pure (.star (← certifyStarTokenOperand declaringGroup source (some having)))
  | .group reference =>
      do pure (.group (← certifyTokenEntityGroup model (.fixed reference)
        |>.mapError .group))
  | .starredGroup source =>
      do pure (.group (← certifyTokenEntityGroup model (.starred source)
        |>.mapError .group))
  | .starredGroupPresence source =>
      do pure (.group (← certifyTokenEntityGroup model (.starredPresence source)
        |>.mapError .group))

private def certifyTokenEntityOperands (model : FlatModel)
    (declaringGroup : GroupPath) : List (ResolvedFieldEntityOperand model) →
      Except TokenEntityElabError
        (List (CheckedTokenEntityOperand model))
  | [] => pure []
  | operand :: remaining => do
      pure ((← certifyTokenEntityOperand model declaringGroup operand) ::
        (← certifyTokenEntityOperands model declaringGroup remaining))

/-- Finish one checked token entity list after its consumer has resolved and certified every slot. Exact direct-reference identity retains category selection, while wildcard occurrences remain independent. -/
def assembleTokenEntitySource
    (modelWellFormed : model.validate.isOk = true)
    (first : CheckedTokenEntityOperand model)
    (rest : List (CheckedTokenEntityOperand model)) :
    Except TokenEntityElabError (CheckedTokenEntitySource model) :=
  if hMultiplicity : (first.isAlreadyMany || !rest.isEmpty) = true then
    match hDuplicate :
        firstDuplicateDirectTokenField? (first :: rest) with
    | some field => throw (.shape (.duplicateOperand field))
    | none => pure {
        first
        rest
        modelWellFormed
        requiredMultiplicity := hMultiplicity
        uniqueDirectOperands := hDuplicate }
  else
    throw (.shape .tooFewFields)

/-- Certify an already checked entity-list shape as String/ordinary stored-Enumeration without
    resolving it again. A consumer may run its own whole-list gate before entering this boundary. -/
def certifyTokenEntityShape (model : FlatModel)
    (declaringGroup : GroupPath) (shape : CheckedFieldEntityShape model) :
    Except TokenEntityElabError (CheckedTokenEntitySource model) := do
  let first ← certifyTokenEntityOperand model declaringGroup shape.first
  let rest ← certifyTokenEntityOperands model declaringGroup shape.rest
  assembleTokenEntitySource shape.modelWellFormed first rest

/-- Resolve duplicate/cardinality shape before certifying the complete list as String/ordinary stored-Enumeration. -/
def elaborateTokenEntitySource (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceTokenEntitySource) :
    Except TokenEntityElabError (CheckedTokenEntitySource model) := do
  let shape ← elaborateFieldEntityShape model declaringGroup authored
    |>.mapError .shape
  certifyTokenEntityShape model declaringGroup shape

/-- A path-resolved projection-bearing token slot. Keeping this intermediate private preserves duplicate-before-certification diagnostics without exposing a second checked representation. -/
private inductive ResolvedProjectedTokenEntityOperand
    (model : FlatModel) where
  | field (declaration : FlatFieldDecl)
      (projectionRef : EnumerationProjectionRef)
  | star (source : CheckedStarFieldPath model)
      (projectionRef : EnumerationProjectionRef)
      (having : Option SurfaceCorrelatedHaving)

namespace ResolvedProjectedTokenEntityOperand

private def isStar :
    ResolvedProjectedTokenEntityOperand model → Bool
  | .field _ _ => false
  | .star _ _ _ => true

private def directReference? :
    ResolvedProjectedTokenEntityOperand model →
      Option (FieldId × EnumerationProjectionRef)
  | .field declaration projectionRef => some (declaration.id, projectionRef)
  | .star _ _ _ => none

end ResolvedProjectedTokenEntityOperand

private def resolveProjectedTokenEntityOperand (model : FlatModel)
    (declaringGroup : GroupPath) :
    SurfaceProjectedTokenEntityOperand →
      Except TokenEntityElabError
        (ResolvedProjectedTokenEntityOperand model)
  | .field source => do
      let reference := match source with
        | .direct field | .category field _ => field
      let projectionRef := match source with
        | .direct _ => EnumerationProjectionRef.stored
        | .category _ name => .category name
      let declaration ←
        (model.resolveNonrepeatableFieldUnchecked declaringGroup reference).mapError
          (fun error => .shape (.resolve error))
      pure (.field declaration projectionRef)
  | .star source projectionRef => do
      let checked ← elaborateStarFieldPath model declaringGroup source
        |>.mapError (fun error => .shape (.starPath error))
      pure (.star checked projectionRef none)
  | .starHaving source projectionRef having => do
      let checked ← elaborateStarFieldPath model declaringGroup source
        |>.mapError (fun error => .shape (.starPath error))
      pure (.star checked projectionRef (some having))

private def firstDuplicateResolvedProjectedTokenField? :
    List (ResolvedProjectedTokenEntityOperand model) → Option FieldId
  | [] => none
  | operand :: remaining =>
      match operand.directReference? with
      | none => firstDuplicateResolvedProjectedTokenField? remaining
      | some reference =>
          if remaining.any fun candidate =>
              candidate.directReference? == some reference then
            some reference.1
          else
            firstDuplicateResolvedProjectedTokenField? remaining

private def certifyProjectedTokenEntityOperand (model : FlatModel)
    (declaringGroup : GroupPath) :
    ResolvedProjectedTokenEntityOperand model →
      Except TokenEntityElabError (CheckedTokenEntityOperand model)
  | .field declaration projectionRef => do
      pure (.field
        (← certifyDirectTokenOperand model declaration projectionRef))
  | .star source projectionRef having => do
      pure (.star
        (← certifyStarTokenOperand declaringGroup source having projectionRef))

/-- Resolve paths before exact-reference duplication and cardinality, then certify kind, category, and `Having` in authored order. This is the sole projection-bearing token entity-list authoring boundary. -/
def elaborateProjectedTokenEntitySource (model : FlatModel)
    (declaringGroup : GroupPath)
    (authored : SurfaceProjectedTokenEntitySource) :
    Except TokenEntityElabError (CheckedTokenEntitySource model) :=
  match hModel : model.validate with
  | .error error => .error (.shape (.resolve error))
  | .ok () => do
      let first ←
        resolveProjectedTokenEntityOperand model declaringGroup authored.first
      let rest ← authored.rest.mapM fun operand =>
        resolveProjectedTokenEntityOperand model declaringGroup operand
      match firstDuplicateResolvedProjectedTokenField? (first :: rest) with
      | some field => throw (.shape (.duplicateOperand field))
      | none =>
          if first.isStar || !rest.isEmpty then
            let checkedFirst ←
              certifyProjectedTokenEntityOperand model declaringGroup first
            let checkedRest ← rest.mapM fun operand =>
              certifyProjectedTokenEntityOperand model declaringGroup operand
            assembleTokenEntitySource (by rw [hModel]; rfl)
              checkedFirst checkedRest
          else
            throw (.shape .tooFewFields)

/-- One authored String/stored-or-category Enumeration operand resolved against the immutable checked input.

    `projectedCells` pairs every reached cell with the operand that must read it. A field-denoting slot repeats its one operand; a group carries the declaration that stored each cell, because an Enumeration cell is classified through its own declaration's resolved projection and the first expanded declaration's would silently misread a sibling that declares a different enumeration. The constructor is private so the pairing can only come from the two resolvers below, each of which builds it in the same walk that produced the cell. -/
structure ResolvedCheckedTokenEntityOperand (model : FlatModel) where
  private mk ::
  source : CheckedTokenEntityOperand model
  projectedCells : List (FlatTextFieldOperand × CheckedAddressedCell)
  topology : Option ResolvedStarTopology
  hasUninstantiatedTail : Bool
  hasHaving : Bool
  hasNonRelevant : Bool

namespace ResolvedCheckedTokenEntityOperand

/-- Pair every cell of a field-denoting slot's shared core with that slot's one operand. -/
private def ofCore (source : CheckedTokenEntityOperand model)
    (operand : FlatTextFieldOperand)
    (core : ResolvedCheckedEntityOperandCore) :
    ResolvedCheckedTokenEntityOperand model :=
  { source
    projectedCells := core.addressedCells.map fun cell => (operand, cell)
    topology := core.topology
    hasUninstantiatedTail := core.hasUninstantiatedTail
    hasHaving := core.hasHaving
    hasNonRelevant := core.hasNonRelevant }

/-- A group slot reaches only instantiated rows through the model's own repeatability, so it has no star topology, no filter, and no omitted tail. -/
private def ofGroupCells (source : CheckedTokenEntityOperand model)
    (cells : List (FlatTextFieldOperand × CheckedAddressedCell))
    (hasNonRelevant : Bool := false) :
    ResolvedCheckedTokenEntityOperand model :=
  { source
    projectedCells := cells
    topology := none
    hasUninstantiatedTail := false
    hasHaving := false
    hasNonRelevant }

def addressedCells (resolved : ResolvedCheckedTokenEntityOperand model) :
    List CheckedAddressedCell :=
  resolved.projectedCells.map Prod.snd

/-- Apply each cell's own declaration-owned String or Enumeration/category projection. -/
def valueListSideAt (resolved : ResolvedCheckedTokenEntityOperand model)
    (phase : Phase) : ResolvedValueListSide .token :=
  { cells := resolved.projectedCells.map fun (operand, addressed) =>
      operand.checkedValueListCellAt phase addressed.cell
    hasUninstantiatedTail := resolved.hasUninstantiatedTail
    hasHaving := resolved.hasHaving
    hasNonRelevant := resolved.hasNonRelevant }

/-- Project away cells beneath a declared-capacity violation while preserving each reached declaration's exact token projection. Every consumer the two accounts separate reads this one; `valueListSideAt` remains for `FieldValuesNotUnique`, whose skip-on-unavailable rule already reaches the same verdict ([checkpoint](../../docs/SOURCES.md#src-capacity-consumer-sweep)). -/
def inCapacityValueListSideAt
    (resolved : ResolvedCheckedTokenEntityOperand model)
    (phase : Phase) : ResolvedValueListSide .token :=
  { cells := (resolved.projectedCells.filter fun (_, addressed) =>
      !addressed.cell.findings.contains .overRepetition).map
        fun (operand, addressed) =>
          operand.checkedValueListCellAt phase addressed.cell
    hasUninstantiatedTail := resolved.hasUninstantiatedTail
    hasHaving := resolved.hasHaving
    hasNonRelevant := resolved.hasNonRelevant }

end ResolvedCheckedTokenEntityOperand

namespace CheckedTokenField

/-- Classify one caller-supplied checked direct cell; this permits prepared custom String checking without moving that host concern into the aggregate. -/
def valueListCellAt (checked : CheckedTokenField model)
    (phase : Phase) (read : FieldId → CheckedCell) : ValueListCell .token :=
  checked.operand.checkedValueListCellAt phase (read checked.operand.field.id)

def resolvedSideAt (checked : CheckedTokenField model)
    (phase : Phase) (read : FieldId → CheckedCell) :
    ResolvedValueListSide .token :=
  { cells := [checked.valueListCellAt phase read]
    hasUninstantiatedTail := false
    hasHaving := false }

end CheckedTokenField

namespace CheckedTokenStarSource

/-- Apply path-owned over-repetition to one caller-supplied checked leaf, then project its exact String/stored-or-category Enumeration token. -/
def valueListCellAt (checked : CheckedTokenStarSource model)
    (phase : Phase) (read : Env → FieldId → CheckedCell)
    (environment : Env) : ValueListCell .token :=
  checked.operand.checkedValueListCellAt phase
    (checked.source.contextualizeCell environment
      (read environment checked.operand.field.id))

/-- Unfiltered phase-indexed resolution is the reusable boundary for a later computation consumer. Filtered computation remains deliberately unsupported. -/
def resolvedUnfilteredSideAt (checked : CheckedTokenStarSource model)
    (phase : Phase) (document : Document) (outer : Env)
    (read : Env → FieldId → CheckedCell)
    (_unfiltered : checked.filter.isNone = true) :
    Except StarAddressingError (ResolvedValueListSide .token) :=
  checked.source.resolvedValueListSide document outer
    (checked.valueListCellAt phase read)

/-- Full validation resolves topology and its optional checked filter before classifying selected token cells. -/
def resolvedValidationSide (checked : CheckedTokenStarSource model)
    (document : Document) (outer : Env)
    (read : Env → FieldId → CheckedCell) :
    Except StarAddressingError (ResolvedValueListSide .token) :=
  checked.source.resolvedOptionalValidationHavingValueListSide document outer
    checked.filter read (checked.valueListCellAt .validation read)

/-- Partial all-rows validation checks wildcard/ancestor extent before reading any selected target. Filtered rules are skipped by the owning whole-source consumer. -/
def resolvedPartialValidationSide
    (checked : CheckedTokenStarSource model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → CheckedCell)
    (_unfiltered : checked.filter.isNone = true) :
    Except StarAddressingError
      (Sum (ResolvedValueListSide .token) Unit) := do
  let resolved ← checked.source.path.resolve document outer
  if checked.source.allRowsRelevant scope outer then
    pure (.inl (resolved.toResolvedSide
      (checked.valueListCellAt .validation read)))
  else
    pure (.inr ())

/-- Resolve token `NumberOfValueInFields` through the same local existential value-list account as its numeric overload. -/
def resolvedPartialValueCountSide
    (checked : CheckedTokenStarSource model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → CheckedCell)
    (_unfiltered : checked.filter.isNone = true) :
    Except StarAddressingError
      (Sum (ResolvedValueListSide .token) Unit) := do
  let resolved ← checked.source.path.resolve document outer
  if checked.source.valueListExtentRelevant scope outer then
    pure (.inl (resolved.toResolvedSide
      (checked.valueListCellAt .validation read)))
  else
    pure (.inr ())

end CheckedTokenStarSource

namespace CheckedTokenEntityOperand

/-- Resolve one full-validation token operand through the sole checked topology, filter, and addressed-cell owners while retaining its exact String/Enumeration projection certificate. A group slot reads its whole `(row × field)` extent from the model's repeatability through the same shared walk. -/
def resolveCheckedValidationOperand
    (source : CheckedTokenEntityOperand model)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError
      (ResolvedCheckedTokenEntityOperand model) :=
  match source with
  | .field direct => do
      let core ←
        document.resolveCheckedDirectEntityOperandCore direct.operand.field.id
      pure (.ofCore source direct.operand core)
  | .star starSource => do
      let having := starSource.filter.map fun filter => filter.condition
      let core ←
        starSource.source.resolveCheckedValidationEntityOperandCore
          document outer having
      pure (.ofCore source starSource.operand core)
  | .group slot => do
      pure (.ofGroupCells source
        (← slot.resolveCheckedValidationCells document outer))

/-- Resolve one partial-validation token operand without collapsing nonrelevance into a semantic cell. Filtered rules remain suppressed by the owning whole-source gate.

    A group slot retains relevant concrete cells per expanded declaration and records complete extent only when every expanded declaration has one covering wildcard identifier. -/
def resolveCheckedPartialValidationOperand
    (source : CheckedTokenEntityOperand model)
    (document : CheckedDocument model) (outer : Env)
    (scope : ValidationRelevanceScope) :
    Except CheckedAddressingError
      (ResolvedCheckedTokenEntityOperand model) :=
  match source with
  | .field direct =>
      if scope.coversCell model direct.declaration.path [] then do
        let core ←
          document.resolveCheckedDirectEntityOperandCore direct.operand.field.id
        pure (.ofCore source direct.operand core)
      else
        pure (.ofCore source direct.operand .nonRelevant)
  | .star starSource =>
      match starSource.filter with
      | some _ => pure (.ofCore source starSource.operand .skippedHaving)
      | none => do
          let core ←
            starSource.source.resolveCheckedPartialValidationEntityOperandCore
              document outer scope
          pure (.ofCore source starSource.operand core)
  | .group slot => do
      let (cells, hasNonRelevant) ←
        slot.resolveCheckedPartialValidationCells document outer scope
      pure (.ofGroupCells source cells hasNonRelevant)

/-- Resolve one direct or starred token slot for full validation through the shared declaration-owned classifier.

    The three raw-`Document` routes below all refuse a group slot. Its extent is enumerated from the **model's** repeatability against instantiated rows, which only the immutable checked document can answer; the caller-supplied read functions here cannot say which rows exist. `resolveCheckedValidationOperand` above is the route that serves a group. -/
def resolvedValidationSide (checked : CheckedTokenEntityOperand model)
    (document : Document) (outer : Env)
    (directRead : FieldId → CheckedCell)
    (starRead : Env → FieldId → CheckedCell) :
    Except StarAddressingError (ResolvedValueListSide .token) :=
  match checked with
  | .field source => pure (source.resolvedSideAt .validation directRead)
  | .star source => source.resolvedValidationSide document outer starRead
  | .group slot => .error (.unsupportedGroupOperand slot.groupPath)

/-- Resolve one unfiltered token slot under partial-validation relevance, preserving rule-level skip/nonrelevance outside the cell domain. -/
def resolvedPartialValidationSide
    (checked : CheckedTokenEntityOperand model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (directRead : FieldId → CheckedCell)
    (starRead : Env → FieldId → CheckedCell) :
    Except StarAddressingError
      (Sum (ResolvedValueListSide .token) PartialValidationAggregateResult) :=
  match checked with
  | .field source =>
      if scope.coversCell model source.declaration.path [] then
        pure (.inl (source.resolvedSideAt .validation directRead))
      else
        pure (.inr .nonRelevant)
  | .star source =>
      if hUnfiltered : source.filter.isNone = true then do
        match ← source.resolvedPartialValidationSide document outer scope
            starRead hUnfiltered with
        | .inl side => pure (.inl side)
        | .inr () => pure (.inr .nonRelevant)
      else
        pure (.inr .skippedHaving)
  | .group slot => .error (.unsupportedGroupOperand slot.groupPath)

/-- Resolve one partial token value-count slot without importing the measured combiner gate used by `resolvedPartialValidationSide`. -/
def resolvedPartialValueCountSide
    (checked : CheckedTokenEntityOperand model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (directRead : FieldId → CheckedCell)
    (starRead : Env → FieldId → CheckedCell) :
    Except StarAddressingError
      (Sum (ResolvedValueListSide .token) PartialValidationAggregateResult) :=
  match checked with
  | .field source =>
      if scope.coversCell model source.declaration.path [] then
        pure (.inl (source.resolvedSideAt .validation directRead))
      else
        pure (.inr .nonRelevant)
  | .star source =>
      if hUnfiltered : source.filter.isNone = true then do
        match ← source.resolvedPartialValueCountSide document outer scope
            starRead hUnfiltered with
        | .inl side => pure (.inl side)
        | .inr () => pure (.inr .nonRelevant)
      else
        pure (.inr .skippedHaving)
  | .group slot => .error (.unsupportedGroupOperand slot.groupPath)

end CheckedTokenEntityOperand

end A12Kernel
