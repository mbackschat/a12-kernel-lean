import A12Kernel.Elaboration.Correlation
import A12Kernel.Elaboration.SelectedTokenEntity

/-! # Checked String/Enumeration entity lists

This boundary certifies the shared field entity-list shape as the Kernel's String/Enumeration token family. The common stored-only surface remains shared by distinct count and first-filled consumers, while the checked field/star representation can retain an exact category projection for a consumer whose syntax admits one. Caller-supplied checked cells let a prepared custom String participate without resampling its validator. Individual consumers retain their own authoring, evaluation, relevance, empty-result, and phase-projection rules.

A group-scope slot is retained by [`TokenEntityGroup`](TokenEntityGroup.lean); indexed slots retain their selection certificate and declaration-owned projections. It is the reason the operand-level projection queries below are **list**-valued: a group reaches many declarations, and a token cell's meaning depends on the declaration that stored it, so an accessor returning one operand for a whole slot would encode a hidden one-declaration assumption.
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

/-- One direct String or stored/category Enumeration declaration. The list's shape decided which reading
scope binds its levels: none on a rule, its target's on a computation. -/
structure CheckedTokenField (model : FlatModel) where
  declaration : FlatFieldDecl
  projectionRef : EnumerationProjectionRef
  operand : FlatTextFieldOperand
  profile : DirectComparableField
  operandOwned :
    declaration.toTokenFieldComparison? projectionRef = some (operand, profile)
  admitted : model.ownsField operand.field = true

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
  bindingGroup : GroupPath := declaringGroup
  filter : Option (CheckedStarHaving model source bindingGroup)

/-- A checked token slot retains its direct, indexed, starred or group owner so selection identity and declaration-owned projections survive lowering. -/
inductive CheckedTokenEntityOperand (model : FlatModel) where
  | field (source : CheckedTokenField model)
  | selected (source : CheckedSelectedTokenEntity model)
  | star (source : CheckedTokenStarSource model)
  | group (source : CheckedTokenEntityGroup model)

namespace CheckedTokenEntityOperand

structure DirectReference where
  field : FieldId
  projection : Option EnumerationProjectionRef
  deriving Repr, DecidableEq

def directField? : CheckedTokenEntityOperand model →
    Option (CheckedTokenField model)
  | .field source => some source
  | .selected _ | .star _ | .group _ => none

def directReference? : CheckedTokenEntityOperand model →
    Option DirectReference
  | .field source =>
      some {
        field := source.operand.field.id
        projection := source.operand.projectionRef? }
  | .selected _ | .star _ | .group _ => none

/-- Whether one authored slot satisfies the multiple-operand requirement by itself. A star denotes a row set and a group denotes a field scope, so both are already-many; this is deliberately weaker than "is a star". -/
def isAlreadyMany : CheckedTokenEntityOperand model → Bool
  | .field _ => false
  | .selected source => source.isAlreadyMany
  | .star _ | .group _ => true

def hasHaving : CheckedTokenEntityOperand model → Bool
  | .field _ | .selected _ | .group _ => false
  | .star source => source.filter.isSome

/-- The retained group slot, for a consumer that must re-render or analyse the authored operand. -/
def groupSlot? :
    CheckedTokenEntityOperand model → Option (CheckedTokenEntityGroup model)
  | .group source => some source
  | .field _ | .selected _ | .star _ => none

/-- Every checked String/Enumeration operand this slot reads through. A field-denoting slot carries exactly one; a group carries its whole certified expansion, because a group declares no operand of its own and two Enumeration declarations under it resolve different projections. -/
def tokenOperands :
    CheckedTokenEntityOperand model → List FlatTextFieldOperand
  | .field source => [source.operand]
  | .selected source => source.slots.map (·.operand)
  | .star source => [source.operand]
  | .group source => source.slots.map (·.operand)

/-- The stored/category selection of each operand the slot reads through, in the same order. -/
def projectionRefs (checked : CheckedTokenEntityOperand model) :
    List (Option EnumerationProjectionRef) :=
  checked.tokenOperands.map FlatTextFieldOperand.projectionRef?

/-- Whether this slot reads `field`. `filterReads` decides which of a filter's reads count: every
    read for a dependency or pointer, only the marked ones for the rule's error-field gates. -/
def referencesField (checked : CheckedTokenEntityOperand model)
    (field : FieldId)
    (filterReads : CorrelatedHaving → FieldId → Bool := CorrelatedHaving.referencesField) :
    Bool :=
  match checked with
  | .field source => source.operand.field.id == field
  | .selected source => source.referencesField field
  | .star source =>
      source.operand.field.id == field ||
        match source.filter with
        | none => false
        | some having => filterReads having.condition field
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
  /-- The arity rule the certifying carrier applies, carried through from the shared shape so a
  consumer can tell a sole-operand list that was *admitted* from one that never occurred. -/
  arity : EntityListArity
  requiredMultiplicity :
    (arity.allowsSole || first.isAlreadyMany || !rest.isEmpty) = true
  uniqueDirectOperands :
    firstDuplicateDirectTokenField? (first :: rest) = none

namespace CheckedTokenEntitySource

def operands (checked : CheckedTokenEntitySource model) :
    List (CheckedTokenEntityOperand model) :=
  checked.first :: checked.rest

def hasHaving (checked : CheckedTokenEntitySource model) : Bool :=
  checked.operands.any (fun operand => operand.hasHaving)

def referencesField (checked : CheckedTokenEntitySource model)
    (field : FieldId)
    (filterReads : CorrelatedHaving → FieldId → Bool := CorrelatedHaving.referencesField) :
    Bool :=
  checked.operands.any (fun operand => operand.referencesField field filterReads)

def directFields? (checked : CheckedTokenEntitySource model) :
    Option (List (CheckedTokenField model)) :=
  checked.operands.mapM CheckedTokenEntityOperand.directField?

end CheckedTokenEntitySource

def CheckedTokenEntitySource.bindingScopes (source : CheckedTokenEntitySource model) : List (List RepeatableLevel) :=
  source.operands.flatMap fun
    | .field field => [field.declaration.repeatableScope]
    | .selected source => match source.source with
      | .inl selected => selected.bindingScopes
      | .inr selected => selected.bindingScopes
    | .star source => source.source.bindingScope ::
        (if source.filter.isSome then [model.repeatableScopeForGroupPath source.bindingGroup] else [])
    | .group source => [source.source.bindingScope]


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

namespace TokenEntityElabError

/-- The Kernel class one token-list refusal draws, against a **String-literal** value list.

    The kind gate partitions three ways rather than two, and the operator's own message vocabulary
    is what makes that visible: a Number field is *inside* the admitted set the
    `MVK_ONLY_STRING_ENUM_NUMBER_ALLOWED` message names, so it passes that gate and then fails the
    literal comparison with `MVK_INVALID_TYPES_FOR_COMPARISON`, while DATE, BOOLEAN, DATE_RANGE and
    CONFIRM never reach that stage
    ([checkpoint](../../docs/SOURCES.md#src-value-list-quantifier-kind-gate-partitions-three-ways)).
    Collapsing the two would report the admitted-set class for a kind the Kernel says is admitted.

    Every other arm keeps its local identity: they are this theory's representation limits or
    delegated shape gates, not observed Kernel classes at this carrier. -/
def diagnostic? : TokenEntityElabError → Option KernelStaticDiagnostic
  | .shape error => error.diagnostic?
  | .fieldKindMismatch _ actual =>
      match actual with
      | .number => some .invalidTypesForComparison
      | .temporal _ | .boolean | .confirm | .dateRange =>
          some .onlyStringEnumNumberAllowed
      -- Both are admitted against a String-literal list, so neither reaches this arm.
      | .string | .enumeration => none
  | .having error => error.diagnostic?
  | .rawStringValue _ | .enumerationOperand _ _ | .group _
  | .incoherentCore => none

end TokenEntityElabError

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
      -- The category read's own class, ahead of the slot's value and kind gates. The stored form's
      -- shape asks it first as each operand is read; the projected form reaches it here, after every
      -- operand resolves ([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-predictions)).
      | _, .category _ =>
          throw (.shape (.resolve (.categoryReadOfNonEnumeration declaration.path)))
      | _, .stored =>
          if declaration.isRawString then
            throw (.rawStringValue declaration.path)
          else
            throw (.fieldKindMismatch declaration.path
              declaration.policy.kind.surfaceKind)
  | some (operand, profile) =>
      if hAdmitted : model.ownsField operand.field = true then
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
    (projectionRef : EnumerationProjectionRef := .stored)
    (bindingGroup : GroupPath := declaringGroup) :
    Except TokenEntityElabError
      (CheckedTokenStarSource model) :=
  match hOperand : checkedTokenOperand? source.declaration projectionRef with
  | none =>
      match source.declaration.policy.kind, projectionRef with
      | .enumeration, .category name =>
          throw (.enumerationOperand source.declaration.path
            (.unknownCategory name))
      | _, .category _ =>
          throw (.shape (.resolve (.categoryReadOfNonEnumeration source.declaration.path)))
      | _, .stored =>
          if source.declaration.isRawString then
            throw (.rawStringValue source.declaration.path)
          else
            throw (.fieldKindMismatch source.declaration.path
              source.declaration.policy.kind.surfaceKind)
  | some (operand, profile) => do
      let filter ← match having with
        | none => pure none
        | some authored =>
            pure (some (← elaborateStarHavingCore model declaringGroup source authored bindingGroup
              |>.mapError .having))
      pure {
        source
        projectionRef
        operand
        profile
        operandOwned := hOperand
        declaringGroup
        bindingGroup
        filter }

private def certifyTokenEntityOperand (model : FlatModel)
    (declaringGroup bindingGroup : GroupPath) : ResolvedFieldEntityOperand model →
      Except TokenEntityElabError (CheckedTokenEntityOperand model)
  -- The authored read form is kept: a category read certifies through its projection, which reading
  -- the field stored would silently replace.
  | .indexed source => do
      pure (.selected (← CheckedSelectedTokenEntity.certify (.inl source) |>.mapError .group))
  | .keyed source => do
      pure (.selected (← CheckedSelectedTokenEntity.certify (.inr source) |>.mapError .group))
  | .field declaration form =>
      let projectionRef : EnumerationProjectionRef := match form with
        | .stored => .stored
        | .projected category => .category category
      do pure (.field (← certifyDirectTokenOperand model declaration projectionRef))
  | .star source =>
      do pure (.star (← certifyStarTokenOperand declaringGroup source none (bindingGroup := bindingGroup)))
  | .starHaving source having =>
      do pure (.star (← certifyStarTokenOperand declaringGroup source (some having) (bindingGroup := bindingGroup)))
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
    (declaringGroup bindingGroup : GroupPath) : List (ResolvedFieldEntityOperand model) →
      Except TokenEntityElabError
        (List (CheckedTokenEntityOperand model))
  | [] => pure []
  | operand :: remaining => do
      pure ((← certifyTokenEntityOperand model declaringGroup bindingGroup operand) ::
        (← certifyTokenEntityOperands model declaringGroup bindingGroup remaining))

/-- Finish one checked token entity list after its consumer has resolved and certified every slot. Exact direct-reference identity retains category selection, while wildcard occurrences remain independent. -/
def assembleTokenEntitySource
    (modelWellFormed : model.validate.isOk = true)
    (first : CheckedTokenEntityOperand model)
    (rest : List (CheckedTokenEntityOperand model))
    (arity : EntityListArity := .manyRequired) :
    Except TokenEntityElabError (CheckedTokenEntitySource model) :=
  if hMultiplicity :
      (arity.allowsSole || first.isAlreadyMany || !rest.isEmpty) = true then
    match hDuplicate :
        firstDuplicateDirectTokenField? (first :: rest) with
    | some field => throw (.shape (.duplicateOperand field))
    | none => pure {
        first
        rest
        modelWellFormed
        arity
        requiredMultiplicity := hMultiplicity
        uniqueDirectOperands := hDuplicate }
  else
    throw (.shape .tooFewFields)

/-- Certify an already checked entity-list shape as String/ordinary stored-Enumeration without
    resolving it again. A consumer may run its own whole-list gate before entering this boundary. -/
def certifyTokenEntityShape (model : FlatModel)
    (declaringGroup : GroupPath) (shape : CheckedFieldEntityShape model)
    (bindingGroup : GroupPath := declaringGroup) :
    Except TokenEntityElabError (CheckedTokenEntitySource model) := do
  let first ← certifyTokenEntityOperand model declaringGroup bindingGroup shape.first
  let rest ← certifyTokenEntityOperands model declaringGroup bindingGroup shape.rest
  -- The shape's own rule carries through rather than being re-decided here: the arity gate has
  -- already fired (or not) upstream, so re-applying `manyRequired` would refuse a list the
  -- carrier's rule admitted.
  assembleTokenEntitySource shape.modelWellFormed first rest shape.arity

/-- Resolve duplicate/cardinality shape before certifying the complete list as String/ordinary stored-Enumeration. -/
def elaborateTokenEntitySource (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceTokenEntitySource)
    (arity : EntityListArity := .manyRequired) (writtenGroup : GroupPath := declaringGroup)
    (fixedTargetGroup? : Option GroupPath := none) (bindingGroup? : Option GroupPath := none) :
    Except TokenEntityElabError (CheckedTokenEntitySource model) := do
  let shape ← elaborateFieldEntityShapeIn model declaringGroup
      (bindingGroup?.map model.repeatableScopeForGroupPath |>.getD []) authored arity fixedTargetGroup?
      (writtenGroup := writtenGroup)
    |>.mapError .shape
  certifyTokenEntityShape model declaringGroup shape ((bindingGroup?.or fixedTargetGroup?).getD writtenGroup)

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

private def bindingScope :
    ResolvedProjectedTokenEntityOperand model → List RepeatableLevel
  | .field declaration _ => declaration.repeatableScope
  | .star source _ _ => source.bindingScope

end ResolvedProjectedTokenEntityOperand

private def resolveProjectedTokenEntityOperand (model : FlatModel)
    (declaringGroup : GroupPath) (fixedTargetGroup? : Option GroupPath) (writtenGroup : GroupPath)
    (bindingGroup? : Option GroupPath) :
    SurfaceProjectedTokenEntityOperand →
      Except TokenEntityElabError
        (ResolvedProjectedTokenEntityOperand model)
  | .field source => do
      let reference := match source with
        | .direct field | .category field _ => field
      let projectionRef := match source with
        | .direct _ => EnumerationProjectionRef.stored
        | .category _ name => .category name
      -- On a fixed-target list the field keeps its levels for the list-wide gate below, as the
      -- shared shape's field does, so the target places its refusal.
      let declaration ← (match fixedTargetGroup? with
          | some _ => model.resolveFieldDeclarationUnchecked declaringGroup reference
          | none => match bindingGroup? with
              | none => model.resolveNonrepeatableFieldUnchecked declaringGroup reference writtenGroup
              | some bindingGroup => do
                  let declaration ← model.resolveFieldDeclarationUnchecked declaringGroup reference
                  let bound := model.repeatableScopeForGroupPath bindingGroup
                  if let some unbound := model.unboundReadLevel? declaringGroup writtenGroup declaration.repeatableScope bound then
                    throw (ResolveError.unboundOperandLevel declaration.path unbound)
                  declaration.requireRepetitionBoundBy bound)
        |>.mapError (fun error => .shape (.resolve error))
      pure (.field declaration projectionRef)
  | .star source projectionRef => do
      pure (.star (← star source) projectionRef none)
  | .starHaving source projectionRef having => do
      let checked ← star source
      if fixedTargetGroup?.isNone then
        if let some (path, unbound) := having.unboundOuterReference? model declaringGroup writtenGroup then
          throw (.shape (.resolve (.unboundOperandLevel path unbound)))
      pure (.star checked projectionRef (some having))
where
  star (source : SurfaceStarFieldPath) :=
    (elaborateStarFieldPath model declaringGroup source).mapError fun error =>
      .shape (.starPath
        (error.placeBelowStar model declaringGroup (fixedTargetGroup?.getD writtenGroup)))

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
    (declaringGroup bindingGroup : GroupPath) :
    ResolvedProjectedTokenEntityOperand model →
      Except TokenEntityElabError (CheckedTokenEntityOperand model)
  | .field declaration projectionRef => do
      pure (.field
        (← certifyDirectTokenOperand model declaration projectionRef))
  | .star source projectionRef having => do
      pure (.star
        (← certifyStarTokenOperand declaringGroup source having projectionRef (bindingGroup := bindingGroup)))

/-- Resolve paths before exact-reference duplication and cardinality, then certify kind, category, and `Having` in authored order. This is the sole projection-bearing token entity-list authoring boundary. -/
def elaborateProjectedTokenEntitySource (model : FlatModel)
    (declaringGroup : GroupPath)
    (authored : SurfaceProjectedTokenEntitySource)
    (arity : EntityListArity := .manyRequired) (fixedTargetGroup? : Option GroupPath := none)
    (writtenGroup : GroupPath := declaringGroup) (bindingGroup? : Option GroupPath := none) :
    Except TokenEntityElabError (CheckedTokenEntitySource model) :=
  match hModel : model.validate with
  | .error error => .error (.shape (.resolve error))
  | .ok () => do
      let first ←
        resolveProjectedTokenEntityOperand model declaringGroup fixedTargetGroup? writtenGroup bindingGroup?
          authored.first
      let rest ← authored.rest.mapM fun operand =>
        resolveProjectedTokenEntityOperand model declaringGroup fixedTargetGroup? writtenGroup bindingGroup?
          operand
      -- The shared shape's list-wide gate, asked of this boundary's own resolved slots.
      if let some targetGroup := fixedTargetGroup? then
        if let some unbound := model.firstUnboundComputationLevel? declaringGroup targetGroup
            ((first :: rest).map ResolvedProjectedTokenEntityOperand.bindingScope) then
          throw (.shape (.unboundOperandLevel unbound))
      match firstDuplicateResolvedProjectedTokenField? (first :: rest) with
      | some field => throw (.shape (.duplicateOperand field))
      | none =>
          if arity.allowsSole || first.isStar || !rest.isEmpty then
            let checkedFirst ←
              certifyProjectedTokenEntityOperand model declaringGroup (bindingGroup?.getD declaringGroup) first
            let checkedRest ← rest.mapM fun operand =>
              certifyProjectedTokenEntityOperand model declaringGroup (bindingGroup?.getD declaringGroup) operand
            assembleTokenEntitySource (by rw [hModel]; rfl)
              checkedFirst checkedRest arity
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

/-- A group slot reaches only instantiated rows through the model's own repeatability, so it has no star topology and no filter; its omitted tail is the declared capacity those rows leave open. -/
private def ofGroupCells (source : CheckedTokenEntityOperand model)
    (cells : List (FlatTextFieldOperand × CheckedAddressedCell))
    (hasUninstantiatedTail : Bool) (hasNonRelevant : Bool := false) :
    ResolvedCheckedTokenEntityOperand model :=
  { source
    projectedCells := cells
    topology := none
    hasUninstantiatedTail
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

/-- Project away cells beneath a declared-capacity violation while preserving each reached declaration's exact token projection. A star or group slot already resolves in capacity, so this and `valueListSideAt` differ only on a direct slot read at an over-limit row ([checkpoint](../../docs/sources/group-list-and-capacity-probes.md#src-group-capacity-consumers)). -/
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

/-- The group's cells on the reader route, read through a caller-supplied checked-cell view over the
shared group walk `FlatModel.groupOperandReads`, as a Number group's are, each cell classified through
its own declaration's stored projection. -/
def CheckedTokenEntityGroup.resolvedSideIn (group : CheckedTokenEntityGroup model) (phase : Phase)
    (document : Document) (outer : Env) (read : Env → FieldId → CheckedCell) :
    Except StarAddressingError (ResolvedValueListSide .token) := do
  let (reads, hasUninstantiatedTail) ← model.groupOperandReads document outer
    group.source.boundLevelCount group.slots (·.declaration.repeatableScope)
  pure { cells := reads.map fun (slot, environment) =>
           slot.operand.checkedValueListCellAt phase (read environment slot.declaration.id)
         hasUninstantiatedTail
         hasHaving := false }

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
    (read : Env → FieldId → CheckedCell)
    (world : Option World := none) :
    Except StarAddressingError (ResolvedValueListSide .token) :=
  checked.source.resolvedOptionalValidationHavingValueListSide (world := world) document outer
    checked.filter read (checked.valueListCellAt .validation read)

/-- Partial all-rows validation checks wildcard/ancestor extent before reading any selected target. Filtered rules are skipped by the owning whole-source consumer. -/
def resolvedPartialValidationSide
    (checked : CheckedTokenStarSource model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → CheckedCell)
    (_unfiltered : checked.filter.isNone = true) :
    Except StarAddressingError
      (Sum (ResolvedValueListSide .token) Unit) := do
  let resolved ← checked.source.path.resolveInCapacity document outer
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
  let resolved ← checked.source.path.resolveInCapacity document outer
  if checked.source.valueListExtentRelevant scope outer then
    pure (.inl (resolved.toResolvedSide
      (checked.valueListCellAt .validation read)))
  else
    pure (.inr ())

end CheckedTokenStarSource

namespace CheckedTokenEntityOperand

/-- Resolve an ordinary full-validation token operand through the checked topology, filter, and addressed-cell owners while retaining its exact String/Enumeration projection certificate. Indexed streams use `checkedValidationSide` until their richer address projection closes. A group slot reads its whole `(row × field)` extent from the model's repeatability through the same shared walk. -/
def resolveCheckedValidationOperand
    (source : CheckedTokenEntityOperand model)
    (document : CheckedDocument model) (outer : Env)
    (world : Option World := none) :
    Except CheckedAddressingError
      (ResolvedCheckedTokenEntityOperand model) :=
  match source with
  | .selected selection => throw (.addressing (.unsupportedGroupOperand selection.path))
  | .field direct => do
      let core ←
        document.resolveCheckedDirectEntityOperandCoreAt outer direct.operand.field.id
      pure (.ofCore source direct.operand core)
  | .star starSource => do
      let having := starSource.filter.map fun filter => filter.condition
      let core ←
        starSource.source.resolveCheckedValidationEntityOperandCore (world := world)
          document outer having
      pure (.ofCore source starSource.operand core)
  | .group slot => do
      pure (.ofGroupCells source
        (← slot.resolveCheckedValidationCells document outer)
        (← slot.resolveCheckedUninstantiatedTail document outer))

/-- Evaluate selected streams without inventing addresses for an absent or unavailable selection.
The richer addressed-cell resolver remains unavailable until selected pointer projection closes. -/
def checkedValidationSide (source : CheckedTokenEntityOperand model)
    (document : CheckedDocument model) (outer : Env)
    (world : Option World := none) (inCapacity : Bool := false) :
    Except CheckedAddressingError (ResolvedValueListSide .token) := do
  match source with
  | .selected source => source.sideIn .validation document outer
  | _ =>
      let resolved ← source.resolveCheckedValidationOperand (world := world) document outer
      pure (if inCapacity then resolved.inCapacityValueListSideAt .validation else resolved.valueListSideAt .validation)

/-- Resolve one partial-validation token operand without collapsing nonrelevance into a semantic cell. Filtered rules remain suppressed by the owning whole-source gate.

    A group slot retains relevant concrete cells per expanded declaration and records complete extent only when every expanded declaration has one covering wildcard identifier. -/
def resolveCheckedPartialValidationOperand
    (source : CheckedTokenEntityOperand model)
    (document : CheckedDocument model) (outer : Env)
    (scope : ValidationRelevanceScope) :
    Except CheckedAddressingError
      (ResolvedCheckedTokenEntityOperand model) :=
  match source with
  | .selected selection => throw (.addressing (.unsupportedGroupOperand selection.path))
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
      pure (.ofGroupCells source cells
        (← slot.resolveCheckedUninstantiatedTail document outer) hasNonRelevant)

/-- Resolve one direct or starred token slot for full validation through the shared declaration-owned classifier.

    The three raw-`Document` routes below all refuse a group slot. Its extent is enumerated from the **model's** repeatability against instantiated rows, which only the immutable checked document can answer; the caller-supplied read functions here cannot say which rows exist. `resolveCheckedValidationOperand` above is the route that serves a group. -/
def resolvedValidationSide (checked : CheckedTokenEntityOperand model)
    (document : Document) (outer : Env)
    (directRead : FieldId → CheckedCell)
    (starRead : Env → FieldId → CheckedCell)
    (world : Option World := none) :
    Except StarAddressingError (ResolvedValueListSide .token) :=
  match checked with
  | .selected source => .error (.unsupportedGroupOperand source.path)
  | .field source => pure (source.resolvedSideAt .validation directRead)
  | .star source => source.resolvedValidationSide (world := world) document outer starRead
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
  | .selected source => .error (.unsupportedGroupOperand source.path)
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
  | .selected source => .error (.unsupportedGroupOperand source.path)
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

namespace CheckedTokenEntityOperand

/-- Resolve one token slot at computation phase, a star over its in-capacity extent ([checkpoint](../../docs/sources/computation-scheduling-probes.md#src-row-star-scans)). Filtered stars reuse the shared one-kept-successor traversal and retain per-slot filter provenance for the consuming fold.

    A group slot reads its declarations' rows through the shared group walk, as a Number group's do ([checkpoint](../../docs/sources/computation-scheduling-probes.md#src-row-groups)). -/
def resolvedComputationSide
    (checked : CheckedTokenEntityOperand model)
    (document : Document) (outer : Env)
    (directRead : FieldId → CheckedCell)
    (filterRead starRead : Env → FieldId → CheckedCell)
    (world : Option World := none)
    (selectedRead : CheckedSelectedTokenEntity model → Except StarAddressingError (ResolvedValueListSide .token) :=
      fun source => .error (.unsupportedGroupOperand source.path))
    (filterStoredText : Env → FieldId → Option String := fun _ _ => none) :
    Except StarAddressingError
      (Sum (ResolvedValueListSide .token) NumericOperand) :=
  match checked with
  | .selected source => .inl <$> selectedRead source
  | .group source => .inl <$> source.resolvedSideIn .computation document outer starRead
  | .field source =>
      pure (.inl (source.resolvedSideAt .computation directRead))
  | .star source => do
      let resolved ← source.source.path.resolveInCapacity document outer
      match source.filter with
      | none =>
          pure (.inl (resolved.toResolvedSide
            (source.valueListCellAt .computation starRead)))
      | some having =>
          let filterContext := ({ read := filterRead, storedText := filterStoredText, world } : CorrelationContext).withModelComputationGroups model document
          let consume := fun cells environment =>
            match source.valueListCellAt .computation starRead environment with
            | .unknown cause => .inr cause
            | cell => .inl (cell :: cells)
          match ← (having.condition.scanComputation filterContext outer consume
              resolved.environments []).mapError (fun
                | .calendarUnavailable => .unsupportedDateCalendar
                | .valueFailure => .temporalValueFailure
                | .worldUnavailable => .worldUnavailable
                | .typeValidityValueFailure => .typeValidityValueFailure
                | .storedTextUnavailable fieldId => .storedTextUnavailable fieldId
                | .groupUnavailable path => .unsupportedGroupOperand path) with
          | .exhausted reversed =>
              pure (.inl {
                cells := reversed.reverse
                hasUninstantiatedTail := resolved.domain.hasOpenTail
                hasHaving := true })
          | .terminated cause | .poison cause =>
              pure (.inr (.unknown cause))

end CheckedTokenEntityOperand

end A12Kernel
