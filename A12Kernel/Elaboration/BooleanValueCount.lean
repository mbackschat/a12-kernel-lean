import A12Kernel.Elaboration.NumericScale
import A12Kernel.Elaboration.TokenEntityList
import A12Kernel.Semantics.NumericAggregate
/-! # Checked Boolean/Confirm value counts

This consumer applies the common checked field-entity list to Boolean/Confirm `NumberOfValueInFields`. It reuses the generic value-count fold only after its distinct static family gate: `True` admits Boolean and Confirm, while `False` admits Boolean only. Direct, plain-star, and filtered-star operands project already-checked scalar values to fixed canonical tokens and never re-read stored text or model-declared display tokens.
-/

namespace A12Kernel

/-- A Boolean/Confirm value count uses the common direct/star/group field-list shape before applying its distinct kind gate. -/
abbrev SurfaceBooleanValueCountSource := SurfaceFieldEntitySource

/-- Static failures specific to the Boolean/Confirm value-count family. -/
inductive BooleanValueCountElabError where
  | shape (error : FieldEntityShapeElabError)
  | fieldKindMismatch (path : List String) (expected : Bool)
      (actual : SurfaceScalarKind)
  | having (error : CorrelationElabError)
  /-- A group slot whose recursive subtree declares no field. Unmeasured, so refused without a diagnostic class. -/
  | groupExpansionEmpty (path : List String)
  | incoherentCore
  deriving Repr, DecidableEq

/-- Whether one field kind is legal for the authored Boolean constant. `True` admits Boolean and Confirm; `False` admits only Boolean. -/
def booleanValueCountKindAllowed (expected : Bool) : FieldKind → Bool
  | .boolean => true
  | .confirm => expected
  | _ => false

/-- Select one declaration admitted by the Boolean/Confirm constant-specific gate. Returning the
    declaration itself lets a group certify that its retained expansion omitted nothing. -/
def FlatFieldDecl.toBooleanValueCountField? (expected : Bool)
    (declaration : FlatFieldDecl) : Option FlatFieldDecl :=
  if booleanValueCountKindAllowed expected declaration.policy.kind then
    some declaration
  else
    none

/-- One checked direct Boolean/Confirm operand. -/
structure CheckedBooleanValueCountField (model : FlatModel)
    (expected : Bool) where
  declaration : FlatFieldDecl
  admitted :
    model.admitsField declaration.toPresenceField = true
  kindAllowed :
    booleanValueCountKindAllowed expected declaration.policy.kind = true

/-- One checked starred Boolean/Confirm operand with its exact optional filter. -/
structure CheckedBooleanValueCountStarSource (model : FlatModel)
    (expected : Bool) where
  source : CheckedStarFieldPath model
  declaringGroup : GroupPath
  filter : Option (CheckedStarHaving model source declaringGroup)
  kindAllowed :
    booleanValueCountKindAllowed expected source.declaration.policy.kind = true

/-- One authored group slot certified as a nonempty recursive expansion whose every declaration is
    admitted by the Boolean constant's kind gate. The authored reference remains the operand;
    `first` and `rest` are the declaration-level certificate used by runtime and consumers. -/
structure CheckedBooleanValueCountGroup (model : FlatModel)
    (expected : Bool) where
  source : CheckedEntityGroupSource model
  first : FlatFieldDecl
  rest : List FlatFieldDecl
  expansionOwned :
    (model.groupSubtreeFields source.groupPath).filterMap
      (FlatFieldDecl.toBooleanValueCountField? expected) = first :: rest
  expansionAllAllowed :
    (model.groupSubtreeFields source.groupPath).all
      (fun declaration =>
        (declaration.toBooleanValueCountField? expected).isSome) = true

namespace CheckedBooleanValueCountGroup

def groupPath (group : CheckedBooleanValueCountGroup model expected) : GroupPath :=
  group.source.groupPath

def isStarred (group : CheckedBooleanValueCountGroup model expected) : Bool :=
  group.source.isStarred

def fields (group : CheckedBooleanValueCountGroup model expected) :
    List FlatFieldDecl :=
  group.first :: group.rest

def referencesField (group : CheckedBooleanValueCountGroup model expected)
    (field : FieldId) : Bool :=
  group.fields.any (·.id == field)

private def scopeHasUninstantiatedTail
    (group : CheckedBooleanValueCountGroup model expected)
    (document : CheckedDocument model) (outer : Env)
    (scope : List RepeatableLevel) :
    Except CheckedAddressingError Bool := do
  if scope.length ≤ group.source.boundLevelCount then
    pure false
  else
    let axes ← match model.repeatableAxesForScope? scope with
      | some axes => pure axes
      | none => throw (.document
          (.incoherentRepeatableScope scope))
    let topology ← (({
      axes
      firstStar := group.source.boundLevelCount } : StarPath).resolve
        document.source.toDocument outer).mapError .addressing
    pure topology.domain.hasOpenTail

/-- Whether any repeatable declaration reopened by this group retains declared-but-uninstantiated
    capacity. The shared group walk still owns concrete `(row × field)` extent; this separate query
    preserves only the hierarchical tail bit consumed by Boolean value-count fillability. -/
def resolveCheckedUninstantiatedTail
    (group : CheckedBooleanValueCountGroup model expected)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError Bool := do
  let scopes := (group.fields.map (·.repeatableScope)).eraseDups
  let tails ← scopes.mapM (group.scopeHasUninstantiatedTail document outer)
  pure (tails.any id)

end CheckedBooleanValueCountGroup

/-- One checked Boolean/Confirm entity-list operand. -/
inductive CheckedBooleanValueCountOperand (model : FlatModel)
    (expected : Bool) where
  | field (source : CheckedBooleanValueCountField model expected)
  | star (source : CheckedBooleanValueCountStarSource model expected)
  | group (source : CheckedBooleanValueCountGroup model expected)

namespace CheckedBooleanValueCountOperand

def declarations :
    CheckedBooleanValueCountOperand model expected → List FlatFieldDecl
  | .field source => [source.declaration]
  | .star source => [source.source.declaration]
  | .group source => source.fields

def directField? :
    CheckedBooleanValueCountOperand model expected → Option FlatFieldDecl
  | .field source => some source.declaration
  | .star _ | .group _ => none

def directFieldId? :
    CheckedBooleanValueCountOperand model expected → Option FieldId
  | .field source => some source.declaration.id
  | .star _ | .group _ => none

def isAlreadyMany : CheckedBooleanValueCountOperand model expected → Bool
  | .field _ => false
  | .star _ | .group _ => true

def groupSlot? : CheckedBooleanValueCountOperand model expected →
    Option (CheckedBooleanValueCountGroup model expected)
  | .group source => some source
  | .field _ | .star _ => none

def hasHaving : CheckedBooleanValueCountOperand model expected → Bool
  | .field _ => false
  | .star source => source.filter.isSome
  | .group _ => false

def referencesField (checked :
    CheckedBooleanValueCountOperand model expected) (field : FieldId) : Bool :=
  match checked with
  | .field source => source.declaration.id == field
  | .star source =>
      source.source.declaration.id == field ||
        match source.filter with
        | none => false
        | some having => having.condition.referencesField field
  | .group source => source.referencesField field

end CheckedBooleanValueCountOperand

def firstDuplicateDirectBooleanValueCountField? :
    List (CheckedBooleanValueCountOperand model expected) → Option FieldId
  | operands => firstDuplicateDirectField?
      (fun operand => operand.directFieldId?) operands

private def certifyBooleanValueCountGroup (model : FlatModel)
    (expected : Bool) (source : CheckedEntityGroupSource model) :
    Except BooleanValueCountElabError
      (CheckedBooleanValueCountOperand model expected) :=
  let declarations := model.groupSubtreeFields source.groupPath
  match declarations.find? fun declaration =>
      !booleanValueCountKindAllowed expected declaration.policy.kind with
  | some declaration =>
      throw (.fieldKindMismatch declaration.path expected
        declaration.policy.kind.surfaceKind)
  | none =>
      if hAll : declarations.all
          (fun declaration =>
            (declaration.toBooleanValueCountField? expected).isSome) = true then
        match hExpansion : declarations.filterMap
            (FlatFieldDecl.toBooleanValueCountField? expected) with
        | [] => throw (.groupExpansionEmpty source.groupPath)
        | first :: rest =>
            pure (.group {
              source
              first
              rest
              expansionOwned := hExpansion
              expansionAllAllowed := hAll })
      else
        throw .incoherentCore

private def certifyBooleanValueCountOperand (model : FlatModel)
    (declaringGroup : GroupPath) (expected : Bool) :
    ResolvedFieldEntityOperand model →
      Except BooleanValueCountElabError
        (CheckedBooleanValueCountOperand model expected)
  | .field declaration _ =>
      if hKind :
          booleanValueCountKindAllowed expected declaration.policy.kind = true then
        if hAdmitted :
            model.admitsField declaration.toPresenceField = true then
          pure (.field { declaration, admitted := hAdmitted, kindAllowed := hKind })
        else
          throw .incoherentCore
      else
        throw (.fieldKindMismatch declaration.path expected
          declaration.policy.kind.surfaceKind)
  | .star source =>
      if hKind :
          booleanValueCountKindAllowed expected source.declaration.policy.kind =
            true then do
        pure (.star {
          source
          declaringGroup
          filter := none
          kindAllowed := hKind })
      else
        throw (.fieldKindMismatch source.declaration.path expected
          source.declaration.policy.kind.surfaceKind)
  | .starHaving source having =>
      if hKind :
          booleanValueCountKindAllowed expected source.declaration.policy.kind =
            true then do
        let filter ←
          elaborateStarHavingCore model declaringGroup source having
            |>.mapError .having
        pure (.star {
          source
          declaringGroup
          filter := some filter
          kindAllowed := hKind })
      else
        throw (.fieldKindMismatch source.declaration.path expected
          source.declaration.policy.kind.surfaceKind)
  | .group reference =>
      certifyBooleanValueCountGroup model expected (.fixed reference)
  | .starredGroup source =>
      certifyBooleanValueCountGroup model expected (.starred source)
  | .starredGroupPresence source =>
      certifyBooleanValueCountGroup model expected (.starredPresence source)

private def certifyBooleanValueCountOperands (model : FlatModel)
    (declaringGroup : GroupPath) (expected : Bool) :
    List (ResolvedFieldEntityOperand model) →
      Except BooleanValueCountElabError
        (List (CheckedBooleanValueCountOperand model expected))
  | [] => pure []
  | operand :: remaining => do
      pure ((← certifyBooleanValueCountOperand model declaringGroup expected operand) ::
        (← certifyBooleanValueCountOperands model declaringGroup expected remaining))

/-- A model-owned Boolean/Confirm `NumberOfValueInFields` source retaining direct/star/group order and optional per-star filters. -/
structure CheckedBooleanValueCountSource (model : FlatModel) where
  expected : Bool
  first : CheckedBooleanValueCountOperand model expected
  rest : List (CheckedBooleanValueCountOperand model expected)
  modelWellFormed : model.validate.isOk = true
  requiredMultiplicity : (first.isAlreadyMany || !rest.isEmpty) = true
  uniqueDirectOperands :
    firstDuplicateDirectBooleanValueCountField? (first :: rest) = none

/-- The measured one-axis Boolean-group computation shape. The group certificate already owns the constant-specific field-kind gate. -/
def measuredBooleanValueCountStarredGroupShape
    (starred : CheckedStarredGroupSource model)
    (group : CheckedBooleanValueCountGroup model expected) : Bool :=
  starred.path.axes.length == 1 &&
    (group.fields.all fun declaration =>
      declaration.repeatableScope == starred.path.axes.map (·.level))

/-- A measured Boolean-group computation form with one repeatable axis, no deeper repeated declaration, and the group certificate's constant-specific field kinds. The source equality excludes fixed groups and the separately admitted terminal-presence shape from this computation carrier. -/
structure CheckedBooleanValueCountStarredGroupSource
    (model : FlatModel) (expected : Bool) where
  starredSource : CheckedStarredGroupSource model
  group : CheckedBooleanValueCountGroup model expected
  sourceOwned : group.source = .starred starredSource
  measuredShape :
    measuredBooleanValueCountStarredGroupShape starredSource group = true
  modelWellFormed : model.validate.isOk = true

/-- The measured fixed computation boundary: exactly two direct nonrepeatable declarations in the
    authored terminal group, with Boolean then Confirm for `True` or two Booleans for `False`. -/
def measuredBooleanValueCountFixedGroupShape
    (reference : ResolvedGroupReference)
    (group : CheckedBooleanValueCountGroup model expected) : Bool :=
  group.fields.length == 2 &&
    (group.fields.all fun declaration =>
      declaration.groupPath == reference.path &&
        declaration.repeatableScope.isEmpty) &&
    group.fields.map (·.policy.kind) ==
      if expected then [.boolean, .confirm] else [.boolean, .boolean]

/-- One measured fixed Boolean-group computation. The source equality excludes starred carriers,
    while `measuredShape` keeps recursive and repeatable expansions outside this first runtime slice. -/
structure CheckedBooleanValueCountFixedGroupSource
    (model : FlatModel) (expected : Bool) where
  reference : ResolvedGroupReference
  group : CheckedBooleanValueCountGroup model expected
  sourceOwned : group.source = .fixed reference
  measuredShape :
    measuredBooleanValueCountFixedGroupShape reference group = true
  modelWellFormed : model.validate.isOk = true

abbrev CheckedTrueValueCountStarredGroupSource (model : FlatModel) :=
  CheckedBooleanValueCountStarredGroupSource model true

abbrev CheckedFalseValueCountStarredGroupSource (model : FlatModel) :=
  CheckedBooleanValueCountStarredGroupSource model false

abbrev CheckedTrueValueCountFixedGroupSource (model : FlatModel) :=
  CheckedBooleanValueCountFixedGroupSource model true

abbrev CheckedFalseValueCountFixedGroupSource (model : FlatModel) :=
  CheckedBooleanValueCountFixedGroupSource model false

namespace CheckedBooleanValueCountSource

def operands (checked : CheckedBooleanValueCountSource model) :
    List (CheckedBooleanValueCountOperand model checked.expected) :=
  checked.first :: checked.rest

def directFields? (checked : CheckedBooleanValueCountSource model) :
    Option (List FlatFieldDecl) :=
  checked.operands.mapM CheckedBooleanValueCountOperand.directField?

def hasHaving (checked : CheckedBooleanValueCountSource model) : Bool :=
  checked.operands.any CheckedBooleanValueCountOperand.hasHaving

end CheckedBooleanValueCountSource

/-- Resolve the common direct/star/group entity-list shape and certify its constant-specific Boolean/Confirm family. -/
def elaborateBooleanValueCountSource (model : FlatModel)
    (declaringGroup : GroupPath) (expected : Bool)
    (authored : SurfaceBooleanValueCountSource) :
    Except BooleanValueCountElabError
      (CheckedBooleanValueCountSource model) := do
  let shape ← elaborateFieldEntityShape model declaringGroup authored
    |>.mapError .shape
  let first ←
    certifyBooleanValueCountOperand model declaringGroup expected shape.first
  let rest ←
    certifyBooleanValueCountOperands model declaringGroup expected shape.rest
  if hMultiplicity : (first.isAlreadyMany || !rest.isEmpty) = true then
    match hDuplicate :
        firstDuplicateDirectBooleanValueCountField? (first :: rest) with
    | some _ => throw .incoherentCore
    | none => pure {
        expected
        first
        rest
        modelWellFormed := shape.modelWellFormed
        requiredMultiplicity := hMultiplicity
        uniqueDirectOperands := hDuplicate }
  else
    throw .incoherentCore

/-- Resolve the measured two-field fixed Boolean/Confirm group computation without widening to a
    recursive, repeatable, starred, or mixed entity-list route. -/
def elaborateBooleanValueCountFixedGroupSource (model : FlatModel)
    (declaringGroup : GroupPath) (expected : Bool)
    (authored : SurfaceGroupReference) :
    Except BooleanValueCountElabError
      (CheckedBooleanValueCountFixedGroupSource model expected) := do
  let shape ← elaborateFieldEntityShape model declaringGroup {
    first := .group authored
    rest := [] } |>.mapError .shape
  match shape.first, shape.rest with
  | .group reference, [] =>
      let operand ←
        certifyBooleanValueCountGroup model expected (.fixed reference)
      match operand with
      | .group group =>
          match hSource : group.source with
          | .fixed fixed =>
              if hMeasured :
                  measuredBooleanValueCountFixedGroupShape fixed group = true then
                pure {
                  reference := fixed
                  group
                  sourceOwned := hSource
                  measuredShape := hMeasured
                  modelWellFormed := shape.modelWellFormed }
              else throw .incoherentCore
          | .starred _ | .starredPresence _ => throw .incoherentCore
      | .field _ | .star _ => throw .incoherentCore
  | _, _ => throw .incoherentCore

/-- Resolve the measured two-field fixed `True` Boolean/Confirm group computation. -/
def elaborateTrueValueCountFixedGroupSource (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceGroupReference) :
    Except BooleanValueCountElabError
      (CheckedTrueValueCountFixedGroupSource model) :=
  elaborateBooleanValueCountFixedGroupSource
    model declaringGroup true authored

/-- Resolve the measured two-field fixed `False` Boolean group computation. -/
def elaborateFalseValueCountFixedGroupSource (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceGroupReference) :
    Except BooleanValueCountElabError
      (CheckedFalseValueCountFixedGroupSource model) :=
  elaborateBooleanValueCountFixedGroupSource
    model declaringGroup false authored

/-- Resolve one measured Boolean-group value-count computation shape without widening fixed groups, terminal-presence stars, mixed lists, or unmeasured declarations. -/
def elaborateBooleanValueCountStarredGroupSource (model : FlatModel)
    (declaringGroup : GroupPath) (expected : Bool)
    (authored : SurfaceStarGroupPath) :
    Except BooleanValueCountElabError
      (CheckedBooleanValueCountStarredGroupSource model expected) := do
  let starred ← elaborateStarredGroupSource model declaringGroup authored
    |>.mapError fun error => .shape (.starredGroup error)
  let operand ←
    certifyBooleanValueCountGroup model expected (.starred starred)
  match operand with
  | .group group =>
      match hSource : group.source with
      | .starred source =>
          if hMeasured :
              measuredBooleanValueCountStarredGroupShape source group = true then
            pure {
              starredSource := source
              group
              sourceOwned := hSource
              measuredShape := hMeasured
              modelWellFormed := source.modelWellFormed }
          else throw .incoherentCore
      | .fixed _ | .starredPresence _ => throw .incoherentCore
  | .field _ | .star _ => throw .incoherentCore

/-- Resolve a measured one-axis Boolean/Confirm `True` group computation. -/
def elaborateTrueValueCountStarredGroupSource (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceStarGroupPath) :
    Except BooleanValueCountElabError
      (CheckedTrueValueCountStarredGroupSource model) :=
  elaborateBooleanValueCountStarredGroupSource
    model declaringGroup true authored

/-- Resolve a measured one-axis Boolean-only `False` group computation. -/
def elaborateFalseValueCountStarredGroupSource (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceStarGroupPath) :
    Except BooleanValueCountElabError
      (CheckedFalseValueCountStarredGroupSource model) :=
  elaborateBooleanValueCountStarredGroupSource
    model declaringGroup false authored

/-- The fixed storage token selected by an authored Boolean constant. -/
def booleanValueCountToken (expected : Bool) : String :=
  if expected then "true" else "false"

/-- Project one already-checked Boolean/Confirm cell to the exact runtime token domain without consulting stored text. Empty remains unfilled; an impossible false Confirm fails closed. -/
def booleanValueCountCellAt (phase : Phase)
    (cell : CheckedCell) : ValueListCell .token :=
  match observeCell phase cell with
  | .empty => .empty
  | .value (.bool value) => .present (booleanValueCountToken value)
  | .value (.conf true) => .present (booleanValueCountToken true)
  | .value _ => .unknown .malformed
  | .unknown cause | .poison cause => .unknown cause

/-- The two externally distinguished checked group-computation extents. Fixed groups consume their
    complete direct extent; starred groups explicitly exclude cells beyond declared capacity. -/
inductive BooleanValueCountGroupComputationExtent where
  | complete
  | inCapacity

/-- Evaluate one certified Boolean group against the selected checked-document extent. This is the
    common scan; fixed and starred carriers differ only in the extent they select. -/
def evaluateCheckedBooleanValueCountGroupComputation
    (expected : Bool) (group : CheckedBooleanValueCountGroup model expected)
    (extent : BooleanValueCountGroupComputationExtent)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError NumericOperand := do
  let core ← document.resolveCheckedGroupEntityOperandCore outer
    group.source.boundLevelCount group.fields
  let addressed := match extent with
    | .complete => core.addressedCells
    | .inCapacity => core.inCapacityAddressedCells
  let resolved : ResolvedValueListSide .token := {
    cells := addressed.map fun cell =>
      booleanValueCountCellAt .computation cell.cell
    hasUninstantiatedTail := core.hasUninstantiatedTail
    hasHaving := core.hasHaving
    hasNonRelevant := core.hasNonRelevant }
  let side := (ResolvedValueCountSide.empty : ResolvedValueCountSide .token)
    |>.appendResolved resolved
  pure (evalValueCountAggregate (booleanValueCountToken expected) side)

namespace CheckedBooleanValueCountSource

/-- Every Boolean/Confirm value count has the Kernel's fixed integral result scale. -/
def scaleSummary (_checked : CheckedBooleanValueCountSource model) :
    NumericScaleSummary :=
  NumericScaleSummary.field 0

def referencesField (checked : CheckedBooleanValueCountSource model)
    (field : FieldId) : Bool :=
  checked.operands.any fun operand => operand.referencesField field

/-- Evaluate a direct-only checked Boolean/Confirm count without inventing repeatable topology. -/
def evaluateDirectAt? (checked : CheckedBooleanValueCountSource model)
    (phase : Phase) (read : FieldId → CheckedCell) :
    Option NumericOperand := do
  let fields ← checked.directFields?
  pure (evalValueCountAggregate
    (booleanValueCountToken checked.expected) {
      cells := fields.map fun field => {
        cell := booleanValueCountCellAt phase (read field.id)
        selectedByHaving := false }
      hasUninstantiatedTail := false
      hasHaving := false })

end CheckedBooleanValueCountSource

namespace CheckedBooleanValueCountStarredGroupSource

def scaleSummary
    (_checked : CheckedBooleanValueCountStarredGroupSource model expected) :
    NumericScaleSummary :=
  NumericScaleSummary.field 0

def referencesField
    (checked : CheckedBooleanValueCountStarredGroupSource model expected)
    (field : FieldId) : Bool :=
  checked.group.referencesField field

/-- Recover the established full-validation carrier for the same sole starred group. -/
def toCheckedBooleanValueCountSource
    (checked : CheckedBooleanValueCountStarredGroupSource model expected) :
    CheckedBooleanValueCountSource model :=
  { expected
    first := .group checked.group
    rest := []
    modelWellFormed := checked.modelWellFormed
    requiredMultiplicity := by rfl
    uniqueDirectOperands := by rfl }

/-- Checked computation selects the in-capacity addressed cells before projecting their canonical Boolean/Confirm tokens. -/
def evaluateCheckedDocumentComputation
    (checked : CheckedBooleanValueCountStarredGroupSource model expected)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError NumericOperand :=
  evaluateCheckedBooleanValueCountGroupComputation expected checked.group
    .inCapacity document outer

end CheckedBooleanValueCountStarredGroupSource

namespace CheckedBooleanValueCountFixedGroupSource

def scaleSummary
    (_checked : CheckedBooleanValueCountFixedGroupSource model expected) :
    NumericScaleSummary :=
  NumericScaleSummary.field 0

def referencesField
    (checked : CheckedBooleanValueCountFixedGroupSource model expected)
    (field : FieldId) : Bool :=
  checked.group.referencesField field

/-- Checked fixed-group computation classifies every cell in its complete direct extent. -/
def evaluateCheckedDocumentComputation
    (checked : CheckedBooleanValueCountFixedGroupSource model expected)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError NumericOperand :=
  evaluateCheckedBooleanValueCountGroupComputation expected checked.group
    .complete document outer

end CheckedBooleanValueCountFixedGroupSource

namespace CheckedBooleanValueCountOperand

private def directSideAt (source : CheckedBooleanValueCountField model expected)
    (phase : Phase) (read : FieldId → CheckedCell) :
    ResolvedValueListSide .token :=
  { cells := [
      booleanValueCountCellAt phase (read source.declaration.id)]
    hasUninstantiatedTail := false
    hasHaving := false }

private def starCellAt
    (source : CheckedBooleanValueCountStarSource model expected)
    (phase : Phase) (read : Env → FieldId → CheckedCell)
    (environment : Env) : ValueListCell .token :=
  booleanValueCountCellAt phase
    (source.source.contextualizeCell environment
      (read environment source.source.declaration.id))

/-- Resolve one Boolean/Confirm slot for full validation through the existing topology and optional checked filter. -/
def resolvedValidationSide
    (checked : CheckedBooleanValueCountOperand model expected)
    (document : Document) (outer : Env)
    (directRead : FieldId → CheckedCell)
    (starRead : Env → FieldId → CheckedCell) :
    Except StarAddressingError (ResolvedValueListSide .token) :=
  match checked with
  | .field source => pure (directSideAt source .validation directRead)
  | .star source =>
      source.source.resolvedOptionalValidationHavingValueListSide
        document outer source.filter starRead
        (starCellAt source .validation starRead)
  | .group source =>
      .error (.unsupportedGroupOperand source.groupPath)

/-- Resolve one Boolean/Confirm slot at computation phase. Filtered stars preserve one-kept-successor selection and stop on the first reached filter or value poison. -/
def resolvedComputationSide
    (checked : CheckedBooleanValueCountOperand model expected)
    (document : Document) (outer : Env)
    (directRead : FieldId → CheckedCell)
    (filterRead starRead : Env → FieldId → CheckedCell) :
    Except StarAddressingError
      (Sum (ResolvedValueListSide .token) NumericOperand) :=
  match checked with
  | .field source =>
      pure (.inl (directSideAt source .computation directRead))
  | .star source => do
      let resolved ← source.source.path.resolve document outer
      match source.filter with
      | none =>
          pure (.inl (resolved.toResolvedSide
            (starCellAt source .computation starRead)))
      | some having =>
          let filterContext : CorrelationContext := { read := filterRead }
          let consume := fun cells environment =>
            match starCellAt source .computation starRead environment with
            | .unknown cause => .inr cause
            | cell => .inl (cell :: cells)
          match having.condition.scanComputation filterContext outer consume
              resolved.environments [] with
          | .exhausted reversed =>
              pure (.inl {
                cells := reversed.reverse
                hasUninstantiatedTail := resolved.domain.hasOpenTail
                hasHaving := true })
          | .terminated cause | .poison cause =>
              pure (.inr (.unknown cause))
  | .group source =>
      .error (.unsupportedGroupOperand source.groupPath)

/-- Resolve one Boolean/Confirm slot from the immutable checked document and project its addressed cells only after topology and filter selection succeed.

    A group slot projects its declared-capacity extent, starred or not: kernel 30.8.1 answers `0` for
    `NumberOfValueInFields(True In G)` when the only `true` cell sits beyond its group's declared
    repeatability, and `1` on the control one index lower
    ([checkpoint](../../docs/sources/inbound-group-operand-batches.md#src-group-operand-capacity-consumer-sweep)),
    and the starred form answers the same way on its own
    [probe](../../docs/sources/group-and-iteration-probes.md#src-starred-group-operand-extent). An
    unfiltered starred Boolean field likewise projects only its in-capacity rows under both Boolean
    constants ([checkpoint](../../docs/sources/group-and-iteration-probes.md#src-boolean-starred-field-capacity)).
    Filtered Boolean stars and Confirm stars retain the complete projection because neither carrier
    is measured. -/
def resolvedCheckedValidationSide
    (checked : CheckedBooleanValueCountOperand model expected)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError (ResolvedValueListSide .token) := do
  let (core, hasUninstantiatedTail) ← match checked with
    | .field source =>
        (document.resolveCheckedDirectEntityOperandCore source.declaration.id)
          |>.map fun core => (core, core.hasUninstantiatedTail)
    | .star source =>
        (source.source.resolveCheckedValidationEntityOperandCore document outer
          (source.filter.map (·.condition)))
          |>.map fun core => (core, core.hasUninstantiatedTail)
    | .group source => do
        let core ← document.resolveCheckedGroupEntityOperandCore outer
          source.source.boundLevelCount source.fields
        let hasUninstantiatedTail ←
          source.resolveCheckedUninstantiatedTail document outer
        pure (core, hasUninstantiatedTail)
  let addressed := match checked with
    | .group _ => core.inCapacityAddressedCells
    | .star source =>
        match source.filter, source.source.declaration.policy.kind with
        | none, .boolean => core.inCapacityAddressedCells
        | _, _ => core.addressedCells
    | .field _ => core.addressedCells
  pure {
    cells := addressed.map fun cell =>
      booleanValueCountCellAt .validation cell.cell
    hasUninstantiatedTail
    hasHaving := core.hasHaving
    hasNonRelevant := core.hasNonRelevant }

end CheckedBooleanValueCountOperand

namespace CheckedBooleanValueCountSource

/-- Full validation preserves authored slot order, omitted tails, and per-filter match provenance. -/
def evaluateValidation (checked : CheckedBooleanValueCountSource model)
    (document : Document) (outer : Env)
    (directRead : FieldId → CheckedCell)
    (starRead : Env → FieldId → CheckedCell) :
    Except StarAddressingError NumericOperand :=
  evalResolvedValueCountOperands
    (booleanValueCountToken checked.expected) checked.operands fun operand => do
      pure (.inl (← operand.resolvedValidationSide document outer
        directRead starRead))

/-- Full validation over the immutable checked document reuses the common addressed entity core before applying Boolean/Confirm classification. -/
def evaluateCheckedDocumentValidation
    (checked : CheckedBooleanValueCountSource model)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError NumericOperand :=
  evalResolvedValueCountOperands
    (booleanValueCountToken checked.expected) checked.operands fun operand => do
      pure (.inl (←
        operand.resolvedCheckedValidationSide document outer))

/-- Computation uses the same checked source and tally while retaining computation-phase filter and value poison. -/
def evaluateComputation (checked : CheckedBooleanValueCountSource model)
    (document : Document) (outer : Env)
    (directRead : FieldId → CheckedCell)
    (filterRead starRead : Env → FieldId → CheckedCell) :
    Except StarAddressingError NumericOperand :=
  evalResolvedValueCountOperands
    (booleanValueCountToken checked.expected) checked.operands fun operand =>
      operand.resolvedComputationSide document outer directRead
        filterRead starRead

end CheckedBooleanValueCountSource

end A12Kernel
