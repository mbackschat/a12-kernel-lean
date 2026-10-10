import A12Kernel.Semantics.TemporalDistinctCount
import A12Kernel.Elaboration.TemporalValuesNotUnique
import A12Kernel.Elaboration.PartialSemanticIndex

/-! # Checked temporal `NumberOfDifferentValues`

The temporal overload of the distinct count, and the operator that sits closest to
`FieldValuesNotUnique` while gating differently. Slot certification, authored order, and the
shared shape rules are that neighbour's and are reused unchanged; what differs is the one thing
this module owns.

**Admission is the operand list's shared component set — after Base Year supplementation — and not
its shared declared format.** Two DATE
fields spelled `yyyy-MM-dd` and `dd.MM.yyyy` name the same components and are **admitted** here,
while the neighbouring uniqueness operator refuses that exact pair; a differing set such as
`yyyy-MM-dd` beside `yyyy-MM` is refused `MVK_DATEFORMATS_NOT_COMPATIBLE` naming both formats
([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-distinct-count-component-set-and-locus)).
So the two operators genuinely differ on one field pair and neither gate may be read off the other.

The component set is taken from the **declaration**, which is equivalent to reading it off the
declared format on every model this project admits: the stored-text classifiers already refuse a
declaration whose format and component set contradict each other, and whether the Kernel accepts
such a declaration at all is unmeasured and owned by SG21. Stated as a total function either way, so
no reachability question gates the clause.

**A group operand is admitted, and its expansion is gated by this operator's rule.** The group's
own certificate is therefore this module's rather than the neighbour's: a group carrying one
component set in two spellings is admitted here and refused there, on the identical group
([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-temporal-group-operand-follows-its-own-operator)). Two
completed users whose gates genuinely differ is the case the reuse rule excludes, so the certificate
is duplicated deliberately. A fixed group beneath an unstarred repeatable ancestor is refused by the
ordinary binding rule, which is the shared shape checker's business and not this gate's.

**Every admitted operand shape folds, the starred group included**, because a group operand resolves
*as a group* through the shared resolver at its own depth rather than being lifted into its
expansion's fields. The lift was the reason the starred shape had to be refused, so removing it
closed the arm instead of widening it; `resolveDistinctCountCore` owns that reasoning.
-/

namespace A12Kernel

/-- The component set a certified temporal operand's declaration names. Total: a slot that reached
    certification carries a temporal kind, and the non-temporal arm cannot occur. -/
def CheckedTemporalUniquenessField.components
    (checked : CheckedTemporalUniquenessField) : TemporalComponents :=
  match checked.declaration.policy.kind with
  | .temporal _ components => components
  | _ =>
      { year := false, month := false, day := false
        hour := false, minute := false, second := false }

/-- The component set one shared slot contributes to the list's gate. -/
def CheckedTemporalUniquenessOperand.components :
    CheckedTemporalUniquenessOperand model → TemporalComponents
  | .field source | .star _ source _ => source.components
  | .group source => source.first.components
  | .selected source _ => source.first.components

/-- Find the first expanded declaration whose component set differs from the group's own, reporting
    its path and its declared format. The group's **internal** agreement obligation, which is this
    operator's gate and not the neighbour's.

    Deliberately **exact**, where the operand-list gate supplements a declared Base Year: no row
    measures a group expansion mixing a yearless declaration with a year-bearing one, so extending
    the supplementation here would cross a carrier boundary on an assumption. -/
def firstMismatchedTemporalFieldComponents?
    (expected : TemporalComponents) :
    List CheckedTemporalUniquenessField → Option (List String × String)
  | [] => none
  | field :: remaining =>
      if field.components == expected then
        firstMismatchedTemporalFieldComponents? expected remaining
      else
        some (field.path, field.format)

/-- One authored group slot certified for **this** operator: a nonempty, wholly temporal expansion
    agreeing on one component set.

    Deliberately not the neighbour's `CheckedTemporalUniquenessGroup`, whose `oneDeclaredFormat`
    obligation is the uniqueness carrier's gate. That certificate refuses a group carrying one
    component set in two spellings, and the Kernel **admits** exactly that group here while refusing
    it there ([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-temporal-group-operand-follows-its-own-operator)).
    Two completed users whose gates genuinely differ is the case the reuse rule excludes, so the
    certificate is duplicated on purpose rather than parameterized. -/
structure CheckedTemporalDistinctCountGroup (model : FlatModel) where
  private mk ::
  source : CheckedEntityGroupSource model
  first : CheckedTemporalUniquenessField
  rest : List CheckedTemporalUniquenessField
  expansionOwned :
    (model.groupSubtreeFields source.groupPath).filterMap
      FlatFieldDecl.toTemporalUniquenessField? = first :: rest
  expansionAllTemporal :
    (model.groupSubtreeFields source.groupPath).all
      (fun declaration => declaration.toTemporalUniquenessField?.isSome) = true
  oneComponentSet :
    firstMismatchedTemporalFieldComponents? first.components rest = none

namespace CheckedTemporalDistinctCountGroup

def groupPath (group : CheckedTemporalDistinctCountGroup model) : GroupPath :=
  group.source.groupPath

def declarations (group : CheckedTemporalDistinctCountGroup model) :
    List FlatFieldDecl :=
  (group.first :: group.rest).map (·.declaration)

def components (group : CheckedTemporalDistinctCountGroup model) :
    TemporalComponents :=
  group.first.components

/-- The expansion's leading declared precision. Its own component gate makes the set shared, and a
    mixed-precision expansion is not separately measured — the leading declaration is the one this
    operator's positional class already reads. -/
def partialMode (group : CheckedTemporalDistinctCountGroup model) :
    TemporalPartialMode :=
  group.first.partialMode

def format (group : CheckedTemporalDistinctCountGroup model) : String :=
  group.first.format

end CheckedTemporalDistinctCountGroup

/-- One certified slot of this operator's list. The scalar forms reuse the shared certifier
    unchanged; only the group arm is this operator's own, for the reason its certificate states. -/
inductive CheckedTemporalDistinctCountOperand (model : FlatModel) where
  | slot (operand : CheckedTemporalUniquenessOperand model)
  | group (source : CheckedTemporalDistinctCountGroup model)
  | selected (source : CheckedSelectedTemporalEntity model)
      (oneComponentSet : firstMismatchedTemporalFieldComponents? source.first.components source.rest = none)

namespace CheckedTemporalDistinctCountOperand

def components : CheckedTemporalDistinctCountOperand model → TemporalComponents
  | .slot operand => operand.components
  | .group source => source.components
  | .selected source _ => source.first.components

def format : CheckedTemporalDistinctCountOperand model → String
  | .slot operand => operand.format
  | .group source => source.format
  | .selected source _ => source.first.format

def path : CheckedTemporalDistinctCountOperand model → List String
  | .slot operand => operand.path
  | .group source => source.groupPath
  | .selected source _ => source.path

/-- Whether this slot reads `field`. `filterReads` decides which of a filter's reads count: every
    read for a dependency or pointer, only the marked ones for the rule's error-field gates. -/
def referencesField (operand : CheckedTemporalDistinctCountOperand model) (field : FieldId)
    (filterReads : CorrelatedHaving → FieldId → Bool := CorrelatedHaving.referencesField) : Bool :=
  match operand with
  | .slot (.field source) => source.declaration.id == field
  | .slot (.star _ source filter) =>
      source.declaration.id == field || filter.any (filterReads · field)
  | .slot (.group source) => source.declarations.any (·.id == field)
  | .slot (.selected source _) | .selected source _ => source.referencesField field
  | .group source => source.declarations.any (·.id == field)

def hasHaving : CheckedTemporalDistinctCountOperand model → Bool
  | .slot operand => operand.hasHaving
  | .group _ | .selected _ _ => false

end CheckedTemporalDistinctCountOperand

inductive TemporalDistinctCountElabError where
  /-- A slot refusal from the shared temporal certifier. Wrapped rather than restated because slot
      certification is identical across the two operators; the **codes** are not, so the projection
      below re-maps each arm instead of delegating. -/
  | slot (error : TemporalValuesNotUniqueElabError)
  /-- **This operator's own gate.** An operand whose component set differs from the list's, carrying
      both declared formats because the Kernel's message names them rather than the sets. -/
  | mixedComponentSets (path : List String) (found expected : String)
  /-- A **partially known** Date operand. This operator compares the decoded date, which a partial
      does not have, and refuses all three declared precisions where its uniqueness neighbour admits
      every one ([checkpoint](../../docs/sources/repeatable-temporal-computation-probes.md#src-partial-date-precision-operand-gate)). -/
  | partialDate (path : List String) (mode : TemporalPartialMode)
  /-- A group whose expansion's **first** declaration is not temporal, so the authored list is not
      this overload's at all. **No class is claimed**: the Kernel reports the leading family's own
      code — `MVK_NUMBER_AND_NON_NUMBER` for a Number-first expansion — which the Number overload
      owns, exactly as it does for a scalar list whose first operand is a Number
      ([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-temporal-group-operand-follows-its-own-operator)).
      The positional rule reaches a group's expansion in declaration order, so which family leads
      decides the code and the offending kind alone does not. -/
  | groupExpansionFirstNotTemporal (path : List String)
      (actual : SurfaceScalarKind)
  | incoherentCore
  deriving Repr, DecidableEq

/-- Find the first operand whose component set differs from the list's, reporting its path, its own
    declared format, and the list's. Public because the certificate states its gate in terms of it.

    Both sides are supplemented, not just the yearless one: the rule is agreement of the sets the
    model can actually supply, and asking which side "needs" the year would make the gate
    order-sensitive where it is not. -/
def firstMismatchedTemporalComponents? (hasBaseYear : Bool)
    (expectedComponents : TemporalComponents) (expectedFormat : String) :
    List (CheckedTemporalDistinctCountOperand model) →
      Option (List String × String × String)
  | [] => none
  | operand :: remaining =>
      if operand.components.supplementedByBaseYear hasBaseYear
          == expectedComponents.supplementedByBaseYear hasBaseYear then
        firstMismatchedTemporalComponents? hasBaseYear expectedComponents expectedFormat remaining
      else
        some (operand.path, operand.format, expectedFormat)

/-- One checked temporal distinct-count operand list, certified to share a single component set.
    Deliberately **not** certified to share a format: that is the neighbour's gate and would refuse
    a pair the Kernel admits. -/
structure CheckedTemporalDistinctCountSource (model : FlatModel) where
  private mk ::
  shape : CheckedFieldEntityShape model
  first : CheckedTemporalDistinctCountOperand model
  rest : List (CheckedTemporalDistinctCountOperand model)
  filterBindingScope : List RepeatableLevel
  oneComponentSet :
    firstMismatchedTemporalComponents? model.hasBaseYear first.components first.format rest = none

namespace CheckedTemporalDistinctCountSource

def operands (checked : CheckedTemporalDistinctCountSource model) :
    List (CheckedTemporalDistinctCountOperand model) :=
  checked.first :: checked.rest

/-- Direct reads retain their identities for target-scope admission; expanded reads carry their
    binding certificates in the shared entity shape. -/
def directFieldIds (checked : CheckedTemporalDistinctCountSource model) : List FieldId :=
  checked.operands.filterMap fun
    | .slot (.field source) => some source.declaration.id
    | _ => none

/-- The scalar reader has no row topology, so only direct field slots can use it. -/
def isDirectOnly (checked : CheckedTemporalDistinctCountSource model) : Bool :=
  checked.operands.all fun | .slot (.field _) => true | _ => false

def referencesField (checked : CheckedTemporalDistinctCountSource model) (field : FieldId)
    (filterReads : CorrelatedHaving → FieldId → Bool := CorrelatedHaving.referencesField) : Bool :=
  checked.operands.any (·.referencesField field filterReads)

def hasHaving (checked : CheckedTemporalDistinctCountSource model) : Bool :=
  checked.operands.any (·.hasHaving)

/-- Expanded levels bind themselves; captured filter levels remain required from the caller. -/
def bindingScopes (checked : CheckedTemporalDistinctCountSource model) : List (List RepeatableLevel) :=
  checked.shape.operands.flatMap (·.bindingScopes) ++
    (if checked.hasHaving then [checked.filterBindingScope] else [])

/-- The list's shared component set, which every operand carries by construction. -/
def components (checked : CheckedTemporalDistinctCountSource model) :
    TemporalComponents :=
  checked.first.components

end CheckedTemporalDistinctCountSource

/-- The group source a slot names, or `none` for a scalar slot. Every group form resolves to the
    shared `CheckedEntityGroupSource`, so all three are certified by one path here. -/
private def groupSlotSource? :
    ResolvedFieldEntityOperand model → Option (CheckedEntityGroupSource model)
  | .group reference => some (.fixed reference)
  | .starredGroup source => some (.starred source)
  | .starredGroupPresence source => some (.starredPresence source)
  | .indexed _ | .keyed _ | .field .. | .star _ | .starHaving _ _ => none

/-- Certify one group slot against **this** operator's component-set gate. -/
private def certifyDistinctCountGroup (model : FlatModel)
    (source : CheckedEntityGroupSource model) :
    Except TemporalDistinctCountElabError
      (CheckedTemporalDistinctCountOperand model) :=
  let declarations := model.groupSubtreeFields source.groupPath
  if hAll : declarations.all
      (fun declaration => declaration.toTemporalUniquenessField?.isSome) = true then
    match hExpansion : declarations.filterMap
        FlatFieldDecl.toTemporalUniquenessField? with
    | [] => throw (.slot (.groupExpansionEmpty source.groupPath))
    | first :: rest =>
        match hComponents :
            firstMismatchedTemporalFieldComponents? first.components rest with
        | some (path, found) =>
            throw (.mixedComponentSets path found first.format)
        | none =>
            pure (.group {
              source
              first
              rest
              expansionOwned := hExpansion
              expansionAllTemporal := hAll
              oneComponentSet := hComponents })
  else
    -- A non-temporal declaration in the expansion, and **position decides the class** here exactly
    -- as it does in a scalar list. A leading non-temporal declaration means the list belongs to
    -- another overload, which draws its own code; a later one is this overload's date/non-date
    -- refusal. The offending declaration is found and re-certified either way, so the refusal names
    -- its own kind and path rather than the group path with a fabricated one.
    match declarations.head? with
    | some leading =>
        if leading.toTemporalUniquenessField?.isNone then
          throw (.groupExpansionFirstNotTemporal leading.path
            leading.policy.kind.surfaceKind)
        else
          match declarations.find? fun declaration =>
              declaration.toTemporalUniquenessField?.isNone with
          | some declaration =>
              match certifyTemporalUniquenessField declaration with
              | .error error => throw (.slot error)
              | .ok _ => throw .incoherentCore
          | none => throw .incoherentCore
    | none => throw (.slot (.groupExpansionEmpty source.groupPath))

private def certifyDistinctCountSelected
    (source : Sum (CheckedSemanticIndexSource model) (CheckedKeyedEntityExtent model)) :
    Except TemporalDistinctCountElabError (CheckedTemporalDistinctCountOperand model) := do
  let source ← certifySelectedTemporalEntity source |>.mapError .slot
  match hComponents : firstMismatchedTemporalFieldComponents? source.first.components source.rest with
  | some (path, found) => throw (.mixedComponentSets path found source.first.format)
  | none => pure (.selected source hComponents)

/-- Certify one slot: the scalar forms through the shared certifier, a group through this
    operator's own. -/
private def certifyDistinctCountOperand (model : FlatModel)
    (declaringGroup bindingGroup : GroupPath) (operand : ResolvedFieldEntityOperand model) :
    Except TemporalDistinctCountElabError
      (CheckedTemporalDistinctCountOperand model) :=
  match operand with
  | .indexed source => certifyDistinctCountSelected (.inl source)
  | .keyed source => certifyDistinctCountSelected (.inr source)
  | _ =>
      match groupSlotSource? operand with
      | some source => certifyDistinctCountGroup model source
      | none =>
          (certifyTemporalUniquenessOperand model declaringGroup operand bindingGroup).map .slot
            |>.mapError .slot

private def certifyDistinctCountOperands (model : FlatModel)
    (declaringGroup bindingGroup : GroupPath) :
    List (ResolvedFieldEntityOperand model) →
      Except TemporalDistinctCountElabError
        (List (CheckedTemporalDistinctCountOperand model))
  | [] => pure []
  | operand :: remaining => do
      pure ((← certifyDistinctCountOperand model declaringGroup bindingGroup operand) ::
        (← certifyDistinctCountOperands model declaringGroup bindingGroup remaining))

/-- The first operand in authored order whose declared precision is not fully known. -/
def firstPartialTemporalOperand? :
    List (CheckedTemporalDistinctCountOperand model) →
      Option (List String × TemporalPartialMode)
  | [] => none
  | operand :: remaining =>
      match operand with
      | .slot slot =>
          if slot.partialMode == .full then
            firstPartialTemporalOperand? remaining
          else
            some (slot.path, slot.partialMode)
      | .selected source _ =>
          match (source.first :: source.rest).find? (·.partialMode != .full) with
          | some field => some (field.path, field.partialMode)
          | none => firstPartialTemporalOperand? remaining
      | .group source =>
          if source.partialMode == .full then
            firstPartialTemporalOperand? remaining
          else
            some (source.groupPath, source.partialMode)

/-- Certify one authored operand list for the temporal distinct count.

    Slot certification is the shared one; the list gate is this operator's own. A **group** slot is
    certified here by `certifyDistinctCountGroup` rather than by the shared group certificate, which
    carries the neighbouring operator's format-equality gate and would refuse an expansion this
    operator admits — one component set in two spellings
    ([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-temporal-group-operand-follows-its-own-operator)). -/
def elaborateTemporalDistinctCountSource (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceFieldEntitySource)
    (writtenGroup : GroupPath := declaringGroup) (fixedTargetGroup? : Option GroupPath := none) :
    Except TemporalDistinctCountElabError
      (CheckedTemporalDistinctCountSource model) := do
  let shape ← elaborateFieldEntityShape model declaringGroup authored (writtenGroup := writtenGroup)
    (fixedTargetGroup? := fixedTargetGroup?)
    |>.mapError fun error => .slot (.shape error)
  match firstKindGateRefusal? shape.operands with
  | some refusal => throw (.slot refusal)
  | none => pure ()
  let bindingGroup := fixedTargetGroup?.getD writtenGroup
  let first ← certifyDistinctCountOperand model declaringGroup bindingGroup shape.first
  let rest ← certifyDistinctCountOperands model declaringGroup bindingGroup shape.rest
  -- The precision gate is this operator's own and is applied in authored order, before the
  -- component-set gate: a partial declaration carries a complete component set, so the two gates
  -- are independent and a list can be refused by either.
  match firstPartialTemporalOperand? (first :: rest) with
  | some (path, mode) => throw (.partialDate path mode)
  | none => pure ()
  match hComponents :
      firstMismatchedTemporalComponents? model.hasBaseYear first.components first.format rest with
  | some (path, found, expected) =>
      throw (.mixedComponentSets path found expected)
  | none => pure {
      shape, first, rest
      filterBindingScope := model.repeatableScopeForGroupPath bindingGroup
      oneComponentSet := hComponents }

namespace TemporalDistinctCountElabError

/-- Project this operator's own gate and delegate the shared shape classes. The component-set
    refusal is `MVK_DATEFORMATS_NOT_COMPATIBLE`, measured naming both formats
    ([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-distinct-count-component-set-and-locus)). -/
def diagnostic? : TemporalDistinctCountElabError → Option KernelStaticDiagnostic
  | .mixedComponentSets _ _ _ => some .dateFormatsNotCompatible
  | .partialDate _ _ => some .partialDateNotAllowed
  -- Re-mapped, never delegated: the shared certifier's own projection carries the neighbour's
  -- codes, and the two operators' kind-domain classes differ by one token —
  -- `MVK_ONLY_STRING_ENUM_NUMBER_CMP_DATE_ALLOWED` here against the `CMP_`-less form there.
  | .slot (.inadmissibleKind _ _) => some .onlyStringEnumNumberCmpDateAllowed
  | .slot (.mixedCategories _ _) => some .dateAndNonDate
  -- No class: the leading family's own overload reports, and this one claims nothing about it.
  | .groupExpansionFirstNotTemporal _ _ => none
  | .slot (.shape error) => error.diagnostic?
  | .slot _ => none
  | .incoherentCore => none

end TemporalDistinctCountElabError

/-! ## The runtime fold

The compared identity is decoded at the declared component set, unlike uniqueness's stored-text
identity ([`spec/07`](../../spec/07-repetition-and-iteration.md)). Date, yearless-date, clock and instant
atoms preserve these distinct comparison domains. Differently spelled formats can therefore denote
one counted value, even where uniqueness's exact-format admission gate refuses the same list.

`CheckedTemporalDistinctCountRun` certifies the runtime's component boundary: date precision can
omit components, while a time-bearing set must name every component of its comparison atom.
Operand shape imposes no additional runtime restriction; scalar, star, group and selected sources
retain their own resolution contracts. The time-bearing and group-fold checkpoints cited below
settle those identities; selected compositions retain the evidence status in the implementation map.

**Every date precision folds, at its own precision.** A component-omitting list is counted at the
shared set after Base Year supplementation, and a list with no year available anywhere is counted on
the calendar position it spells
([checkpoint](../../docs/sources/temporal-runtime-fold-probes.md#src-distinct-count-component-omitting-fold)).
Each operand is projected through **its own** declared set, so one list may hold operands the Base
Year supplements differently. The omitted components are supplied canonically by the projection
rather than read off the cell, which is what keeps the count the declaration's rather than the
producer's.
-/

/-- The `(row × field)` extent one admitted operand reaches, whatever shape it was authored in.

    **A group operand resolves as a group and is never lifted into its fields.** The lift this
    replaced mapped a group's expansion to fixed-path slots, which addressed row one of anything the
    operand reopened — so a *starred* group had to be refused to stay honest, and the refusal was
    read as a missing arm rather than as the symptom it was. The shared group resolver already takes
    the operand's **own depth** and enumerates every instantiated row below it, and
    `CheckedEntityGroupSource.boundLevelCount` already distinguishes the two shapes: a fixed group's
    whole repeatable ancestry, a starred one's `firstStar`. So both fold through one call and neither
    needs a per-declaration star path — which `spec/07` warns against directly, since an extent read
    off star machinery rather than the model's repeatability gets it wrong
    ([resolver](CheckedStarDocument.lean)).

    Resolution stays **fold-local and is never a lowering**: the authored reference is retained
    because the wildcard gate reads the authored path, so a group operand and its written-out
    expansion remain two different models statically — the warning `CheckedEntityGroupSource`
    carries. This decides which cells the count reads, after admission was settled on the authored
    form. -/
def CheckedTemporalDistinctCountOperand.resolveDistinctCountCore
    (operand : CheckedTemporalDistinctCountOperand model)
    (document : CheckedDocument model) (outer : Env)
    (world : Option World := none) :
    Except CheckedAddressingError ResolvedCheckedEntityOperandCore :=
  match operand with
  | .slot inner => inner.resolveValidationCore (world := world) (traversalMode := .sparse) document outer
  | .selected source _ => throw (.checkedDocumentRequired source.path)
  | .group source =>
      document.resolveCheckedGroupEntityOperandCore outer
        source.source.boundLevelCount source.declarations

/-- One statically certified temporal distinct count that this project can also **evaluate**: a
    time-bearing shared set names every component its atom carries.

    **Every admitted operand shape now folds**, so the certificate carries no operand condition at
    all. The set does not have to be a *complete calendar date*, nor date-only: a component-omitting
    date list folds at its own precision and a time-bearing one at the clock or the instant, which is
    what the Kernel does, and each date operand's omitted components are supplied canonically by the
    projection rather than read off the cell — so a list whose declared sets differ under Base Year
    supplementation folds correctly too. -/
structure CheckedTemporalDistinctCountRun (model : FlatModel) where
  source : CheckedTemporalDistinctCountSource model
  timeSetComplete : timeBearingSetIsComplete source.components = true

/-- Why a Lean-certified source has no evaluator here. This internal representation limit has no
    measured Kernel refusal or admitted-format witness; `timeBearingSetIsComplete` owns that scope.
    Retaining the component set lets a consumer explain the precise missing projection. -/
inductive TemporalDistinctCountRunLimit where
  /-- A time-bearing set naming only some of the components its atom carries. Lean-certified and
      unevaluated, because the time atoms cannot be masked to a partial set the way the date ones
      are; `timeBearingSetIsComplete` owns the reason and the format-domain note. -/
  | incompleteTimeBearingSet (components : TemporalComponents)
  deriving Repr, DecidableEq

/-- Admit one checked source to the runtime, or report which restriction it falls outside. -/
def checkTemporalDistinctCountRun
    (source : CheckedTemporalDistinctCountSource model) :
    Except TemporalDistinctCountRunLimit
      (CheckedTemporalDistinctCountRun model) :=
  if hTimeSet : timeBearingSetIsComplete source.components = true then
    .ok { source, timeSetComplete := hTimeSet }
  else
    throw (.incompleteTimeBearingSet source.components)

namespace CheckedTemporalDistinctCountRun

/-- The arm this list folds at, read from the shared set and the model's Base Year. Using the first
    operand's declared set is exact: with a Base Year the arm is `.dated` whatever the sets say, and
    without one the source certifies every declared set equal. -/
def arm (operation : CheckedTemporalDistinctCountRun model) :
    TemporalDistinctCountFoldArm :=
  temporalDistinctCountFoldArm operation.source.components model.hasBaseYear

/-- Count distinct decoded dates from one immutable model-certified checked document. Slots resolve
    in authored order through the shared entity core, and the count itself is the kind-generic
    aggregate every distinct-count carrier already uses.

    Each slot is projected through **its own** declared component set, which is what lets one list
    hold operands the Base Year supplements differently — a yearless `MM-dd` beside a complete date
    reduces to the same identity because the Base Year supplies the one component it lacks. -/
def evaluate (operation : CheckedTemporalDistinctCountRun model)
    (document : CheckedDocument model) (outer : Env)
    (world : Option World := none) :
    Except CheckedAddressingError NumericOperand := do
  let sides ← operation.source.operands.mapM fun operand => do
    match operand with
    | .selected source _ | .slot (.selected source _) =>
        source.sideWith .validation document.source.toDocument outer (document.computationContextAt outer).read
          (document.computationContextAt outer).storedText document.computationFillContext.read document.storedTextIn
          (document.resolveSemanticIndexColumnWith document.read)
          (fun field cell _ => pure (temporalDistinctCountCell .validation field.components model.baseYear operation.arm cell))
    | _ =>
        let core ← operand.resolveDistinctCountCore (world := world) document outer
        pure ({
          cells := core.addressedCells.map
            (fun addressed => temporalDistinctCountCell .validation operand.components model.baseYear
              operation.arm addressed.cell)
          hasUninstantiatedTail := core.hasUninstantiatedTail
          hasHaving := core.hasHaving
          hasNonRelevant := core.hasNonRelevant } : ResolvedValueListSide operation.arm.kind)
  pure (evalDistinctCountAggregate
    (sides.foldl ResolvedValueListSide.append ResolvedValueListSide.empty))

/-- Partial distinct counts require the aggregate's reduced-universal extent gate before
reading targets (spec/10 §5), then retain each declaration's decoded identity. -/
private def resolvePartialSide (operation : CheckedTemporalDistinctCountRun model)
    (operand : CheckedTemporalDistinctCountOperand model)
    (document : CheckedDocument model) (outer : Env) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell)) :
    Except CheckedAddressingError
      (Sum (ResolvedValueListSide operation.arm.kind) PartialValidationAggregateResult) := do
  let ordinary := fun (declarations : List FlatFieldDecl) (bound : Nat) => do
    if !declarations.all (fun declaration => scope.coversAggregateExtent model declaration.path
        (declaration.repeatableScope.take bound) (declaration.repeatableScope.drop bound) outer) then
      return none
    let (addresses, tail) ← model.groupOperandReads document.source.toDocument outer bound declarations
      (·.repeatableScope) |>.mapError CheckedAddressingError.addressing
    pure (some (.value { addresses, hasUninstantiatedTail := tail, extentRelevant := true }) :
      Option (CellObservation PartialSelectedExtent))
  let selection ← match operand with
    | .selected source _ | .slot (.selected source _) =>
        resolvePartialSelectedExtent source.source document scope outer read
          (.consumer (fun declaration bound reopened environment =>
            scope.coversAggregateExtent model declaration.path bound reopened environment)) true
    | .group source => ordinary source.declarations source.source.boundLevelCount
    | .slot (.group source) => ordinary source.declarations source.source.boundLevelCount
    | .slot (.field source) => ordinary [source.declaration] source.declaration.repeatableScope.length
    | .slot (.star path source _) => ordinary [source.declaration] path.path.firstStar
  match selection with
  | none => pure (.inr .nonRelevant)
  | some (.unknown cause) | some (.poison cause) => pure (.inr (.evaluated (.unknown cause)))
  | some .empty => pure (.inl { cells := [.empty], hasUninstantiatedTail := false, hasHaving := false })
  | some (.value extent) =>
      let mut reversed := []
      for (declaration, environment) in extent.addresses do
        let some cell ← read environment declaration.id
          | throw (.partialUnavailable environment declaration.id)
        let some field := declaration.toTemporalUniquenessField?
          | throw (.checkedDocumentRequired declaration.path)
        match temporalDistinctCountCell .validation field.components model.baseYear operation.arm cell with
        | .unknown cause => return .inr (.evaluated (.unknown cause))
        | cell => reversed := cell :: reversed
      let emptyScalar := match operand with
        | .selected source _ | .slot (.selected source _) =>
            match source.source with | .inl _ => true | .inr _ => false
        | _ => false
      pure (.inl {
        cells := if emptyScalar && extent.addresses.isEmpty then [.empty] else reversed.reverse
        hasUninstantiatedTail := extent.hasUninstantiatedTail, hasHaving := false })

/-- Count partial temporal identities through the existing ordered aggregate scan. Whole-rule
filters skip first; unavailability remains separate from formal causes (spec/10 §5). -/
def evaluatePartial (operation : CheckedTemporalDistinctCountRun model)
    (document : CheckedDocument model) (outer : Env) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell)) :
    Except CheckedAddressingError PartialValidationAggregateResult := do
  if operation.source.hasHaving then return .skippedHaving
  match ← scanResolvedValueListOperands
      (operation.resolvePartialSide · document outer scope read)
      (fun cause => .evaluated (.unknown cause))
      (fun accumulated _ side => accumulated.append side)
      operation.source.operands (ResolvedValueListSide.empty (kind := operation.arm.kind)) with
  | .inl side => pure (.evaluated (evalDistinctCountAggregate side))
  | .inr result => pure result

/-- Resolve typed identities through the caller's current computation view. The group walk and
    filtered-star scan are shared with the other list consumers; only the temporal projection is
    local (see the component-set and time-bearing checkpoints above). -/
private def computationSide (operation : CheckedTemporalDistinctCountRun model)
    (document : Document) (outer : Env) (directRead : FieldId → CheckedCell)
    (filterRead starRead : Env → FieldId → CheckedCell)
    (operand : CheckedTemporalDistinctCountOperand model)
    (world : Option World := none)
    (selectedRead : CheckedSelectedTemporalEntity model → Except StarAddressingError (ResolvedValueListSide operation.arm.kind) :=
      fun source => .error (.unsupportedGroupOperand source.path))
    (filterStoredText : Env → FieldId → Option String := fun _ _ => none)
    (filterNumberText : Env → FieldId → Option String := fun _ _ => none) :
    Except StarAddressingError (Sum (ResolvedValueListSide operation.arm.kind) NumericOperand) := do
  let project := temporalDistinctCountCell .computation operand.components model.baseYear operation.arm
  let groupSide := fun (boundCount : Nat) (declarations : List FlatFieldDecl) => do
    let (reads, tail) ← model.groupOperandReads document outer boundCount declarations (·.repeatableScope)
    pure (.inl {
      cells := reads.map (fun (declaration, environment) =>
        project (starRead environment declaration.id))
      hasUninstantiatedTail := tail, hasHaving := false } : Sum (ResolvedValueListSide operation.arm.kind) NumericOperand)
  match operand with
  | .selected source _ | .slot (.selected source _) => .inl <$> selectedRead source
  | .group source => groupSide source.source.boundLevelCount source.declarations
  | .slot (.group source) => groupSide source.source.boundLevelCount source.declarations
  | .slot (.field source) => pure (.inl {
      cells := [project (directRead source.declaration.id)]
      hasUninstantiatedTail := false, hasHaving := false })
  | .slot (.star path source filter) =>
      let resolved ← path.path.resolveInCapacity document outer
      let read := fun environment => project (starRead environment source.declaration.id)
      match filter with
      | none => pure (.inl (resolved.toResolvedSide read))
      | some having => do
          let traversal ← model.filterTraversal path.path
            (document.filterRows.getD document.instantiatedRows) outer
          let read := fun environment => project (model.filterRead document starRead environment source.declaration.id)
          let consume := fun cells environment => match read environment with
            | .unknown cause => .inr cause
            | cell => .inl (cell :: cells)
          match ← (having.scanComputation (({ read := model.filterRead document filterRead, storedText := filterStoredText, numberText := filterNumberText, world } : CorrelationContext).withModelComputationGroups model document) outer consume traversal.candidates [] traversal.occupancy).mapError (fun
            | .calendarUnavailable => .unsupportedDateCalendar
            | .valueFailure => .temporalValueFailure
            | .worldUnavailable => .worldUnavailable
            | .typeValidityValueFailure => .typeValidityValueFailure
            | .stringExpressionUnavailable => .stringExpressionUnavailable
            | .storedTextUnavailable fieldId => .storedTextUnavailable fieldId
            | .groupUnavailable path => .unsupportedGroupOperand path) with
          | .exhausted reversed => pure (.inl {
              cells := reversed.reverse
              hasUninstantiatedTail := resolved.domain.hasOpenTail
              hasHaving := true })
          | .terminated cause | .poison cause => pure (.inr (.unknown cause))

/-- Project each selected declaration through its own decoded temporal components and the
current computation overlay; the checked source keeps stored-text identity out of this fold. -/
def selectedSideWith (operation : CheckedTemporalDistinctCountRun model)
    (source : CheckedSelectedTemporalEntity model) (document : Document) (outer : Env)
    (direct : FieldId → CheckedCell) (stored : FieldId → Option String)
    (read : Env → FieldId → CheckedCell) (column : SemanticIndexColumnReader) :
    Except CheckedAddressingError (ResolvedValueListSide operation.arm.kind) :=
  source.sideWith .computation document outer direct stored read (fun _ _ => none) column
    (fun field cell _ => pure (temporalDistinctCountCell .computation field.components model.baseYear operation.arm cell))

/-- Fold the same typed identities as validation, with computation poison and fresh overlay reads.
    `scanResolvedValueListOperands` preserves the shared slot-unavailability and authored-order rules. -/
def evaluateComputation (operation : CheckedTemporalDistinctCountRun model)
    (document : Document) (outer : Env) (directRead : FieldId → CheckedCell)
    (filterRead starRead : Env → FieldId → CheckedCell)
    (world : Option World := none)
    (selectedRead : CheckedSelectedTemporalEntity model → Except StarAddressingError (ResolvedValueListSide operation.arm.kind) :=
      fun source => .error (.unsupportedGroupOperand source.path))
    (filterStoredText : Env → FieldId → Option String := fun _ _ => none)
    (filterNumberText : Env → FieldId → Option String := fun _ _ => none) : Except StarAddressingError NumericOperand := do
  match ← scanResolvedValueListOperands
      (state := ResolvedValueListSide operation.arm.kind) (terminal := NumericOperand)
      (operation.computationSide (world := world) document outer directRead filterRead starRead (selectedRead := selectedRead) (filterStoredText := filterStoredText) (filterNumberText := filterNumberText))
      (fun cause => .unknown cause)
      (fun accumulated _ side => accumulated.append side)
      operation.source.operands ResolvedValueListSide.empty with
  | .inl side => pure (evalDistinctCountAggregate side)
  | .inr result => pure result

end CheckedTemporalDistinctCountRun

end A12Kernel
