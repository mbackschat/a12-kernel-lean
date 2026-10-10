import A12Kernel.Elaboration.NumericScale
import A12Kernel.Elaboration.NumericSource
import A12Kernel.Elaboration.FieldEntityList
import A12Kernel.Elaboration.StarNumber
import A12Kernel.Elaboration.CheckedStarDocument

/-! # Shared checked Number entity lists

This boundary owns the common authoring contract for Number-valued entity lists consumed by `FirstFilledValue`, `Sum`, `MinValue`, `MaxValue`, and Number-valued `NumberOfDifferentValues`. It resolves every direct, plain-star, filtered-star, group and index-selected slot in authored order; inherits direct-field duplication, fixed-group duplication, and strict-overlap rejection from the shared shape; retains the consuming operator’s arity rule; and certifies every expanded declaration as Number-valued. Runtime consumers retain their own scan semantics.
-/

namespace A12Kernel

namespace CheckedDocument

/-- Classify one model-owned Number field instance from the immutable checked input. The caller retains the authored operand and traversal; this query owns only address resolution and phase observation. Full-rule validation opts into its implicit-coordinate view (spec/07 §1); the default and computation retain physical addressing. -/
def numberValueListCellAt (document : CheckedDocument model)
    (phase : Phase) (environment : Env) (field : FlatNumberField)
    (fullDomain : Bool := false) :
    Except CheckedAddressingError (ValueListCell .number) := do
  let addressed ← match fullDomain, phase with
    | true, .validation => document.fullValidationAddressedCell environment field.id
    | _, _ => document.addressedCell environment field.id
  pure (observeCell phase addressed.cell).asNumberValueListCell

end CheckedDocument

/-- Number entity-list authors use the shared kind-independent syntax. -/
abbrev SurfaceNumberEntityOperand := SurfaceFieldEntityOperand

/-- Number entity-list authors use the shared nonempty source shape. -/
abbrev SurfaceNumberEntitySource := SurfaceFieldEntitySource

/-- Consumer-neutral name for the established direct nonempty Number field-list payload. -/
abbrev ResolvedDirectNumberEntityFields := ResolvedNumericAggregateFields

/-- One direct Number declaration certified against the source model. The list's shape decided which
reading scope binds its levels: the rule instance or the computation target. -/
structure CheckedNumberEntityField (model : FlatModel) where
  declaration : FlatFieldDecl
  field : FlatNumberField
  admitted : model.ownsField (.number field) = true
  fieldOwned : declaration.toNumberField? = some field

/-- One authored group-scope slot certified as Number-valued.

    `expansionOwned` and `expansionAllNumber` together are the certificate: the retained list **is** the group's recursive subtree in declaration order, nonempty by its shape, and no declaration in that subtree was dropped along the way. The second obligation is what makes the first a completeness claim rather than a filter — without it a subtree of Strings would certify as an empty selection. A consumer may therefore read the expansion off this slot without re-walking the model, while the authored reference stays available for re-rendering.

    `uniformSigned` is a **representation** obligation rather than a Kernel gate. Directional missingness reads each empty cell's own declaration, but the aggregate scan applies one signedness per authored operand, so a slot spanning declarations that disagree has no correct operand-level answer. Refusing that shape keeps the accessor sound; it claims nothing about what the Kernel admits, and widening it belongs with the runtime capsule that makes signedness per-cell. -/
structure CheckedNumberEntityGroup (model : FlatModel) where
  source : CheckedEntityGroupSource model
  first : FlatNumberField
  rest : List FlatNumberField
  expansionOwned :
    (model.groupSubtreeFields source.groupPath).filterMap
      FlatFieldDecl.toNumberField? = first :: rest
  expansionAllNumber :
    (model.groupSubtreeFields source.groupPath).all
      (fun declaration => declaration.toNumberField?.isSome) = true
  uniformSigned : rest.all (·.info.signed == first.info.signed) = true

namespace CheckedNumberEntityGroup

def groupPath (group : CheckedNumberEntityGroup model) : GroupPath :=
  group.source.groupPath

/-- The group's cells on the reader route, read through a caller-supplied checked-cell view over the
shared group walk `FlatModel.groupOperandReads`, so a group operand there takes the in-capacity
extent and canonical order the checked document gives it. -/
def resolvedSideIn (group : CheckedNumberEntityGroup model) (phase : Phase) (document : Document)
    (outer : Env) (read : Env → FieldId → CheckedCell) :
    Except StarAddressingError (ResolvedValueListSide .number) := do
  let (reads, hasUninstantiatedTail) ← model.groupOperandReads document outer
    group.source.boundLevelCount (model.groupSubtreeFields group.groupPath) (·.repeatableScope)
  pure { cells := reads.map fun (declaration, environment) =>
           (observeCell phase (read environment declaration.id)).asNumberValueListCell
         hasUninstantiatedTail
         hasHaving := false }

def isStarred (group : CheckedNumberEntityGroup model) : Bool :=
  group.source.isStarred

/-- The certified expansion, in model declaration order. -/
def fields (group : CheckedNumberEntityGroup model) : List FlatNumberField :=
  group.first :: group.rest

/-- The union scale of the whole expansion, so a nested subgroup's wider scale reaches the list's derived scale exactly as a directly authored operand would. -/
def scaleSummary (group : CheckedNumberEntityGroup model) : NumericScaleSummary :=
  group.rest.foldl
    (fun summary field => summary.union (NumericScaleSummary.field field.info.scale))
    (NumericScaleSummary.field group.first.info.scale)

/-- Sound because `uniformSigned` forces every expanded declaration to agree. -/
def declarationSigned (group : CheckedNumberEntityGroup model) : Bool :=
  group.first.info.signed

def referencesField (group : CheckedNumberEntityGroup model)
    (field : FieldId) : Bool :=
  group.fields.any (·.id == field)

/-- The all-rows aggregates' reduced-universal partial gate, asked field by field. -/
def allRowsRelevant (group : CheckedNumberEntityGroup model)
    (scope : ValidationRelevanceScope) (outer : Env) : Bool :=
  group.source.everyDeclarationCovers (model.groupSubtreeFields group.groupPath)
    fun path bound reopened => scope.coversAggregateExtent model path bound reopened outer

/-- The value count's existential partial gate, asked field by field. -/
def valueListExtentRelevant (group : CheckedNumberEntityGroup model)
    (scope : ValidationRelevanceScope) (outer : Env) : Bool :=
  group.source.everyDeclarationCovers (model.groupSubtreeFields group.groupPath)
    fun path bound reopened => scope.coversValueListExtent model path bound reopened outer

end CheckedNumberEntityGroup

/-- Homogeneous Number declarations behind one checked index selection. The complete expansion
and signedness certificate retain the same aggregate assumptions as an ordinary group slot. -/
structure CheckedSelectedNumberEntity (model : FlatModel) where
  private mk ::
  source : Sum (CheckedSemanticIndexSource model) (CheckedKeyedEntityExtent model)
  first : FlatNumberField
  rest : List FlatNumberField
  allNumber : (match source with
    | .inl source => [source.targetDeclaration]
    | .inr source => source.declarations).all (fun d => d.toNumberField?.isSome) = true
  expansionOwned : (match source with
    | .inl source => [source.targetDeclaration]
    | .inr source => source.declarations).filterMap FlatFieldDecl.toNumberField? = first :: rest
  uniformSigned : rest.all (·.info.signed == first.info.signed) = true

namespace CheckedSelectedNumberEntity

def groupPath (source : CheckedSelectedNumberEntity model) : GroupPath :=
  match source.source with
  | .inl source => source.targetDeclaration.groupPath
  | .inr source => source.groupPath

def isAlreadyMany (source : CheckedSelectedNumberEntity model) : Bool :=
  match source.source with | .inl _ => false | .inr _ => true

def referencesField (source : CheckedSelectedNumberEntity model) (field : FieldId) : Bool :=
  match source.source with
  | .inl source => source.referencesField field
  | .inr source => source.referencesField field

/-- The selected extent supplies addresses and omission; the Number scanner keeps its own
empty-value and poison policy (spec/08 §4.1 and spec/04 aggregates). -/
def sideWith (source : CheckedSelectedNumberEntity model) (phase : Phase)
    (document : Document) (outer : Env) (direct : FieldId → CheckedCell)
    (stored : FieldId → Option String) (read : Env → FieldId → CheckedCell)
    (column : SemanticIndexColumnReader) (missingStarIsOmitted : Bool := false) :
    Except CheckedAddressingError (ResolvedValueListSide .number) :=
  selectedValueListSideWith (missingStarIsOmitted := missingStarIsOmitted) source.source phase document outer direct stored read column
    (fun _ value => pure value.asNumberValueListCell)

def sideIn (source : CheckedSelectedNumberEntity model) (phase : Phase)
    (document : CheckedDocument model) (outer : Env) (missingStarIsOmitted : Bool := false) :
    Except CheckedAddressingError (ResolvedValueListSide .number) :=
  source.sideWith (missingStarIsOmitted := missingStarIsOmitted) phase document.source.toDocument outer (document.computationContextAt outer).read
    (document.computationContextAt outer).storedText document.computationFillContext.read
    (document.resolveSemanticIndexColumnWith document.read)

end CheckedSelectedNumberEntity

/-- A checked Number slot retains exactly the owner needed by its direct, plain-star, filtered-star, or group-scope runtime consumer. -/
inductive CheckedNumberEntityOperand (model : FlatModel) where
  | field (source : CheckedNumberEntityField model)
  | selected (source : CheckedSelectedNumberEntity model)
  | star (source : CheckedStarNumberSource model)
  | starHaving (source : CheckedStarNumberHavingSource model)
  | group (source : CheckedNumberEntityGroup model)

namespace CheckedNumberEntityOperand

def directFieldId? : CheckedNumberEntityOperand model → Option FieldId
  | .field source => some source.field.id
  | .selected _ | .star _ | .starHaving _ | .group _ => none

def directField? :
    CheckedNumberEntityOperand model → Option FlatNumberField
  | .field source => some source.field
  | .selected _ | .star _ | .starHaving _ | .group _ => none

/-- The retained group slot, for a consumer that must re-render or analyse the authored operand. -/
def groupSlot? :
    CheckedNumberEntityOperand model → Option (CheckedNumberEntityGroup model)
  | .group source => some source
  | .field _ | .selected _ | .star _ | .starHaving _ => none

/-- Whether one authored slot satisfies the multiple-operand requirement by itself. A star denotes a row set and a group denotes a field scope, so both are already-many; this is deliberately weaker than "is a star". -/
def isAlreadyMany : CheckedNumberEntityOperand model → Bool
  | .selected source => source.isAlreadyMany
  | .field _ => false
  | .star _ | .starHaving _ | .group _ => true

def hasHaving : CheckedNumberEntityOperand model → Bool
  | .starHaving _ => true
  | .field _ | .selected _ | .star _ | .group _ => false

def scaleSummary : CheckedNumberEntityOperand model → NumericScaleSummary
  | .selected source => source.rest.foldl (fun acc field => acc.union (NumericScaleSummary.field field.info.scale)) (NumericScaleSummary.field source.first.info.scale)
  | .field source => NumericScaleSummary.field source.field.info.scale
  | .star source => NumericScaleSummary.field source.field.info.scale
  | .starHaving source => NumericScaleSummary.field source.source.field.info.scale
  | .group source => source.scaleSummary

def declarationSigned : CheckedNumberEntityOperand model → Bool
  | .selected source => source.first.info.signed
  | .field source => source.field.info.signed
  | .star source => source.field.info.signed
  | .starHaving source => source.source.field.info.signed
  | .group source => source.declarationSigned

/-- Whether this slot reads `field`. `filterReads` decides which of a filter's reads count: every
    read for a dependency or pointer, only the marked ones for the rule's error-field gates. -/
def referencesField (field : FieldId)
    (filterReads : CorrelatedHaving → FieldId → Bool := CorrelatedHaving.referencesField) :
    CheckedNumberEntityOperand model → Bool
  | .field source => source.field.id == field
  | .star source => source.field.id == field
  | .starHaving source =>
      source.source.field.id == field ||
        filterReads source.having field
  | .group source => source.referencesField field
  | .selected source => source.referencesField field

end CheckedNumberEntityOperand

def firstDuplicateDirectNumberEntityField? :
    List (CheckedNumberEntityOperand model) → Option FieldId
  | operands => firstDuplicateDirectField? (fun operand => operand.directFieldId?) operands

/-- A checked nonempty homogeneous Number entity list with kernel-valid cardinality and direct-reference uniqueness. Wildcarded occurrences remain independent authored slots. -/
structure CheckedNumberEntitySource (model : FlatModel) where
  first : CheckedNumberEntityOperand model
  rest : List (CheckedNumberEntityOperand model)
  modelWellFormed : model.validate.isOk = true
  arity : EntityListArity := .manyRequired
  requiredMultiplicity : (arity.allowsSole || first.isAlreadyMany || !rest.isEmpty) = true
  uniqueDirectOperands :
    firstDuplicateDirectNumberEntityField? (first :: rest) = none

namespace CheckedNumberEntitySource

def operands (checked : CheckedNumberEntitySource model) :
    List (CheckedNumberEntityOperand model) :=
  checked.first :: checked.rest

/-- Whether this checked list contains a filtered wildcard slot. Partial validation uses this only as a rule-level early-skip discriminator; it never evaluates the filter. -/
def hasHaving (checked : CheckedNumberEntitySource model) : Bool :=
  checked.operands.any (fun operand => operand.hasHaving)

/-- Number entity-list operations derive the union/max scale of every authored declaration and gain no literal expansion capability. -/
def scaleSummary (checked : CheckedNumberEntitySource model) :
    NumericScaleSummary :=
  checked.rest.foldl
    (fun summary operand => summary.union operand.scaleSummary)
    checked.first.scaleSummary

def aggregateScaleSummary (op : NumericAggregateOp)
    (checked : CheckedNumberEntitySource model) : NumericScaleSummary :=
  match op with
  | .sum | .minimum | .maximum => checked.scaleSummary
  | .distinctCount => NumericScaleSummary.field 0

def referencesField (checked : CheckedNumberEntitySource model)
    (field : FieldId)
    (filterReads : CorrelatedHaving → FieldId → Bool := CorrelatedHaving.referencesField) :
    Bool :=
  checked.operands.any (·.referencesField field filterReads)

def directFields? (checked : CheckedNumberEntitySource model) :
    Option (FlatNumberField × List FlatNumberField) := do
  let first ← checked.first.directField?
  let rest ← checked.rest.mapM CheckedNumberEntityOperand.directField?
  pure (first, rest)

/-- Recover the legacy direct aggregate payload exactly when every checked entity-list operand is a direct field. Scalar computation and generated validation share this narrowing rather than reconstructing or rechecking source syntax. -/
def directResolvedFields?
    (checked : CheckedNumberEntitySource model) :
    Option ResolvedDirectNumberEntityFields := do
  let (first, rest) ← checked.directFields?
  pure { first, rest }

/-- Compatibility name for aggregate consumers of the common direct field-list narrowing. -/
def directAggregateFields?
    (checked : CheckedNumberEntitySource model) :
    Option ResolvedNumericAggregateFields :=
  checked.directResolvedFields?

end CheckedNumberEntitySource

def CheckedNumberEntitySource.bindingScopes (source : CheckedNumberEntitySource model) : List (List RepeatableLevel) :=
  source.operands.flatMap fun
    | .field field => [field.declaration.repeatableScope]
    | .selected source => match source.source with
      | .inl selected => selected.bindingScopes
      | .inr selected => selected.bindingScopes
    | .star source => [source.source.bindingScope]
    | .starHaving source => source.source.source.bindingScope ::
        (CorrelatedHaving.outerIterationScopes model source.having).filterMap id
    | .group source => [source.source.bindingScope]


inductive NumberEntityElabError where
  | shape (error : FieldEntityShapeElabError)
  /-- The list's **first** field operand is not Number-valued. Certification binds the first operand before the rest, so reaching any later arm implies this one passed — which is what lets the later arm read the list's family off its own position instead of carrying it. -/
  | fieldKindMismatch (path : List String) (actual : SurfaceScalarKind)
  /-- A **later** field operand is not Number-valued. Distinct from the arm above because the extrema's class is positional: here the first operand is already known Number-valued, so the Kernel reports `MVK_NOT_SORTABLE` for a temporal member too, where the same declaration in first position means the list was the temporal family's all along. -/
  | laterFieldKindMismatch (path : List String) (actual : SurfaceScalarKind)
  | star (error : StarNumberElabError)
  /-- A group with non-Number declarations. The offending kinds decide the extrema's class, while
      `numberLeads` retains whether the whole list's first expanded declaration is Number-valued;
      the distinct count needs that independent fact to project its positional class
      ([checkpoint](../../docs/sources/group-list-and-capacity-probes.md#src-distinct-count-first-operand-class)). -/
  | groupExpansionNotNumber (path : List String) (kinds : List SurfaceScalarKind)
      (numberLeads : Bool)
  /-- A group slot whose subtree declares no field at all, reached only as `RuleGroup` in a rule
      declared at an empty repeatable group; the shared shape refuses an explicit empty starred
      group first, as `MVK_GROUP_IS_EMPTY`. That spelling is unmeasured, so no class is claimed. -/
  | groupExpansionEmpty (path : List String)
  /-- A group slot whose expanded declarations disagree on signedness. A representation limit rather than a Kernel gate; see `CheckedNumberEntityGroup.uniformSigned`. -/
  | groupExpansionMixedSign (path : List String)
  | incoherentCore
  deriving Repr, DecidableEq

namespace NumberEntityElabError

/-- Whether the extrema are measured to refuse an operand of this declared kind **in first position**.

    The extrema's admitted set is **wider than this family's representable set**: they take Number *or* a temporal kind, while every value here is a Number field. A temporal operand in first position therefore reaches an error value meaning "this family cannot hold it", and must **not** be reported as a Kernel refusal, because the Kernel admits that model and refuses it — if at all — through the temporal list's own gate. Reading the family's own limit as `MVK_NOT_SORTABLE` is the defect these arms are written against.

    A temporal operand in a **later** position is the opposite case and answers `true` through `extremaRefuseLaterKind`: the first operand certified as Number, so the Kernel's own positional rule puts the whole list in the numeric family and refuses the temporal member. Both directions are measured ([checkpoint](../../docs/sources/group-list-and-capacity-probes.md#src-extrema-operand-family-is-positional)); the earlier reading that a Date is simply "admitted at this gate" was measured on the temporal list and does not survive the crossing.

    String, Enumeration, Boolean, Confirm, and DateRange are measured refused in first position; the checkpoint's kind grid records those controls. Number and every temporal kind are left to their own overloads, with the wider temporal leader set covered by the [reviewed handback](../../docs/sources/inbound-handbacks.md#reviewed-2026-09-07-handback--the-extremum-leader-set-and-the-powers-derived-scale). -/
private def extremaRefuseKind : SurfaceScalarKind → Bool
  | .string => true
  | .number => false
  -- A first-position temporal operand is the temporal list's, not a Kernel refusal here.
  | .temporal _ => false
  -- Measured to lead no overload, so each is refused outright where it once claimed nothing
  -- ([checkpoint](../../docs/sources/group-list-and-capacity-probes.md#src-extrema-operand-family-is-positional)). The comment
  -- here used to add "the sortable leader set is exactly `{NUMBER, DATE}`", which was refuted: the
  -- set is `{NUMBER}` plus **every** temporal kind, which is why the arm above returns `false` for
  -- `.temporal _` without inspecting the kind
  -- ([provenance](../../docs/sources/inbound-handbacks.md#reviewed-2026-09-07-handback--the-extremum-leader-set-and-the-powers-derived-scale)).
  | .enumeration | .boolean | .confirm | .dateRange => true

/-- Whether `Sum` is measured to refuse a field operand of this declared kind with its own domain
    class. That class reads neither position nor form: a String leading, behind a Number, and starred
    in either place all draw it
    ([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-entity-list-kind-empty-and-root-carriers)),
    so one predicate serves both field arms. Every other kind is unmeasured on a field operand. -/
private def sumRefuseKind : SurfaceScalarKind → Bool
  | .string => true
  | .number => false
  | .temporal _ | .enumeration | .boolean | .confirm | .dateRange => false

/-- Whether the extrema are measured to refuse an operand of this declared kind **after** a Number one. Temporal joins String here, which is the whole difference from first position. -/
private def extremaRefuseLaterKind : SurfaceScalarKind → Bool
  | .string | .temporal _ => true
  | .number => false
  -- Measured in later position too, so only NUMBER survives after a Number leader.
  | .enumeration | .boolean | .confirm | .dateRange => true

/-- The expansion-kind gate is **each operator's own question about the expansion's values**, which is why this projection is keyed by the operator where every gate the shared checker owns is not. One group whose subtree contains a String draws a different class under each of `Sum` and the extrema, and reading one carrier's class off a sibling is precisely the inference the Kernel refutes. The distinct count is stronger still: its class is not a property of the operator alone, so it is projected below rather than claimed.

    Shape refusals delegate to the shared checker, which already applied the consumer’s arity rule and the common star and duplicate gates.

    The extrema's class is additionally keyed by the **kind** that arrived, not merely by the operand failing to be a Number; see `extremaRefuseKind`. `Sum` needs no such split, because its admitted set and this family's representable set coincide, so nothing reaching its arm is a model the Kernel would accept. What stays open for `Sum` is only whether some unmeasured kind draws a *different* code, never whether it is refused.

    Direct and starred field-kind refusals retain leading versus later position. The distinct count
    therefore projects its Number-leading field class as well as the group class below
    ([checkpoint](../../docs/sources/group-list-and-capacity-probes.md#src-distinct-count-first-operand-class)). `Sum` projects its
    domain class from both field arms alike, because it is not keyed by position; see `sumRefuseKind`. -/
def aggregateDiagnostic? (op : NumericAggregateOp) :
    NumberEntityElabError → Option KernelStaticDiagnostic
  | .shape error => error.diagnostic?
  -- The filter's class is the filter's own and does not vary by wrapping carrier
  -- ([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-having-filter-comparison-and-scope-classes)), so it
  -- reaches every aggregate alike and needs no `op` split.
  | .star (.having error) => error.diagnostic?
  | .groupExpansionNotNumber _ kinds numberLeads =>
      match op with
      | .sum => some .noNumber
      -- One measured-refused kind decides the whole expansion: an admitted kind beside it does not
      -- rescue the list, which is why this is `any` and not "every kind is unadmitted".
      | .minimum | .maximum =>
          if kinds.any extremaRefuseKind then some .notSortable else none
      -- Other leading families belong to their own overloads. The offending group's kinds cannot
      -- settle this: a Number may precede the group, which the retained whole-list fact records.
      | .distinctCount => if numberLeads then some .numberAndNonNumber else none
  | .fieldKindMismatch _ actual =>
      match op with
      | .minimum | .maximum =>
          if extremaRefuseKind actual then some .notSortable else none
      -- A first operand that is not Number-valued means this list was never the Number family's, so
      -- the Kernel routes it to another overload rather than refusing — except for the two kinds no
      -- overload leads with. The distinct count's kind domain is string, enumeration, number, and
      -- date/time, so a Boolean or Confirm **first** operand is refused outright whatever follows
      -- it, while the same kind in a later position takes the leading family's homogeneity code
      -- instead ([checkpoint](../../docs/sources/group-list-and-capacity-probes.md#src-distinct-count-first-operand-class)).
      | .distinctCount =>
          match actual with
          | .boolean | .confirm => some .onlyStringEnumNumberCmpDateAllowed
          | _ => none
      | .sum => if sumRefuseKind actual then some .noNumber else none
  | .laterFieldKindMismatch _ actual =>
      match op with
      | .minimum | .maximum =>
          if extremaRefuseLaterKind actual then some .notSortable else none
      -- **The distinct count is keyed by position, and this arm is the position that determines it.**
      -- Reaching a *later* arm implies the first operand already certified Number-valued, so the list
      -- is Number-first, and Number-first with a non-Number member draws `MVK_NUMBER_AND_NON_NUMBER`
      -- ([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-distinct-count-operand-domain)). That is why the
      -- field arm gets that fact from certification order; the group arm retains it explicitly.
      --
      -- The kind that arrived does **not** matter here, and that is measured rather than assumed:
      -- `(Number, Boolean)` draws this same code, because once an admissible operand leads, a
      -- Boolean is merely "non-number" and the domain gate no longer applies
      -- ([checkpoint](../../docs/sources/group-list-and-capacity-probes.md#src-distinct-count-first-operand-class)). The domain
      -- code is a **first-operand** class only.
      | .distinctCount => some .numberAndNonNumber
      | .sum => if sumRefuseKind actual then some .noNumber else none
  | .star _ | .groupExpansionEmpty _ | .groupExpansionMixedSign _
  | .incoherentCore => none

end NumberEntityElabError

/-- A starred single-field operand refuses through the **direct field arm**, not a star-specific one.
    The Kernel's family gate reads the declaration and not the operand form: a starred field draws
    the same code as the plain field of that kind, in either position
    ([checkpoint](../../docs/sources/group-list-and-capacity-probes.md#src-extrema-operand-family-is-positional)). Routing here is
    what lets `atLaterOperand` re-key the star positionally and the existing kind predicates classify
    it; the former star arm carried neither the kind nor the position, so it could project nothing at
    all — `none` was sound only because the admitted DATE-first case shared it. -/
private def certifyStarNumber (source : CheckedStarFieldPath model) :
    Except NumberEntityElabError (CheckedStarNumberSource model) :=
  match hField : source.declaration.toNumberField? with
  | none =>
      throw (.fieldKindMismatch source.declaration.path
        source.declaration.policy.kind.surfaceKind)
  | some field => pure { source, field, fieldOwned := hField }

/-- Certify one authored group slot by expanding it once through the shared subtree query. The three refusals are distinct and all deliberately unprojected: `MVK_NO_NUMBER` and its siblings are each operator's own class, and this boundary has no operator. -/
private def certifyNumberEntityGroup (model : FlatModel)
    (source : CheckedEntityGroupSource model) :
    Except NumberEntityElabError (CheckedNumberEntityOperand model) :=
  if hAll : (model.groupSubtreeFields source.groupPath).all
      (fun declaration => declaration.toNumberField?.isSome) = true then
    match hExpansion :
        (model.groupSubtreeFields source.groupPath).filterMap
          FlatFieldDecl.toNumberField? with
    | [] => throw (.groupExpansionEmpty source.groupPath)
    | first :: rest =>
        if hSigned : rest.all (·.info.signed == first.info.signed) = true then
          pure (.group {
            source
            first
            rest
            expansionOwned := hExpansion
            expansionAllNumber := hAll
            uniformSigned := hSigned })
        else
          throw (.groupExpansionMixedSign source.groupPath)
  else
    throw (.groupExpansionNotNumber source.groupPath
      ((model.groupSubtreeFields source.groupPath).filterMap fun declaration =>
        if declaration.toNumberField?.isSome then none
        else some declaration.policy.kind.surfaceKind)
      (((model.groupSubtreeFields source.groupPath).head?).bind
        FlatFieldDecl.toNumberField?).isSome)

private def certifySelectedNumberEntity (model : FlatModel)
    (source : Sum (CheckedSemanticIndexSource model) (CheckedKeyedEntityExtent model)) :
    Except NumberEntityElabError (CheckedNumberEntityOperand model) := do
  let declarations := match source with | .inl s => [s.targetDeclaration] | .inr s => s.declarations
  let path := match source with | .inl s => s.targetDeclaration.path | .inr s => s.entityPath
  if hAll : declarations.all (fun d => d.toNumberField?.isSome) = true then
    match hFields : declarations.filterMap FlatFieldDecl.toNumberField? with
    | [] => throw (.groupExpansionEmpty path)
    | first :: rest =>
        if hSigned : rest.all (·.info.signed == first.info.signed) = true then
          pure (.selected { source, first, rest, allNumber := hAll, expansionOwned := hFields, uniformSigned := hSigned })
        else throw (.groupExpansionMixedSign path)
  else
    match source with
    | .inl s => throw (.fieldKindMismatch s.targetDeclaration.path s.targetDeclaration.policy.kind.surfaceKind)
    | .inr _ => throw (.groupExpansionNotNumber path
        (declarations.filterMap fun d => if d.toNumberField?.isSome then none else some d.policy.kind.surfaceKind)
        ((declarations.head?).bind FlatFieldDecl.toNumberField?).isSome)

private def certifyNumberEntityOperand (model : FlatModel)
    (declaringGroup bindingGroup : GroupPath) : ResolvedFieldEntityOperand model →
      Except NumberEntityElabError (CheckedNumberEntityOperand model)
  | .indexed source => certifySelectedNumberEntity model (.inl source)
  | .keyed source => certifySelectedNumberEntity model (.inr source)
  | .field declaration _ =>
      match hField : declaration.toNumberField? with
      | none => throw (.fieldKindMismatch declaration.path declaration.policy.kind.surfaceKind)
      | some field =>
          if hAdmitted : model.ownsField (.number field) = true then
            pure (.field {
              declaration
              field
              admitted := hAdmitted
              fieldOwned := hField })
          else
            throw .incoherentCore
  | .star source _ => do
      pure (.star (← certifyStarNumber source))
  | .starHaving source having _ => do
      let numberSource ← certifyStarNumber source
      let filter ← elaborateStarHavingCore model declaringGroup numberSource.source having bindingGroup
        |>.mapError fun error => .star (.having error)
      pure (.starHaving { source := numberSource, declaringGroup, bindingGroup, filter })
  | .group reference => certifyNumberEntityGroup model (.fixed reference)
  | .starredGroup source => certifyNumberEntityGroup model (.starred source)
  | .starredGroupPresence source =>
      certifyNumberEntityGroup model (.starredPresence source)

/-- A later operand is reached only after the leading operand certified Number-valued. Retain that
    whole-list fact even when a later group's own expansion starts with another kind; the group's
    offending-kind payload remains available to the other aggregates unchanged. -/
private def atLaterOperand :
    NumberEntityElabError → NumberEntityElabError
  | .fieldKindMismatch path actual => .laterFieldKindMismatch path actual
  | .groupExpansionNotNumber path kinds _ => .groupExpansionNotNumber path kinds true
  | error => error

private def certifyNumberEntityOperands (model : FlatModel)
    (declaringGroup bindingGroup : GroupPath) : List (ResolvedFieldEntityOperand model) →
      Except NumberEntityElabError (List (CheckedNumberEntityOperand model))
  | [] => pure []
  | operand :: remaining => do
      pure ((← (certifyNumberEntityOperand model declaringGroup bindingGroup operand).mapError
          atLaterOperand) ::
        (← certifyNumberEntityOperands model declaringGroup bindingGroup remaining))

/-- Certify an already checked entity-list shape as Number-valued without resolving its authored
    references a second time. Consumer-specific whole-list gates run between shape and kind
    certification through this boundary. -/
def certifyNumberEntityShape (model : FlatModel)
    (declaringGroup : GroupPath) (shape : CheckedFieldEntityShape model)
    (bindingGroup : GroupPath := declaringGroup) :
    Except NumberEntityElabError (CheckedNumberEntitySource model) := do
  let first ← certifyNumberEntityOperand model declaringGroup bindingGroup shape.first
  let rest ← certifyNumberEntityOperands model declaringGroup bindingGroup shape.rest
  if hMultiplicity : (shape.arity.allowsSole || first.isAlreadyMany || !rest.isEmpty) = true then
    match hDuplicate :
        firstDuplicateDirectNumberEntityField? (first :: rest) with
    | some _ => throw .incoherentCore
    | none => pure {
        first
        rest
        modelWellFormed := shape.modelWellFormed
        arity := shape.arity
        requiredMultiplicity := hMultiplicity
        uniqueDirectOperands := hDuplicate }
  else
    throw .incoherentCore

/-- Resolve and certify a Number list under its consumer’s arity rule. Aggregates keep the
many-required default; entity-valued membership uses the sole-allowed rule
([checkpoint](../../docs/sources/group-list-and-capacity-probes.md#src-group-capacity-consumers)). -/
def elaborateNumberEntitySource (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceNumberEntitySource)
    (fixedTargetGroup? : Option GroupPath := none) (writtenGroup : GroupPath := declaringGroup)
    (arity : EntityListArity := .manyRequired) (bindingGroup? : Option GroupPath := none) :
    Except NumberEntityElabError (CheckedNumberEntitySource model) := do
  let bindingGroup? := bindingGroup?.or fixedTargetGroup?
  let shape ←
    elaborateFieldEntityShapeIn model declaringGroup
      (bindingGroup?.map model.repeatableScopeForGroupPath |>.getD [])
      authored arity (fixedTargetGroup? := fixedTargetGroup?)
      (writtenGroup := writtenGroup)
    |>.mapError NumberEntityElabError.shape
  certifyNumberEntityShape model declaringGroup shape (bindingGroup?.getD declaringGroup)

/-- One authored Number operand resolved against the immutable checked input. The source retains declaration/filter metadata; the optional topology retains every canonical candidate environment, while `addressedCells` retains exactly the relevant or filter-selected cells that were read. -/
structure ResolvedCheckedNumberEntityOperand (model : FlatModel) where
  private mk ::
  source : CheckedNumberEntityOperand model
  core : ResolvedCheckedEntityOperandCore

namespace ResolvedCheckedNumberEntityOperand

def topology (resolved : ResolvedCheckedNumberEntityOperand model) :
    Option ResolvedStarTopology :=
  resolved.core.topology

def addressedCells (resolved : ResolvedCheckedNumberEntityOperand model) :
    List CheckedAddressedCell :=
  resolved.core.addressedCells

def hasUninstantiatedTail
    (resolved : ResolvedCheckedNumberEntityOperand model) : Bool :=
  resolved.core.hasUninstantiatedTail

def hasHaving (resolved : ResolvedCheckedNumberEntityOperand model) : Bool :=
  resolved.core.hasHaving

def hasNonRelevant
    (resolved : ResolvedCheckedNumberEntityOperand model) : Bool :=
  resolved.core.hasNonRelevant

/-- Project the rich addressed operand to the existing semantic side without losing its operand-local structural metadata. -/
def valueListSideAt (resolved : ResolvedCheckedNumberEntityOperand model)
    (phase : Phase) : ResolvedValueListSide .number :=
  { cells := resolved.core.addressedCells.map fun addressed =>
      (observeCell phase addressed.cell).asNumberValueListCell
    hasUninstantiatedTail := resolved.core.hasUninstantiatedTail
    hasHaving := resolved.core.hasHaving
    hasNonRelevant := resolved.core.hasNonRelevant }

/-- The capacity-bounded projection. A star or group operand already resolves in capacity, so this and `valueListSideAt` differ only on a direct operand read at an over-limit row ([checkpoint](../../docs/sources/group-list-and-capacity-probes.md#src-group-capacity-consumers)). -/
def inCapacityValueListSideAt
    (resolved : ResolvedCheckedNumberEntityOperand model)
    (phase : Phase) : ResolvedValueListSide .number :=
  { cells := resolved.core.inCapacityAddressedCells.map fun addressed =>
      (observeCell phase addressed.cell).asNumberValueListCell
    hasUninstantiatedTail := resolved.core.hasUninstantiatedTail
    hasHaving := resolved.core.hasHaving
    hasNonRelevant := resolved.core.hasNonRelevant }

end ResolvedCheckedNumberEntityOperand

namespace CheckedNumberEntityOperand

/-- Resolve one full-validation operand through the sole checked topology, filter, and addressed-cell owners. -/
def resolveCheckedValidationOperand
    (source : CheckedNumberEntityOperand model)
    (document : CheckedDocument model) (outer : Env)
    (world : Option World := none) (traversalMode : FilterTraversalMode := .requireSmall) :
    Except CheckedAddressingError
      (ResolvedCheckedNumberEntityOperand model) :=
  match source with
  | .selected selection => .error (.addressing (.unsupportedGroupOperand selection.groupPath))
  | .field direct => do
      let core ← document.resolveCheckedDirectEntityOperandCoreAt outer direct.field.id
      pure { source, core }
  | .star starSource => do
      let core ← starSource.source.resolveCheckedValidationEntityOperandCore (traversalMode := traversalMode)
        document outer none
      pure { source, core }
  | .starHaving filtered => do
      let core ←
        filtered.source.source.resolveCheckedValidationEntityOperandCore (traversalMode := traversalMode)
          document outer (some filtered.having) world
      pure { source, core }
  | .group slot => do
      let core ← document.resolveCheckedGroupEntityOperandCore outer
        slot.source.boundLevelCount (model.groupSubtreeFields slot.groupPath)
      pure { source, core }

/-- Project the selected or ordinary checked stream without inventing addresses for an absent
selection; rich selected pointer projection remains a separate boundary. -/
def checkedValidationSide (source : CheckedNumberEntityOperand model)
    (document : CheckedDocument model) (outer : Env)
    (world : Option World := none) (traversalMode : FilterTraversalMode := .requireSmall) (missingStarIsOmitted : Bool := false) : Except CheckedAddressingError (ResolvedValueListSide .number) := do
  match source with
  | .selected selection => selection.sideIn .validation document outer (missingStarIsOmitted := missingStarIsOmitted)
  | _ => pure ((← source.resolveCheckedValidationOperand (world := world) (traversalMode := traversalMode) document outer).valueListSideAt .validation)

/-- Resolve one unfiltered partial-validation operand. Direct masking precedes its read; a star retains canonical topology, reads only relevant concrete cells, and records incomplete extent on that exact authored operand. -/
def resolveCheckedPartialValidationOperand
    (source : CheckedNumberEntityOperand model)
    (document : CheckedDocument model) (outer : Env)
    (scope : ValidationRelevanceScope) :
    Except CheckedAddressingError
      (ResolvedCheckedNumberEntityOperand model) :=
  match source with
  | .selected selection => .error (.addressing (.unsupportedGroupOperand selection.groupPath))
  | .field direct =>
      if scope.coversCell model direct.declaration.path outer then do
        let core ← document.resolveCheckedDirectEntityOperandCoreAt outer direct.field.id
        pure { source, core }
      else
        pure { source, core := .nonRelevant }
  | .star starSource => do
      let core ←
        starSource.source.resolveCheckedPartialValidationEntityOperandCore
          document outer scope
      pure { source, core }
  | .starHaving _ =>
      -- The owning rule checks `hasHaving` and skips before any operand resolver.
      pure { source, core := .skippedHaving }
  | .group slot =>
      .error (.addressing (.unsupportedGroupOperand slot.groupPath))

end CheckedNumberEntityOperand

end A12Kernel
