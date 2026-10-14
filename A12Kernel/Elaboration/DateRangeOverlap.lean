import A12Kernel.Elaboration.Correlation
import A12Kernel.Elaboration.CheckedStarDocument
import A12Kernel.Elaboration.DateRangeBound
import A12Kernel.Elaboration.DateRangeInput
import A12Kernel.Elaboration.FieldEntityList
import A12Kernel.Semantics.DateRangeOverlapOperators

/-! # Checked DateRange overlap operands

This boundary owns static admission and full-validation checked-document assembly for the any-pair singular `DateRangesOverlap` operator, plus the certification steps, field walk and format/year agreement gate its plural sibling in `A12Kernel.Elaboration.AtLeastOneDateRangeOverlap` reuses. It reuses the shared entity-list shape and checked DateRange declaration policies; stored and selected fields additionally certify the internally supported year fragment plus measured year-month and Base-Year-completed fragment profiles while starred routes remain canonical. Every operand list passes the field walk and then the Kernel's format/year agreement gate, which is decided by the declarations and the model's Base Year alone, before any operand is certified. Pure overlap truth and polarity remain in `A12Kernel.Semantics.DateRangeOverlapOperators`.
-/

namespace A12Kernel

/-- Static refusal while certifying the singular DateRange overlap operand list. -/
inductive DateRangesOverlapElabError where
  | shape (error : FieldEntityShapeElabError)
  | sourceNotDateRange (path : List String) (actual : SurfaceScalarKind)
  | unsupportedPolicy (path : List String) (format separator : String)
  | unsupportedReadForm (path : List String) (form : FieldEntityReadForm)
  | groupsNotAllowed (path : GroupPath)
  | dateWithAndWithoutYear
  | yearInterpretationNotSupported (path : List String)
  | having (error : CorrelationElabError)
  | incoherentCore
  deriving Repr, DecidableEq

namespace DateRangesOverlapElabError

def diagnostic? : DateRangesOverlapElabError → Option KernelStaticDiagnostic
  | .shape error => error.diagnostic?
  | .groupsNotAllowed _ => some .noGroupsAllowed
  | .dateWithAndWithoutYear => some .dateWithAndWithoutYear
  | .yearInterpretationNotSupported _ => some .invalidDateRangeFormat
  -- The field walk raises this for the first field of another kind, ahead of the year question
  -- ([checkpoint](../../docs/sources/group-list-and-capacity-probes.md#src-overlap-field-walk-order)).
  | .sourceNotDateRange _ _ => some .noDateRange
  | .having error => error.diagnostic?
  | .unsupportedPolicy _ _ _ | .unsupportedReadForm _ _ | .incoherentCore => none

end DateRangesOverlapElabError

/-- Selection failure has no physical address; successful selection retains every actual cell.
Overlap projects both only at its consuming slot boundary (spec/07 §3, spec/08 §4.2). -/
inductive ResolvedDateRangeOverlapCore where
  | addressed (core : ResolvedCheckedEntityOperandCore)
  | selected (cells : CellObservation (List CheckedAddressedCell))

/-- Validation selection uses the authored index preliminary and retains its observation and actual
payload coordinate for the consuming slot projection (spec/07 §3, spec/08 §4.2). -/
def resolveSelectedOverlapCore (source : CheckedSemanticIndexSource model)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError ResolvedDateRangeOverlapCore := do
  let preliminary ← document.applySelectedFullIndexPreliminary [source.indexDeclaration.id]
    |>.mapError .indexPreliminary
  let column ← source.resolvePreliminaryColumn preliminary outer |>.mapError .semanticIndex
  let key ← source.observePreparedKey preliminary outer .validation
  match column.lookupEnvironment .validation source.numericIndex key with
  | .empty => pure (.selected .empty)
  | .unknown cause => pure (.selected (.unknown cause))
  | .poison cause => pure (.selected (.poison cause))
  | .value none => throw (.checkedDocumentRequired source.group.path)
  | .value (some environment) => do
      let cell ← document.addressedCellWithRead preliminary.readAuthoredValidation
        environment source.targetDeclaration.id
      pure (.selected (.value [cell]))

/-- Expand only below the selected row, retaining declaration-major physical addresses and the
selection outcome separately from overlap's skipped-slot projection (spec/08 §4). -/
def resolveKeyedOverlapCore (source : CheckedKeyedEntityExtent model)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError ResolvedDateRangeOverlapCore := do
  let context := document.computationContextAt outer
  let selected ← source.selectWith .validation (document.resolveSemanticIndexColumnWith document.read)
    outer context.read context.storedText
  match selected with
  | .empty => pure (.selected .empty)
  | .unknown cause => pure (.selected (.unknown cause))
  | .poison cause => pure (.selected (.poison cause))
  | .value environment => do
      let rows ← source.rows document.source.toDocument environment |>.mapError .addressing
      let cells ← rows.flatMapM fun (declaration, environments, _) =>
        environments.mapM fun row => document.fullValidationAddressedCell row declaration.id
      pure (.selected (.value cells))

/-- One certified canonical direct, plain-star, or filter-bearing star DateRange operand. -/
inductive CheckedDateRangesOverlapOperand (model : FlatModel) where
  | field (source : CheckedCanonicalDateRangeField)
  | indexed (selection : CheckedSemanticIndexSource model) (source : CheckedCanonicalDateRangeField)
  | keyed (selection : CheckedKeyedEntityExtent model) (source : CheckedCanonicalDateRangeField)
  | star (path : CheckedStarFieldPath model)
      (source : CheckedCanonicalDateRangeField)
      (filter : Option CorrelatedHaving)

namespace CheckedDateRangesOverlapOperand

def source : CheckedDateRangesOverlapOperand model →
    CheckedCanonicalDateRangeField
  | .field source | .indexed _ source | .keyed _ source | .star _ source _ => source

def hasHaving : CheckedDateRangesOverlapOperand model → Bool
  | .field _ | .indexed .. | .keyed .. | .star _ _ none => false
  | .star _ _ (some _) => true

/-- Resolve one full-validation operand through the shared checked direct/star addressing and filter boundary. -/
def resolveValidationCore (operand : CheckedDateRangesOverlapOperand model)
    (document : CheckedDocument model) (outer : Env)
    (world : Option World := none) (traversalMode : FilterTraversalMode := .dense) :
    Except CheckedAddressingError ResolvedDateRangeOverlapCore :=
  match operand with
  | .field source =>
      -- The reading row, not the document root: a nonrepeatable operand addresses identically at
      -- either, and an operand the rule's own iteration binds must be read at its row.
      .addressed <$> document.resolveCheckedDirectEntityOperandCoreAt outer source.declaration.id
  | .star path _ filter =>
      .addressed <$> path.resolveCheckedValidationEntityOperandCore (world := world) (traversalMode := traversalMode) document outer filter
  | .indexed selection _ => resolveSelectedOverlapCore selection document outer
  | .keyed selection _ => resolveKeyedOverlapCore selection document outer

end CheckedDateRangesOverlapOperand

/-- One singular direct fragment profile that resolves to an exact range without changing starred or plural admission. -/
inductive DirectDateRangeOverlapFragmentProfile where
  | year
  | yearMonth
  | month (baseYear : Int)
  | monthDay (baseYear : Int)
  deriving Repr, DecidableEq

namespace DirectDateRangeOverlapFragmentProfile

def accepts (profile : DirectDateRangeOverlapFragmentProfile)
    (model : FlatModel) (format : DateRangeInputFormat) : Bool :=
  match profile with
  | .year => format == .yearFragment
  | .yearMonth => format == .yearMonthFragment
  -- A profile is a component set, so both declared spellings of one set qualify once the
  -- Base Year has completed the value.
  | .month baseYear =>
      (format == .yearlessMonth || format == .yearlessMonthConcatenated) &&
        model.baseYear == some baseYear
  | .monthDay baseYear =>
      (format == .yearlessMonthDay || format == .yearlessDayMonthDotted) &&
        model.baseYear == some baseYear

end DirectDateRangeOverlapFragmentProfile

/-- One direct DateRange field whose checked input profile is year-bearing or completed by the checked model's Base Year. -/
structure CheckedDirectDateRangeOverlapFragmentField (model : FlatModel)
    extends CheckedDateRangeInputField where
  private mk ::
  profile : DirectDateRangeOverlapFragmentProfile
  profileOwned : profile.accepts model format = true

/-- One singular-overlap operand. Stored and selected fields gain the same supported fragment profiles; canonical fields and star operands retain their existing certificate. -/
inductive CheckedSingularDateRangesOverlapOperand (model : FlatModel) where
  | canonical (source : CheckedDateRangesOverlapOperand model)
  | fragmentField (source : CheckedDirectDateRangeOverlapFragmentField model)
  | indexedFragment (selection : CheckedSemanticIndexSource model)
      (source : CheckedDirectDateRangeOverlapFragmentField model)

namespace CheckedSingularDateRangesOverlapOperand

def hasHaving : CheckedSingularDateRangesOverlapOperand model → Bool
  | .canonical source => source.hasHaving
  | .fragmentField _ | .indexedFragment .. => false

/-- Whether the retained declaration satisfies the exact canonical policy or one field fragment profile valid for the checked model. -/
def policySupported : CheckedSingularDateRangesOverlapOperand model → Bool
  | .canonical source =>
      (DateRangeFormat.ofPolicy? source.source.policy).isSome
  | .fragmentField source | .indexedFragment _ source => source.profile.accepts model source.format

/-- The authored declaration behind a stored, selected or starred operand. -/
def declaration : CheckedSingularDateRangesOverlapOperand model → FlatFieldDecl
  | .canonical source => source.source.declaration
  | .fragmentField source | .indexedFragment _ source => source.declaration

/-- Resolve one singular full-validation operand through the existing checked direct/star addressing boundary. -/
def resolveValidationCore (operand : CheckedSingularDateRangesOverlapOperand model)
    (document : CheckedDocument model) (outer : Env)
    (world : Option World := none) (traversalMode : FilterTraversalMode := .dense) :
    Except CheckedAddressingError ResolvedDateRangeOverlapCore :=
  match operand with
  | .canonical source => source.resolveValidationCore (world := world) (traversalMode := traversalMode) document outer
  | .fragmentField source =>
      .addressed <$> document.resolveCheckedDirectEntityOperandCoreAt outer source.declaration.id
  | .indexedFragment selection _ => resolveSelectedOverlapCore selection document outer

end CheckedSingularDateRangesOverlapOperand

/-- A model-checked nonempty `DateRangesOverlap` operand list retaining the shared shape and exact authored filter slots. -/
structure CheckedDateRangesOverlapSource (model : FlatModel) where
  private mk ::
  shape : CheckedFieldEntityShape model
  first : CheckedSingularDateRangesOverlapOperand model
  rest : List (CheckedSingularDateRangesOverlapOperand model)

namespace CheckedDateRangesOverlapSource

def operands (checked : CheckedDateRangesOverlapSource model) :
    List (CheckedSingularDateRangesOverlapOperand model) :=
  checked.first :: checked.rest

def hasHaving (checked : CheckedDateRangesOverlapSource model) : Bool :=
  checked.operands.any CheckedSingularDateRangesOverlapOperand.hasHaving

end CheckedDateRangesOverlapSource

/-- Refuse a DateRange declaration that carries an `interpretationOfYear`, on either operand side of either overlap operator, under every profile including a year-bearing exact one, and with or without a Base Year. Bound extraction and comparison accept the same declaration, so this gate belongs to the overlap operators alone. -/
def refuseDateRangeOverlapYearInterpretation (declaration : FlatFieldDecl)
    (policy : DateRangeDeclarationPolicy) :
    Except DateRangesOverlapElabError Unit :=
  if policy.interpretationOfYear.isSome then
    throw (.yearInterpretationNotSupported declaration.path)
  else
    pure ()

/-- The first group carrier in a singular overlap list. The singular operator refuses every group
carrier, even one whose whole expansion is DateRange, ahead of its field walk and year question
([checkpoint](../../docs/sources/group-list-and-capacity-probes.md#src-overlap-field-walk-order)). -/
def firstDateRangesOverlapGroup? :
    List (ResolvedFieldEntityOperand model) → Option GroupPath :=
  List.findSome? fun
    | .group reference => some reference.path
    | .starredGroup source => some source.group.path
    | .starredGroupPresence source => some source.groupPath
    | .keyed source _ => match source.target with
        | .group path | .starredGroup path => some path
        | .star _ => none
    | .indexed _ _ | .field .. | .star .. | .starHaving .. => none

/-- Both overlap operators' field walk: every field the operands expand to, in authored order, must be
a DateRange declaration without a year interpretation. It completes before the format/year agreement gate over
the whole list, so an interpreted field is refused beside a year mix and a wrong kind ahead of one
draws the kind refusal
([checkpoint](../../docs/sources/group-list-and-capacity-probes.md#src-overlap-field-walk-order)).
A DateRange declaration with no policy passes and keeps its own certification. -/
def walkDateRangeOverlapFields (operands : List (ResolvedFieldEntityOperand model)) :
    Except DateRangesOverlapElabError Unit :=
  (expandedDeclarations operands).forM fun declaration =>
    match declaration.policy.kind, declaration.dateRangePolicy with
    | .dateRange, some policy => refuseDateRangeOverlapYearInterpretation declaration policy
    | .dateRange, none => pure ()
    | kind, _ => throw (.sourceNotDateRange declaration.path kind.surfaceKind)

/-- Apply the operator's two declaration-level gates in order: the canonical exact policy, then the
year-interpretation refusal. Every operand shape the operator admits — direct, starred, filtered, and
keyed — goes through this, so none can acquire a profile the others refuse. -/
def certifyDateRangesOverlapField (declaration : FlatFieldDecl) :
    Except DateRangesOverlapElabError CheckedCanonicalDateRangeField := do
  let checked ← (certifyCanonicalDateRangeField declaration).mapError fun
    | .notDateRange path actual => .sourceNotDateRange path actual.surfaceKind
    | .unsupportedPolicy path format separator =>
        .unsupportedPolicy path format separator
    | .incoherentCore => .incoherentCore
  refuseDateRangeOverlapYearInterpretation declaration checked.policy
  pure checked

/-- Certify one direct DateRange field whose profile is year-bearing on its own or completed by the model's Base Year. Shared with the plural operator, whose scalar and list sides accept the same profiles. -/
def certifyDirectDateRangeOverlapFragmentField (model : FlatModel)
    (declaration : FlatFieldDecl) : Except DateRangesOverlapElabError
      (CheckedDirectDateRangeOverlapFragmentField model) := do
  let source ← certifyDateRangeInputField declaration |>.mapError fun
    | .notDateRange path actual => .sourceNotDateRange path actual.surfaceKind
    | .unsupportedPolicy path format separator =>
        .unsupportedPolicy path format separator
    | .incoherentCore => .incoherentCore
  refuseDateRangeOverlapYearInterpretation declaration source.policy
  match hFormat : source.format with
  | .yearFragment =>
      pure {
        source with
        profile := .year
        profileOwned := by
          simp [DirectDateRangeOverlapFragmentProfile.accepts, hFormat] }
  | .yearMonthFragment =>
      pure {
        source with
        profile := .yearMonth
        profileOwned := by
          simp [DirectDateRangeOverlapFragmentProfile.accepts, hFormat] }
  | .yearlessMonth | .yearlessMonthConcatenated =>
      match hBaseYear : model.baseYear with
      | some baseYear => pure {
          source with
          profile := .month baseYear
          profileOwned := by
            simp [DirectDateRangeOverlapFragmentProfile.accepts, hFormat,
              hBaseYear] }
      | none => throw (.unsupportedPolicy declaration.path
          source.policy.format source.policy.separator)
  | .yearlessMonthDay | .yearlessDayMonthDotted =>
      match hBaseYear : model.baseYear with
      | some baseYear => pure {
          source with
          profile := .monthDay baseYear
          profileOwned := by
            simp [DirectDateRangeOverlapFragmentProfile.accepts, hFormat,
              hBaseYear] }
      | none => throw (.unsupportedPolicy declaration.path
          source.policy.format source.policy.separator)
  | .exact _ =>
      throw (.unsupportedPolicy declaration.path
        source.policy.format source.policy.separator)

/-- Certify one canonical direct, plain-star, or filter-bearing star DateRange operand. Shared with the plural operator, which applies the same canonical policy to its list side. -/
def certifyDateRangesOverlapOperand (model : FlatModel)
    (declaringGroup : GroupPath) (operand : ResolvedFieldEntityOperand model)
    (bindingGroup : GroupPath := declaringGroup) :
      Except DateRangesOverlapElabError
        (CheckedDateRangesOverlapOperand model) := match operand with
  | .indexed source _ => .indexed source <$> certifyDateRangesOverlapField source.targetDeclaration
  | .keyed source _ => match source.target with
      | .star path => .keyed source <$> certifyDateRangesOverlapField path.declaration
      | .group path | .starredGroup path => throw (.groupsNotAllowed path)
  | .field declaration .stored =>
      .field <$> certifyDateRangesOverlapField declaration
  | .field declaration form =>
      throw (.unsupportedReadForm declaration.path form)
  | .star path .stored => do
      pure (.star path (← certifyDateRangesOverlapField path.declaration) none)
  | .starHaving path authored .stored => do
      let source ← certifyDateRangesOverlapField path.declaration
      let filter ← elaborateStarHavingCore model declaringGroup path authored bindingGroup
        |>.mapError .having
      pure (.star path source (some filter.condition))
  | .star source form | .starHaving source _ form =>
      throw (.unsupportedReadForm source.declaration.path form)
  | .group reference => throw (.groupsNotAllowed reference.path)
  | .starredGroup source => throw (.groupsNotAllowed source.group.path)
  | .starredGroupPresence source => throw (.groupsNotAllowed source.groupPath)

/-- Certify direct and selected fields through the same declaration profile; starred operands keep
their canonical profile. The plural list reuses this contract (spec/07 §3). -/
def certifySingularDateRangesOverlapOperand (model : FlatModel)
    (declaringGroup : GroupPath) (operand : ResolvedFieldEntityOperand model)
    (bindingGroup : GroupPath := declaringGroup) :
      Except DateRangesOverlapElabError
        (CheckedSingularDateRangesOverlapOperand model) := match operand with
  | .indexed selection _ =>
      match certifyDateRangesOverlapField selection.targetDeclaration with
      | .ok source => pure (.canonical (.indexed selection source))
      | .error (.unsupportedPolicy _ _ _) =>
          .indexedFragment selection <$>
            certifyDirectDateRangeOverlapFragmentField model selection.targetDeclaration
      | .error error => throw error
  | .field declaration .stored =>
      match certifyDateRangesOverlapField declaration with
      | .ok source => pure (.canonical (.field source))
      | .error (.unsupportedPolicy _ _ _) =>
          .fragmentField <$>
            certifyDirectDateRangeOverlapFragmentField model declaration
      | .error error => throw error
  | operand =>
      .canonical <$> certifyDateRangesOverlapOperand model declaringGroup operand bindingGroup

private def certifySingularDateRangesOverlapOperands (model : FlatModel)
    (declaringGroup : GroupPath) (operands : List (ResolvedFieldEntityOperand model))
    (bindingGroup : GroupPath := declaringGroup) :
      Except DateRangesOverlapElabError
        (List (CheckedSingularDateRangesOverlapOperand model)) :=
  operands.mapM (fun operand => certifySingularDateRangesOverlapOperand model declaringGroup operand bindingGroup)

/-- Classify a certified single-field profile after Base-Year completion, as required by the
SemanticIndex pair certificates. Expansion-wide agreement is checked separately below. -/
def dateRangeProfileIncludesYear (model : FlatModel)
    (format : DateRangeInputFormat) : Bool :=
  format.includesYear || model.baseYear.isSome

/-- Preserve each authored reference's declaration expansion until format agreement is settled.
Missing local policy certificates remain with the subsequent policy-admission gate. -/
def dateRangeOverlapFormatAgreement (model : FlatModel)
    (operands : List (ResolvedFieldEntityOperand model)) : Bool :=
  dateRangeFormatAgreement model.hasBaseYear (operands.map fun operand =>
    operand.expansionDeclarations.filterMap fun declaration =>
      declaration.toDateRangeDeclarationPolicy?.map (·.format))

/-- Apply the shared shape gates first, then the singular operator's group refusal, the field walk, the format/year agreement gate, and exact-or-direct-fragment policy certification in authored order.

    `scope` is the reading rule's iteration scope, threaded to the shared shape resolver so an
    unstarred operand inside a level the rule iterates is admitted. Every other gate — arity,
    duplicates, overlap, the group refusal, the field walk, the format/year agreement rule, and per-operand
    policy — is unchanged and unaware of the scope. -/
def elaborateDateRangesOverlapSourceIn (model : FlatModel)
    (declaringGroup : GroupPath) (scope : List RepeatableLevel)
    (authored : SurfaceFieldEntitySource) (writtenGroup : GroupPath := declaringGroup)
    (fixedTargetGroup? : Option GroupPath := none) :
    Except DateRangesOverlapElabError
      (CheckedDateRangesOverlapSource model) := do
  let shape ← elaborateFieldEntityShapeIn model declaringGroup scope authored
      (fixedTargetGroup? := fixedTargetGroup?) (writtenGroup := writtenGroup) (categoryGate := .behindRootGate)
    |>.mapError .shape
  if let some path := firstDateRangesOverlapGroup? (shape.first :: shape.rest) then
    throw (.groupsNotAllowed path)
  walkDateRangeOverlapFields (shape.first :: shape.rest)
  if !dateRangeOverlapFormatAgreement model (shape.first :: shape.rest) then
    throw .dateWithAndWithoutYear
  let first ← certifySingularDateRangesOverlapOperand model declaringGroup
    shape.first (fixedTargetGroup?.getD declaringGroup)
  let rest ← certifySingularDateRangesOverlapOperands model declaringGroup
    shape.rest (fixedTargetGroup?.getD declaringGroup)
  pure { shape, first, rest }

/-- The scalar instance: a source read where the rule iterates no level. -/
def elaborateDateRangesOverlapSource (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceFieldEntitySource) :
    Except DateRangesOverlapElabError
      (CheckedDateRangesOverlapSource model) :=
  elaborateDateRangesOverlapSourceIn model declaringGroup [] authored

/-! ## Checked-document assembly -/

/-- Structural failure while projecting an admitted DateRange source from one immutable checked document. -/
inductive DateRangesOverlapEvaluationError where
  | addressing (error : CheckedAddressingError)
  | sourceValueKind (address : CellAddr)
  | sourceValueProfile (address : CellAddr) (value : DateRangeCellValue)
  | unresolvedRange (address : CellAddr) (value : DateRangeValue)
  | incoherentDirectOperand (actualCells : Nat)
  deriving Repr, DecidableEq

/-- Project this family's evaluation failure into the shared addressing channel a condition leaf
carries. The three payload classes name a stored value that contradicts its own certificate, which no
checked source can produce, and the incoherent-extent class names a direct operand that resolved to
other than one cell; all four report as the shared payload class at the offending address rather than
being dropped, so the standalone and leaf routes give one account of one certificate. -/
def DateRangesOverlapEvaluationError.toAddressing (fallback : CellAddr) :
    DateRangesOverlapEvaluationError → CheckedAddressingError
  | .addressing error => error
  | .sourceValueKind address | .sourceValueProfile address _
  | .unresolvedRange address _ => .operandPayload address
  | .incoherentDirectOperand _ => .operandPayload fallback

/-- One resolved operand retains exact source and addressing metadata beside its pure overlap input. -/
structure ResolvedCheckedDateRangesOverlapOperand (model : FlatModel) where
  private mk ::
  source : CheckedSingularDateRangesOverlapOperand model
  core : ResolvedDateRangeOverlapCore
  semantic : ResolvedDateRangeOperand

/-- Project one already-observed range into a kept-or-skipped overlap slot. Absence and formal
unavailability both skip the slot rather than contributing an interval, which is what makes an empty
operand suppress the predicate. Every read route shares this, so an addressed cell and a keyed
lookup cannot disagree about which slots participate. -/
def dateRangeOverlapSlotOf (address : CellAddr) :
    CellObservation DateRangeCellValue →
    Except DateRangesOverlapEvaluationError ResolvedDateRangeSlot
  | .empty | .unknown _ | .poison _ => .ok .skipped
  | .value (.exact value) =>
      match value.toResolvedDateRange? with
      | some range => .ok (.kept range)
      | none => .error (.unresolvedRange address value)
  | .value value => .error (.sourceValueProfile address value)

/-- Project one addressed cell into a kept-or-skipped overlap slot. Shared with the plural operator, whose scalar and group operands read cells through the same validation-phase observation. -/
def checkedDateRangeSlot
    (addressed : CheckedAddressedCell) :
    Except DateRangesOverlapEvaluationError ResolvedDateRangeSlot :=
  match CheckedDateRangeSource.projectRange addressed.address.field
      (observeCell .validation addressed.cell) with
  -- The projection's only failure is a payload that is not a DateRange at all.
  | .error _ => .error (.sourceValueKind addressed.address)
  | .ok observed => dateRangeOverlapSlotOf addressed.address observed

/-- Project one resolved operand core into the pure overlap operand, carrying its filter provenance. Shared with the plural operator's list side. -/
def checkedDateRangeOperandSemantic
    (core : ResolvedDateRangeOverlapCore) :
    Except DateRangesOverlapEvaluationError ResolvedDateRangeOperand := do
  match core with
  | .addressed core =>
      let slots ← core.addressedCells.mapM checkedDateRangeSlot
      pure { slots, hasFilter := core.hasHaving }
  | .selected (.value cells) =>
      pure { slots := ← cells.mapM checkedDateRangeSlot, hasFilter := false }
  | .selected (.empty) | .selected (.unknown _) | .selected (.poison _) =>
      pure { slots := [.skipped], hasFilter := false }

namespace CheckedSingularDateRangesOverlapOperand

/-- Resolve and project one admitted operand without discarding authored identity, concrete addresses, topology, or filter provenance. -/
def resolveCheckedValidation
    (source : CheckedSingularDateRangesOverlapOperand model)
    (document : CheckedDocument model) (outer : Env)
    (world : Option World := none) :
    Except DateRangesOverlapEvaluationError
      (ResolvedCheckedDateRangesOverlapOperand model) := do
  let core ← (source.resolveValidationCore (world := world) document outer).mapError .addressing
  let semantic ← checkedDateRangeOperandSemantic core
  pure { source, core, semantic }

end CheckedSingularDateRangesOverlapOperand

/-- Rich resolved singular-overlap query result. Its verdict is derived from, rather than stored beside, the occurrence-preserving semantic operands. -/
structure CheckedDateRangesOverlapResult (model : FlatModel) where
  private mk ::
  operands : List (ResolvedCheckedDateRangesOverlapOperand model)

namespace CheckedDateRangesOverlapResult

/-- Evaluate the established pure any-pair scan over the resolved checked operands. -/
def verdict (result : CheckedDateRangesOverlapResult model) : Verdict :=
  evalDateRangesOverlap (result.operands.map fun operand => operand.semantic)

end CheckedDateRangesOverlapResult

namespace CheckedDateRangesOverlapSource

/-- Resolve every authored singular-overlap operand against the same checked document in authored order, then expose the established pure verdict. -/
def evaluateCheckedDocument
    (checked : CheckedDateRangesOverlapSource model)
    (document : CheckedDocument model) (outer : Env)
    (world : Option World := none) :
    Except DateRangesOverlapEvaluationError
      (CheckedDateRangesOverlapResult model) := do
  let operands ← checked.operands.mapM fun source =>
    source.resolveCheckedValidation (world := world) document outer
  pure { operands }

end CheckedDateRangesOverlapSource

end A12Kernel
