import A12Kernel.Elaboration.CheckedStarDocument
import A12Kernel.Elaboration.DateRangeInput
import A12Kernel.Elaboration.FieldEntityList
import A12Kernel.Semantics.DateRangeOverlapOperators

/-! # Checked DateRange overlap operands

This boundary owns operator-specific static admission and full-validation checked-document assembly for DateRange overlap conditions. It reuses the shared entity-list shape and checked DateRange declaration policies; singular direct fields additionally certify measured year-month and Base-Year-completed fragment profiles while starred and plural routes remain canonical. Pure overlap truth and polarity remain in `A12Kernel.Semantics.DateRangeOverlapOperators`.
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
  | having (error : CorrelationElabError)
  | incoherentCore
  deriving Repr, DecidableEq

namespace DateRangesOverlapElabError

def diagnostic? : DateRangesOverlapElabError → Option KernelStaticDiagnostic
  | .shape error => error.diagnostic?
  | .groupsNotAllowed _ => some .noGroupsAllowed
  | .dateWithAndWithoutYear => some .dateWithAndWithoutYear
  | .sourceNotDateRange _ _ | .unsupportedPolicy _ _ _ |
      .unsupportedReadForm _ _ | .having _ | .incoherentCore => none

end DateRangesOverlapElabError

/-- One certified canonical direct, plain-star, or filter-bearing star DateRange operand. -/
inductive CheckedDateRangesOverlapOperand (model : FlatModel) where
  | field (source : CheckedCanonicalDateRangeField)
  | star (path : CheckedStarFieldPath model)
      (source : CheckedCanonicalDateRangeField)
      (filter : Option CorrelatedHaving)

namespace CheckedDateRangesOverlapOperand

def source : CheckedDateRangesOverlapOperand model →
    CheckedCanonicalDateRangeField
  | .field source | .star _ source _ => source

def hasHaving : CheckedDateRangesOverlapOperand model → Bool
  | .field _ | .star _ _ none => false
  | .star _ _ (some _) => true

/-- Resolve one full-validation operand through the shared checked direct/star addressing and filter boundary. -/
def resolveValidationCore (operand : CheckedDateRangesOverlapOperand model)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError ResolvedCheckedEntityOperandCore :=
  match operand with
  | .field source =>
      document.resolveCheckedDirectEntityOperandCore source.declaration.id
  | .star path _ filter =>
      path.resolveCheckedValidationEntityOperandCore document outer filter

end CheckedDateRangesOverlapOperand

/-- One singular direct fragment profile that resolves to an exact range without changing starred or plural admission. -/
inductive DirectDateRangeOverlapFragmentProfile where
  | yearMonth
  | month (baseYear : Int)
  | monthDay (baseYear : Int)
  deriving Repr, DecidableEq

namespace DirectDateRangeOverlapFragmentProfile

def accepts (profile : DirectDateRangeOverlapFragmentProfile)
    (model : FlatModel) (format : DateRangeInputFormat) : Bool :=
  match profile with
  | .yearMonth => format == .yearMonthFragment
  | .month baseYear =>
      format == .yearlessMonth && model.baseYear == some baseYear
  | .monthDay baseYear =>
      format == .yearlessMonthDay && model.baseYear == some baseYear

end DirectDateRangeOverlapFragmentProfile

/-- One direct DateRange field whose checked input profile is year-bearing or completed by the checked model's Base Year. -/
structure CheckedDirectDateRangeOverlapFragmentField (model : FlatModel)
    extends CheckedDateRangeInputField where
  private mk ::
  profile : DirectDateRangeOverlapFragmentProfile
  profileOwned : profile.accepts model format = true

/-- One singular-overlap operand. Only a direct field gains the measured fragment profiles; canonical direct and star operands retain their existing certificate. -/
inductive CheckedSingularDateRangesOverlapOperand (model : FlatModel) where
  | canonical (source : CheckedDateRangesOverlapOperand model)
  | fragmentField (source : CheckedDirectDateRangeOverlapFragmentField model)

namespace CheckedSingularDateRangesOverlapOperand

def hasHaving : CheckedSingularDateRangesOverlapOperand model → Bool
  | .canonical source => source.hasHaving
  | .fragmentField _ => false

/-- Whether the retained declaration satisfies the exact canonical policy or one singular-only direct fragment profile valid for the checked model. -/
def policySupported : CheckedSingularDateRangesOverlapOperand model → Bool
  | .canonical source =>
      (DateRangeFormat.ofPolicy? source.source.policy).isSome
  | .fragmentField source => source.profile.accepts model source.format

/-- Resolve one singular full-validation operand through the existing checked direct/star addressing boundary. -/
def resolveValidationCore (operand : CheckedSingularDateRangesOverlapOperand model)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError ResolvedCheckedEntityOperandCore :=
  match operand with
  | .canonical source => source.resolveValidationCore document outer
  | .fragmentField source =>
      document.resolveCheckedDirectEntityOperandCore source.declaration.id

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

private def certifyDateRangesOverlapField (declaration : FlatFieldDecl) :
    Except DateRangesOverlapElabError CheckedCanonicalDateRangeField :=
  (certifyCanonicalDateRangeField declaration).mapError fun
    | .notDateRange path actual => .sourceNotDateRange path actual.surfaceKind
    | .unsupportedPolicy path format separator =>
        .unsupportedPolicy path format separator
    | .incoherentCore => .incoherentCore

private def certifyDirectDateRangeOverlapFragmentField (model : FlatModel)
    (declaration : FlatFieldDecl) : Except DateRangesOverlapElabError
      (CheckedDirectDateRangeOverlapFragmentField model) := do
  let source ← certifyDateRangeInputField declaration |>.mapError fun
    | .notDateRange path actual => .sourceNotDateRange path actual.surfaceKind
    | .unsupportedPolicy path format separator =>
        .unsupportedPolicy path format separator
    | .incoherentCore => .incoherentCore
  match hFormat : source.format with
  | .yearMonthFragment =>
      pure {
        source with
        profile := .yearMonth
        profileOwned := by
          simp [DirectDateRangeOverlapFragmentProfile.accepts, hFormat] }
  | .yearlessMonth =>
      match hBaseYear : model.baseYear with
      | some baseYear => pure {
          source with
          profile := .month baseYear
          profileOwned := by
            simp [DirectDateRangeOverlapFragmentProfile.accepts, hFormat,
              hBaseYear] }
      | none => throw (.unsupportedPolicy declaration.path
          source.policy.format source.policy.separator)
  | .yearlessMonthDay =>
      match hBaseYear : model.baseYear with
      | some baseYear => pure {
          source with
          profile := .monthDay baseYear
          profileOwned := by
            simp [DirectDateRangeOverlapFragmentProfile.accepts, hFormat,
              hBaseYear] }
      | none => throw (.unsupportedPolicy declaration.path
          source.policy.format source.policy.separator)
  | .exact _ | .yearFragment =>
      throw (.unsupportedPolicy declaration.path
        source.policy.format source.policy.separator)

private def certifyDateRangesOverlapOperand (model : FlatModel)
    (declaringGroup : GroupPath) : ResolvedFieldEntityOperand model →
      Except DateRangesOverlapElabError
        (CheckedDateRangesOverlapOperand model)
  | .field declaration .stored =>
      .field <$> certifyDateRangesOverlapField declaration
  | .field declaration form =>
      throw (.unsupportedReadForm declaration.path form)
  | .star path => do
      pure (.star path (← certifyDateRangesOverlapField path.declaration) none)
  | .starHaving path authored => do
      let source ← certifyDateRangesOverlapField path.declaration
      let filter ← elaborateStarHavingCore model declaringGroup path authored
        |>.mapError .having
      pure (.star path source (some filter.condition))
  | .group reference => throw (.groupsNotAllowed reference.path)
  | .starredGroup source => throw (.groupsNotAllowed source.group.path)
  | .starredGroupPresence source => throw (.groupsNotAllowed source.groupPath)

private def certifySingularDateRangesOverlapOperand (model : FlatModel)
    (declaringGroup : GroupPath) : ResolvedFieldEntityOperand model →
      Except DateRangesOverlapElabError
        (CheckedSingularDateRangesOverlapOperand model)
  | .field declaration .stored =>
      match certifyDateRangesOverlapField declaration with
      | .ok source => pure (.canonical (.field source))
      | .error (.unsupportedPolicy _ _ _) =>
          .fragmentField <$>
            certifyDirectDateRangeOverlapFragmentField model declaration
      | .error error => throw error
  | operand =>
      .canonical <$> certifyDateRangesOverlapOperand model declaringGroup operand

private def certifySingularDateRangesOverlapOperands (model : FlatModel)
    (declaringGroup : GroupPath) : List (ResolvedFieldEntityOperand model) →
      Except DateRangesOverlapElabError
        (List (CheckedSingularDateRangesOverlapOperand model)) :=
  List.mapM (certifySingularDateRangesOverlapOperand model declaringGroup)

private def isCanonicalDirectDateRangeOperand :
    ResolvedFieldEntityOperand model → Bool
  | .field declaration .stored =>
      (certifyCanonicalDateRangeField declaration).toOption.isSome
  | _ => false

private def isYearlessDirectDateRangeOperand :
    ResolvedFieldEntityOperand model → Bool
  | .field declaration .stored =>
      match (certifyDateRangeInputField declaration).toOption.map (·.format) with
      | some format =>
          match format with
          | .yearlessMonth | .yearlessMonthDay => true
          | _ => false
      | none => false
  | _ => false

/-- The retained diagnostic row is exactly one canonical direct range beside one unconfigured yearless direct range. -/
private def hasMeasuredYearlessDateRangeMix (model : FlatModel)
    (operands : List (ResolvedFieldEntityOperand model)) : Bool :=
  if model.baseYear.isSome then
    false
  else
    match operands with
    | [left, right] =>
        (isCanonicalDirectDateRangeOperand left &&
          isYearlessDirectDateRangeOperand right) ||
        (isYearlessDirectDateRangeOperand left &&
          isCanonicalDirectDateRangeOperand right)
    | _ => false

/-- Apply the shared shape gates first, then the singular operator's group refusal and exact-or-direct-fragment policy certification in authored order. -/
def elaborateDateRangesOverlapSource (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceFieldEntitySource) :
    Except DateRangesOverlapElabError
      (CheckedDateRangesOverlapSource model) := do
  let shape ← elaborateFieldEntityShape model declaringGroup authored
    |>.mapError .shape
  if hasMeasuredYearlessDateRangeMix model (shape.first :: shape.rest) then
    throw .dateWithAndWithoutYear
  let first ← certifySingularDateRangesOverlapOperand model declaringGroup
    shape.first
  let rest ← certifySingularDateRangesOverlapOperands model declaringGroup
    shape.rest
  pure { shape, first, rest }

/-! ## Checked `AtLeastOneDateRangeOverlaps` source admission -/

inductive DateRangeOverlapSourceRole where
  | scalar
  | list
  deriving Repr, DecidableEq

/-- Static refusal while certifying the plural scalar-versus-list DateRange overlap source. -/
inductive AtLeastOneDateRangeOverlapsElabError where
  | shape (error : FieldEntityShapeElabError)
  | scalarStarred (path : List String)
  | scalarFilteredStarred (path : List String)
  | scalarGroup (path : GroupPath)
  | measuredNumberPairNotDateRange (scalarPath listPath : List String)
  | sourceNotDateRange (role : DateRangeOverlapSourceRole)
      (path : List String) (actual : SurfaceScalarKind)
  | unsupportedPolicy (role : DateRangeOverlapSourceRole)
      (path : List String) (format separator : String)
  | unsupportedReadForm (role : DateRangeOverlapSourceRole)
      (path : List String) (form : FieldEntityReadForm)
  | groupExpansionEmpty (path : GroupPath)
  | groupExpansionNotDateRange (path : GroupPath)
  | having (error : CorrelationElabError)
  | incoherentCore
  deriving Repr, DecidableEq

namespace AtLeastOneDateRangeOverlapsElabError

/-- Project only the two exact operator-specific diagnostic rows plus the shared shape classes. Every other local refusal remains deliberately unmapped. -/
def diagnostic? : AtLeastOneDateRangeOverlapsElabError →
    Option KernelStaticDiagnostic
  | .shape error => error.diagnostic?
  | .scalarStarred _ => some .invalidParameterForDateRangeComparison
  | .measuredNumberPairNotDateRange _ _ => some .noDateRange
  | .scalarFilteredStarred _ | .scalarGroup _ |
      .sourceNotDateRange _ _ _ | .unsupportedPolicy _ _ _ _ |
      .unsupportedReadForm _ _ _ | .groupExpansionEmpty _ |
      .groupExpansionNotDateRange _ | .having _ | .incoherentCore => none

end AtLeastOneDateRangeOverlapsElabError

/-- One group-scope list slot whose complete recursive expansion is nonempty and uses the supported DateRange policies. -/
structure CheckedDateRangeEntityGroup (model : FlatModel) where
  source : CheckedEntityGroupSource model
  first : CheckedCanonicalDateRangeField
  rest : List CheckedCanonicalDateRangeField
  expansionOwned :
    (model.groupSubtreeFields source.groupPath).filterMap
      (fun declaration => (certifyCanonicalDateRangeField declaration).toOption) =
        first :: rest
  expansionAllDateRange :
    (model.groupSubtreeFields source.groupPath).all
      (fun declaration =>
        (certifyCanonicalDateRangeField declaration).toOption.isSome) = true

/-- One certified list-side field, star, or recursively expanded group operand. -/
inductive CheckedAtLeastOneDateRangeOverlapsListOperand (model : FlatModel) where
  | field (source : CheckedDateRangesOverlapOperand model)
  | group (source : CheckedDateRangeEntityGroup model)

namespace CheckedAtLeastOneDateRangeOverlapsListOperand

def hasHaving : CheckedAtLeastOneDateRangeOverlapsListOperand model → Bool
  | .field source => source.hasHaving
  | .group _ => false

def fields : CheckedAtLeastOneDateRangeOverlapsListOperand model →
    List CheckedCanonicalDateRangeField
  | .field source => [source.source]
  | .group source => source.first :: source.rest

end CheckedAtLeastOneDateRangeOverlapsListOperand

/-- Parser-independent scalar-versus-list source. The scalar retains the broad entity spelling long enough to project the measured starred-scalar diagnostic; checked construction narrows it to one direct field. -/
structure SurfaceAtLeastOneDateRangeOverlapsSource where
  scalar : SurfaceFieldEntityOperand
  list : SurfaceFieldEntitySource
  deriving Repr, DecidableEq

/-- A model-checked scalar-versus-list source. The shared shape spans both sides, so exact duplication or overlap between the scalar and any list operand is rejected once. -/
structure CheckedAtLeastOneDateRangeOverlapsSource (model : FlatModel) where
  private mk ::
  shape : CheckedFieldEntityShape model
  scalar : CheckedCanonicalDateRangeField
  first : CheckedAtLeastOneDateRangeOverlapsListOperand model
  rest : List (CheckedAtLeastOneDateRangeOverlapsListOperand model)

namespace CheckedAtLeastOneDateRangeOverlapsSource

def operands (checked : CheckedAtLeastOneDateRangeOverlapsSource model) :
    List (CheckedAtLeastOneDateRangeOverlapsListOperand model) :=
  checked.first :: checked.rest

def hasHaving (checked : CheckedAtLeastOneDateRangeOverlapsSource model) : Bool :=
  checked.operands.any CheckedAtLeastOneDateRangeOverlapsListOperand.hasHaving

end CheckedAtLeastOneDateRangeOverlapsSource

private def certifyPluralDateRangeField (role : DateRangeOverlapSourceRole)
    (declaration : FlatFieldDecl) :
    Except AtLeastOneDateRangeOverlapsElabError
      CheckedCanonicalDateRangeField :=
  (certifyCanonicalDateRangeField declaration).mapError fun
    | .notDateRange path actual =>
        .sourceNotDateRange role path actual.surfaceKind
    | .unsupportedPolicy path format separator =>
        .unsupportedPolicy role path format separator
    | .incoherentCore => .incoherentCore

private def certifyAtLeastOneDateRangeOverlapScalarShape :
    ResolvedFieldEntityOperand model →
      Except AtLeastOneDateRangeOverlapsElabError
        FlatFieldDecl
  | .field declaration .stored => pure declaration
  | .field declaration form =>
      throw (.unsupportedReadForm .scalar declaration.path form)
  | .star source => throw (.scalarStarred source.declaration.path)
  | .starHaving source _ =>
      throw (.scalarFilteredStarred source.declaration.path)
  | .group reference => throw (.scalarGroup reference.path)
  | .starredGroup source => throw (.scalarGroup source.group.path)
  | .starredGroupPresence source => throw (.scalarGroup source.groupPath)

private def certifyDateRangeEntityGroup (model : FlatModel)
    (source : CheckedEntityGroupSource model) :
    Except AtLeastOneDateRangeOverlapsElabError
      (CheckedDateRangeEntityGroup model) :=
  if hAll : (model.groupSubtreeFields source.groupPath).all
      (fun declaration =>
        (certifyCanonicalDateRangeField declaration).toOption.isSome) = true then
    match hOwned : (model.groupSubtreeFields source.groupPath).filterMap
        (fun declaration =>
          (certifyCanonicalDateRangeField declaration).toOption) with
    | [] => throw (.groupExpansionEmpty source.groupPath)
    | first :: rest => pure {
        source
        first
        rest
        expansionOwned := hOwned
        expansionAllDateRange := hAll }
  else
    throw (.groupExpansionNotDateRange source.groupPath)

private def pluralListError : DateRangesOverlapElabError →
    AtLeastOneDateRangeOverlapsElabError
  | .sourceNotDateRange path actual => .sourceNotDateRange .list path actual
  | .unsupportedPolicy path format separator =>
      .unsupportedPolicy .list path format separator
  | .unsupportedReadForm path form => .unsupportedReadForm .list path form
  | .having error => .having error
  | .shape _ | .groupsNotAllowed _ | .dateWithAndWithoutYear |
      .incoherentCore => .incoherentCore

private def certifyAtLeastOneDateRangeOverlapsListOperand (model : FlatModel)
    (declaringGroup : GroupPath) : ResolvedFieldEntityOperand model →
      Except AtLeastOneDateRangeOverlapsElabError
        (CheckedAtLeastOneDateRangeOverlapsListOperand model)
  | .group reference =>
      .group <$> certifyDateRangeEntityGroup model (.fixed reference)
  | .starredGroup source =>
      .group <$> certifyDateRangeEntityGroup model (.starred source)
  | .starredGroupPresence source =>
      .group <$> certifyDateRangeEntityGroup model (.starredPresence source)
  | operand =>
      .field <$> (certifyDateRangesOverlapOperand model declaringGroup operand
        |>.mapError pluralListError)

private def certifyAtLeastOneDateRangeOverlapsListOperands (model : FlatModel)
    (declaringGroup : GroupPath) : List (ResolvedFieldEntityOperand model) →
      Except AtLeastOneDateRangeOverlapsElabError
        (List (CheckedAtLeastOneDateRangeOverlapsListOperand model)) :=
  List.mapM (certifyAtLeastOneDateRangeOverlapsListOperand model declaringGroup)

/-- Resolve and gate the scalar shape before reading the list, then resolve both sides as one nonempty entity sequence so cross-side duplicate and overlap checks remain shared. Finally certify the supported DateRange policies. -/
def elaborateAtLeastOneDateRangeOverlapsSource (model : FlatModel)
    (declaringGroup : GroupPath)
    (authored : SurfaceAtLeastOneDateRangeOverlapsSource) :
    Except AtLeastOneDateRangeOverlapsElabError
      (CheckedAtLeastOneDateRangeOverlapsSource model) :=
  match model.validate with
  | .error error => .error (.shape (.resolve error))
  | .ok () => do
      let scalarDeclaration ←
        resolveFieldEntityOperandUnchecked model declaringGroup authored.scalar
          |>.mapError .shape
          |>.bind certifyAtLeastOneDateRangeOverlapScalarShape
      let shape ← elaborateFieldEntityShape model declaringGroup {
          first := authored.scalar
          rest := authored.list.first :: authored.list.rest
        } |>.mapError .shape
      match shape.rest with
      | [] => throw .incoherentCore
      | listFirst :: listRest => do
          match listFirst, listRest with
          | .field listed .stored, [] =>
              if scalarDeclaration.policy.kind.surfaceKind == .number &&
                  listed.policy.kind.surfaceKind == .number then
                throw (.measuredNumberPairNotDateRange
                  scalarDeclaration.path listed.path)
          | _, _ => pure ()
          let scalar ←
            certifyPluralDateRangeField .scalar scalarDeclaration
          let first ← certifyAtLeastOneDateRangeOverlapsListOperand model
            declaringGroup listFirst
          let rest ← certifyAtLeastOneDateRangeOverlapsListOperands model
            declaringGroup listRest
          pure { shape, scalar, first, rest }

/-! ## Checked-document assembly -/

/-- Structural failure while projecting an admitted DateRange source from one immutable checked document. -/
inductive DateRangesOverlapEvaluationError where
  | addressing (error : CheckedAddressingError)
  | sourceValueKind (address : CellAddr)
  | sourceValueProfile (address : CellAddr) (value : DateRangeCellValue)
  | unresolvedRange (address : CellAddr) (value : DateRangeValue)
  | incoherentDirectOperand (actualCells : Nat)
  deriving Repr, DecidableEq

/-- One resolved operand retains exact source and addressing metadata beside its pure overlap input. -/
structure ResolvedCheckedDateRangesOverlapOperand (model : FlatModel) where
  private mk ::
  source : CheckedSingularDateRangesOverlapOperand model
  core : ResolvedCheckedEntityOperandCore
  semantic : ResolvedDateRangeOperand

private def checkedDateRangeSlot
    (addressed : CheckedAddressedCell) :
    Except DateRangesOverlapEvaluationError ResolvedDateRangeSlot :=
  match observeCell .validation addressed.cell with
  | .empty | .unknown _ | .poison _ => pure .skipped
  | .value (Value.dateRange (.exact value)) =>
      match value.toResolvedDateRange? with
      | some range => pure (.kept range)
      | none => throw (.unresolvedRange addressed.address value)
  | .value (Value.dateRange value) =>
      throw (.sourceValueProfile addressed.address value)
  | .value _ => throw (.sourceValueKind addressed.address)

private def checkedDateRangeOperandSemantic
    (core : ResolvedCheckedEntityOperandCore) :
    Except DateRangesOverlapEvaluationError ResolvedDateRangeOperand := do
  let slots ← core.addressedCells.mapM checkedDateRangeSlot
  pure { slots, hasFilter := core.hasHaving }

namespace CheckedSingularDateRangesOverlapOperand

/-- Resolve and project one admitted operand without discarding authored identity, concrete addresses, topology, or filter provenance. -/
def resolveCheckedValidation
    (source : CheckedSingularDateRangesOverlapOperand model)
    (document : CheckedDocument model) (outer : Env) :
    Except DateRangesOverlapEvaluationError
      (ResolvedCheckedDateRangesOverlapOperand model) := do
  let core ← (source.resolveValidationCore document outer).mapError .addressing
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
    (document : CheckedDocument model) (outer : Env) :
    Except DateRangesOverlapEvaluationError
      (CheckedDateRangesOverlapResult model) := do
  let operands ← checked.operands.mapM fun source =>
    source.resolveCheckedValidation document outer
  pure { operands }

end CheckedDateRangesOverlapSource

/-! ## Checked plural-overlap assembly -/

/-- The separately resolved scalar retains its checked declaration and concrete addressed cell beside the pure scalar slot. -/
structure ResolvedCheckedAtLeastOneDateRangeOverlapScalar
    (model : FlatModel) where
  private mk ::
  source : CheckedCanonicalDateRangeField
  core : ResolvedCheckedEntityOperandCore
  semantic : ResolvedDateRangeSlot

/-- One resolved list operand retains its authored field/group boundary and complete addressed extent beside the pure scan input. -/
structure ResolvedCheckedAtLeastOneDateRangeOverlapListOperand
    (model : FlatModel) where
  private mk ::
  source : CheckedAtLeastOneDateRangeOverlapsListOperand model
  core : ResolvedCheckedEntityOperandCore
  semantic : ResolvedDateRangeOperand

private def resolveCheckedAtLeastOneDateRangeOverlapScalar
    (source : CheckedCanonicalDateRangeField)
    (document : CheckedDocument model) :
    Except DateRangesOverlapEvaluationError
      (ResolvedCheckedAtLeastOneDateRangeOverlapScalar model) := do
  let core ←
    (document.resolveCheckedDirectEntityOperandCore source.declaration.id)
      |>.mapError .addressing
  match core.addressedCells with
  | [addressed] => do
      let semantic ← checkedDateRangeSlot addressed
      pure { source, core, semantic }
  | addressed => throw (.incoherentDirectOperand addressed.length)

namespace CheckedAtLeastOneDateRangeOverlapsListOperand

/-- Resolve one admitted list operand without erasing its authored field/group boundary, filter provenance, or checked group extent. -/
def resolveCheckedValidation
    (source : CheckedAtLeastOneDateRangeOverlapsListOperand model)
    (document : CheckedDocument model) (outer : Env) :
    Except DateRangesOverlapEvaluationError
      (ResolvedCheckedAtLeastOneDateRangeOverlapListOperand model) :=
  match source with
  | .field fieldSource => do
      let core ← (fieldSource.resolveValidationCore document outer)
        |>.mapError .addressing
      let semantic ← checkedDateRangeOperandSemantic core
      pure {
        source := .field fieldSource
        core
        semantic }
  | .group groupSource => do
      let declarations :=
        (groupSource.first :: groupSource.rest).map (·.declaration)
      let core ← document.resolveCheckedGroupEntityOperandCore outer
        groupSource.source.boundLevelCount declarations
        |>.mapError .addressing
      let slots ← core.addressedCells.mapM checkedDateRangeSlot
      pure {
        source := .group groupSource
        core
        semantic := { slots, hasFilter := false } }

end CheckedAtLeastOneDateRangeOverlapsListOperand

/-- Rich resolved plural-overlap query result. The checked source keeps every authored list boundary even when an empty `operands` list records scalar-first termination; reached operands remain in authored order. -/
structure CheckedAtLeastOneDateRangeOverlapsResult (model : FlatModel) where
  private mk ::
  source : CheckedAtLeastOneDateRangeOverlapsSource model
  scalar : ResolvedCheckedAtLeastOneDateRangeOverlapScalar model
  operands : List (ResolvedCheckedAtLeastOneDateRangeOverlapListOperand model)

namespace CheckedAtLeastOneDateRangeOverlapsResult

/-- Evaluate the established scalar-versus-list scan over the resolved checked source. -/
def verdict (result : CheckedAtLeastOneDateRangeOverlapsResult model) : Verdict :=
  evalAtLeastOneDateRangeOverlaps result.scalar.semantic
    (result.operands.map (·.semantic))

end CheckedAtLeastOneDateRangeOverlapsResult

namespace CheckedAtLeastOneDateRangeOverlapsSource

private def resolveUntilFirstOverlap
    (scalar : ResolvedDateRangeSlot)
    (document : CheckedDocument model) (outer : Env) :
    List (CheckedAtLeastOneDateRangeOverlapsListOperand model) →
      Except DateRangesOverlapEvaluationError
        (List (ResolvedCheckedAtLeastOneDateRangeOverlapListOperand model))
  | [] => pure []
  | source :: remaining => do
      let resolved ← source.resolveCheckedValidation document outer
      match evalAtLeastOneDateRangeOverlaps scalar [resolved.semantic] with
      | .fired _ => pure [resolved]
      | _ => pure (resolved ::
          (← resolveUntilFirstOverlap scalar document outer remaining))

/-- Resolve the scalar first, then resolve authored list operands against the same immutable checked document only through the first overlap. -/
def evaluateCheckedDocument
    (checked : CheckedAtLeastOneDateRangeOverlapsSource model)
    (document : CheckedDocument model) (outer : Env) :
    Except DateRangesOverlapEvaluationError
      (CheckedAtLeastOneDateRangeOverlapsResult model) := do
  let scalar ←
    resolveCheckedAtLeastOneDateRangeOverlapScalar checked.scalar document
  match scalar.semantic with
  | .skipped => pure { source := checked, scalar, operands := [] }
  | .kept _ => do
      let operands ←
        resolveUntilFirstOverlap scalar.semantic document outer checked.operands
      pure { source := checked, scalar, operands }

end CheckedAtLeastOneDateRangeOverlapsSource

end A12Kernel
