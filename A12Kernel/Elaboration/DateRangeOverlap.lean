import A12Kernel.Elaboration.CheckedStarDocument
import A12Kernel.Elaboration.DateRangeInput
import A12Kernel.Elaboration.FieldEntityList
import A12Kernel.Semantics.DateRangeOverlapOperators

/-! # Checked DateRange overlap operands

This boundary owns static admission and full-validation checked-document assembly for the any-pair singular `DateRangesOverlap` operator, plus the certification steps and uniform-year gate its plural sibling in `A12Kernel.Elaboration.AtLeastOneDateRangeOverlap` reuses. It reuses the shared entity-list shape and checked DateRange declaration policies; singular direct fields additionally certify the internally supported year fragment plus measured year-month and Base-Year-completed fragment profiles while starred and plural routes remain canonical. Every operand list first passes the Kernel's uniform-year gate, which is decided by the declarations and the model's Base Year alone. Pure overlap truth and polarity remain in `A12Kernel.Semantics.DateRangeOverlapOperators`.
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

/-- One singular-overlap operand. Only a direct field gains the supported fragment profiles; canonical direct and star operands retain their existing certificate. -/
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

/-- Whether one operand's compared value carries a year: either its declaration does, or the model's Base Year completes a yearless declaration into an exact range. `none` is an operand shape whose declaration this boundary does not read, which keeps its own certification instead of being guessed at either way. -/
def dateRangeOperandIncludesYear? (model : FlatModel) :
    ResolvedFieldEntityOperand model → Option Bool
  | .field declaration .stored =>
      (certifyDateRangeInputField declaration).toOption.map fun checked =>
        checked.format.includesYear || model.baseYear.isSome
  | _ => none

/-- The Kernel's uniform-year gate over a whole overlap operand list: every compared range must include the year, or none may. It is a property of the list rather than of a distinguished pair, so it reaches lists longer than two and every declared spelling of a component set. A configured Base Year makes each yearless declaration year-bearing, so a configured model never mixes. -/
def mixesDateRangeYearInclusion (model : FlatModel)
    (operands : List (ResolvedFieldEntityOperand model)) : Bool :=
  let inclusions := operands.filterMap (dateRangeOperandIncludesYear? model)
  inclusions.contains true && inclusions.contains false

/-- Apply the shared shape gates first, then the singular operator's group refusal and exact-or-direct-fragment policy certification in authored order. -/
def elaborateDateRangesOverlapSource (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceFieldEntitySource) :
    Except DateRangesOverlapElabError
      (CheckedDateRangesOverlapSource model) := do
  let shape ← elaborateFieldEntityShape model declaringGroup authored
    |>.mapError .shape
  if mixesDateRangeYearInclusion model (shape.first :: shape.rest) then
    throw .dateWithAndWithoutYear
  let first ← certifySingularDateRangesOverlapOperand model declaringGroup
    shape.first
  let rest ← certifySingularDateRangesOverlapOperands model declaringGroup
    shape.rest
  pure { shape, first, rest }

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

/-- Project one addressed cell into a kept-or-skipped overlap slot. Shared with the plural operator, whose scalar and group operands read cells through the same validation-phase observation. -/
def checkedDateRangeSlot
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

/-- Project one resolved operand core into the pure overlap operand, carrying its filter provenance. Shared with the plural operator's list side. -/
def checkedDateRangeOperandSemantic
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

end A12Kernel
