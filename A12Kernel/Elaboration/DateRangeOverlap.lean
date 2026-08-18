import A12Kernel.Elaboration.CheckedStarDocument
import A12Kernel.Elaboration.DateRangeInput
import A12Kernel.Elaboration.FieldEntityList
import A12Kernel.Semantics.DateRangeOverlapOperators

/-! # Checked DateRange overlap operands

This boundary owns operator-specific static admission and full-validation checked-document assembly for DateRange overlap conditions. It reuses the shared entity-list shape and the canonical checked DateRange declaration policy; pure overlap truth and polarity remain in `A12Kernel.Semantics.DateRangeOverlapOperators`.
-/

namespace A12Kernel

/-- Static refusal while certifying the singular DateRange overlap operand list. -/
inductive DateRangesOverlapElabError where
  | shape (error : FieldEntityShapeElabError)
  | sourceNotDateRange (path : List String) (actual : SurfaceScalarKind)
  | unsupportedPolicy (path : List String) (format separator : String)
  | unsupportedReadForm (path : List String) (form : FieldEntityReadForm)
  | groupsNotAllowed (path : GroupPath)
  | having (error : CorrelationElabError)
  | incoherentCore
  deriving Repr, DecidableEq

namespace DateRangesOverlapElabError

def diagnostic? : DateRangesOverlapElabError → Option KernelStaticDiagnostic
  | .shape error => error.diagnostic?
  | .groupsNotAllowed _ => some .noGroupsAllowed
  | .sourceNotDateRange _ _ | .unsupportedPolicy _ _ _ |
      .unsupportedReadForm _ _ | .having _ | .incoherentCore => none

end DateRangesOverlapElabError

/-- One certified direct, plain-star, or filter-bearing star DateRange operand. -/
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

/-- A model-checked nonempty `DateRangesOverlap` operand list retaining the shared shape and exact authored filter slots. -/
structure CheckedDateRangesOverlapSource (model : FlatModel) where
  private mk ::
  shape : CheckedFieldEntityShape model
  first : CheckedDateRangesOverlapOperand model
  rest : List (CheckedDateRangesOverlapOperand model)

namespace CheckedDateRangesOverlapSource

def operands (checked : CheckedDateRangesOverlapSource model) :
    List (CheckedDateRangesOverlapOperand model) :=
  checked.first :: checked.rest

def hasHaving (checked : CheckedDateRangesOverlapSource model) : Bool :=
  checked.operands.any CheckedDateRangesOverlapOperand.hasHaving

end CheckedDateRangesOverlapSource

private def certifyDateRangesOverlapField (declaration : FlatFieldDecl) :
    Except DateRangesOverlapElabError CheckedCanonicalDateRangeField :=
  (certifyCanonicalDateRangeField declaration).mapError fun
    | .notDateRange path actual => .sourceNotDateRange path actual.surfaceKind
    | .unsupportedPolicy path format separator =>
        .unsupportedPolicy path format separator
    | .incoherentCore => .incoherentCore

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

private def certifyDateRangesOverlapOperands (model : FlatModel)
    (declaringGroup : GroupPath) : List (ResolvedFieldEntityOperand model) →
      Except DateRangesOverlapElabError
        (List (CheckedDateRangesOverlapOperand model))
  | [] => pure []
  | operand :: remaining => do
      pure ((← certifyDateRangesOverlapOperand model declaringGroup operand) ::
        (← certifyDateRangesOverlapOperands model declaringGroup remaining))

/-- Apply the shared shape gates first, then the singular operator's group refusal and exact DateRange policy certification in authored order. -/
def elaborateDateRangesOverlapSource (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceFieldEntitySource) :
    Except DateRangesOverlapElabError
      (CheckedDateRangesOverlapSource model) := do
  let shape ← elaborateFieldEntityShape model declaringGroup authored
    |>.mapError .shape
  let first ← certifyDateRangesOverlapOperand model declaringGroup shape.first
  let rest ← certifyDateRangesOverlapOperands model declaringGroup shape.rest
  pure { shape, first, rest }

/-! ## Checked-document assembly -/

/-- Structural failure while projecting an admitted DateRange source from one immutable checked document. -/
inductive DateRangesOverlapEvaluationError where
  | addressing (error : CheckedAddressingError)
  | sourceValueKind (address : CellAddr)
  | unresolvedRange (address : CellAddr) (value : DateRangeValue)
  deriving Repr, DecidableEq

/-- One resolved operand retains exact source and addressing metadata beside its pure overlap input. -/
structure ResolvedCheckedDateRangesOverlapOperand (model : FlatModel) where
  private mk ::
  source : CheckedDateRangesOverlapOperand model
  core : ResolvedCheckedEntityOperandCore
  semantic : ResolvedDateRangeOperand

private def checkedDateRangeSlot
    (addressed : CheckedAddressedCell) :
    Except DateRangesOverlapEvaluationError ResolvedDateRangeSlot :=
  match observeCell .validation addressed.cell with
  | .empty | .unknown _ | .poison _ => pure .skipped
  | .value (Value.dateRange value) =>
      match value.toResolvedDateRange? with
      | some range => pure (.kept range)
      | none => throw (.unresolvedRange addressed.address value)
  | .value _ => throw (.sourceValueKind addressed.address)

namespace CheckedDateRangesOverlapOperand

/-- Resolve and project one admitted operand without discarding authored identity, concrete addresses, topology, or filter provenance. -/
def resolveCheckedValidation
    (source : CheckedDateRangesOverlapOperand model)
    (document : CheckedDocument model) (outer : Env) :
    Except DateRangesOverlapEvaluationError
      (ResolvedCheckedDateRangesOverlapOperand model) := do
  let core ← (source.resolveValidationCore document outer).mapError .addressing
  let slots ← core.addressedCells.mapM checkedDateRangeSlot
  pure { source, core, semantic := { slots, hasFilter := core.hasHaving } }

end CheckedDateRangesOverlapOperand

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
