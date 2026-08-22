import A12Kernel.Elaboration.DateRangeOverlap

/-! # Unconfigured yearless DateRange overlap

A model with no Base Year cannot complete a yearless DATE_RANGE declaration, and the Kernel
compares such ranges as month/day labels rather than refusing them. This capsule owns that
admission and evaluation separately from the Base-Year-completed route, because the two
retain different domains: the completed route yields exact instants, and this one must never
manufacture a year.

The admitted shape is deliberately narrow. Every operand is a direct stored field whose
declaration is yearless, and a list mixing a year-bearing operand with a yearless one is
refused here because the Kernel refuses it statically: with no Base Year to complete the
yearless side, the uniform-year gate in `A12Kernel.Elaboration.DateRangeOverlap` rejects the
whole list. A configured model completes the value instead, so a mixed list there is admitted
and belongs to the exact route. Filters, stars, groups, and the plural operator keep their
existing owners.
-/

namespace A12Kernel

/-- The two yearless component shapes an unconfigured declaration can denote. -/
inductive YearlessOverlapShape where
  | month
  | monthDay
  deriving Repr, DecidableEq

namespace YearlessOverlapShape

/-- Recognize a yearless stored-input profile under either of its declared spellings. -/
def ofInputFormat? : DateRangeInputFormat → Option YearlessOverlapShape
  | .yearlessMonth | .yearlessMonthConcatenated => some .month
  | .yearlessMonthDay | .yearlessDayMonthDotted => some .monthDay
  | _ => none

end YearlessOverlapShape

/-- Static refusal while checking an unconfigured yearless overlap operand. -/
inductive YearlessDateRangesOverlapElabError where
  | source (cause : DateRangesOverlapElabError)
  | baseYearConfigured (path : List String)
  | notYearless (path : List String) (format separator : String)
  deriving Repr, DecidableEq

/-- One direct stored field whose declaration is yearless in a model with no Base Year. -/
structure CheckedYearlessDateRangeOverlapField (model : FlatModel)
    extends CheckedDateRangeInputField where
  private mk ::
  shape : YearlessOverlapShape
  shapeOwned : YearlessOverlapShape.ofInputFormat? format = some shape
  modelUnconfigured : model.baseYear = none

/-- Certify one operand: the declaration must be a yearless profile and the model must supply no Base Year, because a configured model completes the value instead and belongs to the exact route. -/
def certifyYearlessDateRangeOverlapField (model : FlatModel)
    (declaration : FlatFieldDecl) :
    Except YearlessDateRangesOverlapElabError
      (CheckedYearlessDateRangeOverlapField model) := do
  let checked ← (certifyDateRangeInputField declaration).mapError fun
    | .notDateRange path actual => .source (.sourceNotDateRange path actual.surfaceKind)
    | .unsupportedPolicy path format separator =>
        .source (.unsupportedPolicy path format separator)
    | .incoherentCore => .source .incoherentCore
  match hShape : YearlessOverlapShape.ofInputFormat? checked.format with
  | none =>
      throw (.notYearless declaration.path checked.policy.format
        checked.policy.separator)
  | some shape =>
      if hModel : model.baseYear = none then
        pure { checked with shape, shapeOwned := hShape, modelUnconfigured := hModel }
      else
        throw (.baseYearConfigured declaration.path)

/-- Runtime refusal while resolving an admitted unconfigured yearless operand. -/
inductive YearlessDateRangesOverlapEvaluationError where
  | addressing (cause : CheckedAddressingError)
  | incoherentDirectOperand (count : Nat)
  | sourceValueProfile (address : CellAddr) (value : DateRangeCellValue)
  | sourceValueKind (address : CellAddr)
  deriving Repr, DecidableEq

namespace CheckedYearlessDateRangeOverlapField

/-- Project one addressed cell into a yearless slot. An empty, unavailable, or poisoned cell is skipped exactly as on the exact route; an exact cell is refused here rather than compared, because it belongs to the completed route. -/
private def slotFor (addressed : CheckedAddressedCell) :
    Except YearlessDateRangesOverlapEvaluationError
      (OverlapSlot YearlessInterval) :=
  match observeCell .validation addressed.cell with
  | .empty | .unknown _ | .poison _ => pure .skipped
  | .value (Value.dateRange (.yearlessMonth start finish)) =>
      pure (.kept (YearlessInterval.ofMonthPair start finish))
  | .value (Value.dateRange (.yearlessMonthDay start finish)) =>
      pure (.kept (YearlessInterval.ofMonthDayPair start finish))
  | .value (Value.dateRange value) =>
      throw (.sourceValueProfile addressed.address value)
  | .value _ => throw (.sourceValueKind addressed.address)

/-- Resolve one admitted operand against the checked document, retaining its single concrete address. -/
def resolveCheckedValidation
    (source : CheckedYearlessDateRangeOverlapField model)
    (document : CheckedDocument model) :
    Except YearlessDateRangesOverlapEvaluationError
      (OverlapOperand YearlessInterval) := do
  let core ← (document.resolveCheckedDirectEntityOperandCore source.declaration.id)
    |>.mapError .addressing
  match core.addressedCells with
  | [addressed] =>
      let slot ← slotFor addressed
      pure { slots := [slot], hasFilter := false }
  | addressed => throw (.incoherentDirectOperand addressed.length)

end CheckedYearlessDateRangeOverlapField

/-- Evaluate the any-pair scan over admitted unconfigured yearless operands in authored order. -/
def evaluateYearlessDateRangesOverlap
    (sources : List (CheckedYearlessDateRangeOverlapField model))
    (document : CheckedDocument model) :
    Except YearlessDateRangesOverlapEvaluationError Verdict := do
  let operands ← sources.mapM fun source =>
    source.resolveCheckedValidation document
  pure (evalYearlessRangesOverlap operands)

end A12Kernel
