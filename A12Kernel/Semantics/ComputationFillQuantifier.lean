import A12Kernel.Semantics.Condition
import A12Kernel.Semantics.Observation
import A12Kernel.Semantics.StarAddressing
import A12Kernel.Semantics.FieldFillQuantifier

/-! # Resolved computation field-fill quantifiers

This capsule classifies reached computation observations and evaluates the seven field-fill quantifiers over an already-expanded ordered slot stream. It preserves the semantic difference between an instantiated empty cell and a declared-but-uninstantiated slot, and it stops at each operator's deciding cell so an unread invalid suffix cannot poison the computation. Resolved declaration sources share the addressed extent resolver; authored path resolution, group expansion, filtering and validation-mode truth/polarity remain separate boundaries.
-/

namespace A12Kernel

/-- One resolved slot in a computation-side field-fill scan. An uninstantiated slot belongs to the declared range but has no cell read in the instantiated range. -/
inductive ComputationFillSlot where
  | filled
  | empty
  | uninstantiated
  | poison (cause : FormalCause)
  deriving Repr, DecidableEq

/-- A resolved field occurrence in an ordered fill list. Group expansion preserves one entry
per declaration; its bound depth retains exactly the axes above the operand. -/
inductive ComputationFillSource where
  | direct (field : FieldId)
  | expanded (field : FieldId) (axes : List StarAxis) (boundCount : Nat)
  deriving Repr, DecidableEq

def ComputationFillSource.field : ComputationFillSource → FieldId
  | .direct field | .expanded field _ _ => field

/-- Topology and the current checked-cell overlay for addressed computation guards. -/
structure ComputationFillContext where
  document : Document
  read : Env → FieldId → CheckedCell

inductive ComputationFillError where
  | contextRequired
  | addressing (error : StarAddressingError)
  deriving Repr, DecidableEq

namespace CellObservation

/-- Classify one reached computation read for an ordered field-fill scan. Either formal-unavailability face becomes the exact poison carried by the slot. -/
@[simp]
def asComputationFillSlot : CellObservation → ComputationFillSlot
  | .empty => .empty
  | .value _ => .filled
  | .unknown cause => .poison cause
  | .poison cause => .poison cause

end CellObservation

/-- Resolve all occurrences through the shared in-capacity extent. The per-declaration tail stays
beside its cells, as required by `evalComputation_omittedRun`. -/
def ComputationFillSource.slots (source : ComputationFillSource)
    (read : FieldId → CheckedCell) (outer : Env) (addressed : Option ComputationFillContext) :
    Except ComputationFillError (List ComputationFillSlot) := do
  let observe (cell : CheckedCell) : Option ComputationFillSlot :=
    if cell.findings.contains .overRepetition then none
    else some (observeCell .computation cell).asComputationFillSlot
  match source with
  | .direct field =>
      pure (observe (read field)).toList
  | .expanded field axes boundCount =>
      let some context := addressed | throw .contextRequired
      let (environments, omitted) ←
        (StarAxes.resolveOperandExtent axes context.document outer boundCount).mapError .addressing
      pure ((environments.filterMap fun environment => observe (context.read environment field)) ++
        if omitted then [.uninstantiated] else [])

namespace FieldFillQuantifier

private inductive ScanResult where
  | found
  | exhausted
  | poison (cause : FormalCause)

/-- Find the first filled instantiated slot. Declared-but-uninstantiated slots are outside this scan. -/
private def scanAnyFilled : List ComputationFillSlot → ScanResult
  | [] => .exhausted
  | .filled :: _ => .found
  | .empty :: remaining => scanAnyFilled remaining
  | .uninstantiated :: remaining => scanAnyFilled remaining
  | .poison cause :: _ => .poison cause

/-- Find the first empty slot in the declared range. An uninstantiated declaration is a deciding empty without a cell read. -/
private def scanAnyDeclaredEmpty : List ComputationFillSlot → ScanResult
  | [] => .exhausted
  | .filled :: remaining => scanAnyDeclaredEmpty remaining
  | .empty :: _ => .found
  | .uninstantiated :: _ => .found
  | .poison cause :: _ => .poison cause

/-- Find a second filled instantiated slot, retaining whether the first has already been seen. -/
private def scanSecondFilled : List ComputationFillSlot → Bool → ScanResult
  | [], _ => .exhausted
  | .filled :: _, true => .found
  | .filled :: remaining, false => scanSecondFilled remaining true
  | .empty :: remaining, seenFirst => scanSecondFilled remaining seenFirst
  | .uninstantiated :: remaining, seenFirst => scanSecondFilled remaining seenFirst
  | .poison cause :: _, _ => .poison cause

/-- Evaluate one field-fill quantifier over the canonical resolved slot order. `NotExactlyOneFieldFilled` and `FieldsNotCollectivelyFilled` deliberately perform their two source-level scans from the beginning; the slot domain is pure, so rereading a clean slot adds no state, while the first reached poison remains exact. -/
def evalComputation (operator : FieldFillQuantifier)
    (slots : List ComputationFillSlot) : ComputationConditionResult :=
  match operator with
  | .allFieldsFilled =>
      match scanAnyDeclaredEmpty slots with
      | .found => .notTrue
      | .exhausted => .holds
      | .poison cause => .poison cause
  | .noFieldFilled =>
      match scanAnyFilled slots with
      | .found => .notTrue
      | .exhausted => .holds
      | .poison cause => .poison cause
  | .atLeastOneFieldFilled =>
      match scanAnyFilled slots with
      | .found => .holds
      | .exhausted => .notTrue
      | .poison cause => .poison cause
  | .moreThanOneFieldFilled =>
      match scanSecondFilled slots false with
      | .found => .holds
      | .exhausted => .notTrue
      | .poison cause => .poison cause
  | .notAllFieldsFilled =>
      match scanAnyDeclaredEmpty slots with
      | .found => .holds
      | .exhausted => .notTrue
      | .poison cause => .poison cause
  | .notExactlyOneFieldFilled =>
      match scanAnyFilled slots with
      | .exhausted => .holds
      | .poison cause => .poison cause
      | .found =>
          match scanSecondFilled slots false with
          | .found => .holds
          | .exhausted => .notTrue
          | .poison cause => .poison cause
  | .fieldsNotCollectivelyFilled =>
      match scanAnyFilled slots with
      | .exhausted => .notTrue
      | .poison cause => .poison cause
      | .found =>
          match scanAnyDeclaredEmpty slots with
          | .found => .holds
          | .exhausted => .notTrue
          | .poison cause => .poison cause

private theorem scanAnyFilled_omittedRun (before suffix : List ComputationFillSlot) (count : Nat) :
    scanAnyFilled (before ++ List.replicate count .uninstantiated ++ suffix) =
      scanAnyFilled (before ++ suffix) := by
  induction before with
  | nil =>
      induction count with
      | zero => rfl
      | succ count ih => simpa [scanAnyFilled, List.replicate_succ] using ih
  | cons head rest ih => cases head <;> simp_all [scanAnyFilled]

private theorem scanAnyDeclaredEmpty_omittedRun (before suffix : List ComputationFillSlot)
    (count : Nat) :
    scanAnyDeclaredEmpty (before ++ List.replicate (count + 1) .uninstantiated ++ suffix) =
      scanAnyDeclaredEmpty (before ++ [.uninstantiated] ++ suffix) := by
  induction before with
  | nil => simp [scanAnyDeclaredEmpty, List.replicate_succ]
  | cons head rest ih => cases head <;> simp_all [scanAnyDeclaredEmpty]

private theorem scanSecondFilled_omittedRun (before suffix : List ComputationFillSlot)
    (count : Nat) (seen : Bool) :
    scanSecondFilled (before ++ List.replicate count .uninstantiated ++ suffix) seen =
      scanSecondFilled (before ++ suffix) seen := by
  induction before generalizing seen with
  | nil =>
      induction count with
      | zero => rfl
      | succ count ih => simpa [scanSecondFilled, List.replicate_succ] using ih
  | cons head rest ih => cases head <;> cases seen <;> simp_all [scanSecondFilled]

/-- Every nonempty run of declared omissions has the same meaning as one marker at that exact
position. This permits the checked operand core's open-tail bit to supply all seven scans. -/
theorem evalComputation_omittedRun (operator : FieldFillQuantifier)
    (before suffix : List ComputationFillSlot) (count : Nat) :
    operator.evalComputation (before ++ List.replicate (count + 1) .uninstantiated ++ suffix) =
      operator.evalComputation (before ++ [.uninstantiated] ++ suffix) := by
  have one : [.uninstantiated] = List.replicate 1 (ComputationFillSlot.uninstantiated) := rfl
  cases operator <;> simp only [evalComputation, scanAnyDeclaredEmpty_omittedRun] <;>
    rw [one] <;> simp only [scanAnyFilled_omittedRun, scanSecondFilled_omittedRun]

end FieldFillQuantifier

end A12Kernel
