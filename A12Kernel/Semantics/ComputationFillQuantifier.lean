import A12Kernel.Semantics.ComputationCondition
import A12Kernel.Semantics.FieldFillQuantifier

/-! # Resolved computation field-fill quantifiers

This capsule classifies reached computation observations and evaluates the seven field-fill quantifiers over an already-expanded ordered slot stream. It preserves the semantic difference between an instantiated empty cell and a declared-but-uninstantiated slot, and it stops at each operator's deciding cell so an unread invalid suffix cannot poison the computation. Path resolution, group expansion, repetition ordering, filtering, and validation-mode truth/polarity remain separate boundaries.
-/

namespace A12Kernel

/-- One resolved slot in a computation-side field-fill scan. An uninstantiated slot belongs to the declared range but has no cell read in the instantiated range. -/
inductive ComputationFillSlot where
  | filled
  | empty
  | uninstantiated
  | poison (cause : FormalCause)
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

end FieldFillQuantifier

end A12Kernel
