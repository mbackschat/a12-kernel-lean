import A12Kernel.Semantics.SemanticIndexColumn
import A12Kernel.Semantics.Condition
import A12Kernel.Semantics.Observation
import A12Kernel.Semantics.StarAddressing
import A12Kernel.Semantics.FieldFillQuantifier
import A12Kernel.Semantics.GroupReference

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
  /-- Whether `document` instantiates every repeatable row of the field's address at the
  environment; `read` cannot tell an absent row from a malformed cell. A context that is not built
  from a checked document treats every row as present, so it must not address a row an index's
  selected group lacks. -/
  rowsPresent : Env → FieldId → Bool := fun _ _ => true
  /-- Exact current storage paired with checked reads; temporal uniqueness compares this identity. -/
  storedText : Env → FieldId → Option String := fun _ _ => none
  /-- Number-to-String consumes regime-selected formal text, not raw storage or a rendered rational (spec/04). -/
  numberText : Env → FieldId → Option String := fun _ _ => none
  /-- Prepared index entries are immutable because index fields cannot be computed (spec/09).
  Target payloads are projected through the current read channel after selecting a row. -/
  indexColumn : GroupPath → Env → Option ResolvedSemanticIndexColumn := fun _ _ => none

inductive ComputationFillError where
  | indexedOperandNotSupported
  | declaredCapacityRequired
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

/-- Count every filled instantiated slot, preserving the first failed operand. Unlike a deciding
field-fill quantifier, the count cannot discard an invalid suffix after finding filled content
(`spec/09` §3.2); declared omissions contribute zero without a cell read. -/
def numberOfFilledFieldsForComputation : List ComputationFillSlot → Except FormalCause Nat
  | [] => .ok 0
  | .filled :: remaining => Nat.succ <$> numberOfFilledFieldsForComputation remaining
  | .empty :: remaining | .uninstantiated :: remaining => numberOfFilledFieldsForComputation remaining
  | .poison cause :: _ => .error cause

namespace FieldFillQuantifier

inductive ScanResult where
  | found
  | exhausted
  | poison (cause : FormalCause)
  deriving Repr, DecidableEq

/-- The family has two instantiated searches and one declared-range search; the filtered
field-fill grid (2026-10-04) separates their missing-coordinate behavior. -/
inductive ScanKind where
  | anyFilled
  | anyDeclaredEmpty
  | secondFilled
  deriving Repr, DecidableEq

/-- One reached slot either advances the search or decides it. The Boolean state records only
whether the second-filled search has already seen its first witness. -/
def step (kind : ScanKind) (seen : Bool) : ComputationFillSlot → Bool ⊕ ScanResult
  | .poison cause => .inr (.poison cause)
  | .filled => match kind with
      | .anyFilled => .inr .found
      | .anyDeclaredEmpty => .inl seen
      | .secondFilled => if seen then .inr .found else .inl true
  | .empty => match kind with
      | .anyDeclaredEmpty => .inr .found
      | _ => .inl seen
  | .uninstantiated => match kind with
      | .anyDeclaredEmpty => .inr .found
      | _ => .inl seen

/-- Scan reached reads while retaining the witness state for the next operand. -/
def scanRead (kind : ScanKind) (read : slot → ComputationFillSlot) :
    List slot → Bool → Bool ⊕ ScanResult
  | [], seen => .inl seen
  | slot :: rest, seen => match step kind seen (read slot) with
      | .inl next => scanRead kind read rest next
      | .inr result => .inr result

def scanSlots (kind : ScanKind) (seen : Bool) (slots : List ComputationFillSlot) : ScanResult :=
  match scanRead kind id slots seen with
  | .inl _ => .exhausted
  | .inr result => result

private def scanAnyFilled (slots : List ComputationFillSlot) : ScanResult :=
  scanSlots .anyFilled false slots

private def scanAnyDeclaredEmpty (slots : List ComputationFillSlot) : ScanResult :=
  scanSlots .anyDeclaredEmpty false slots

private def scanSecondFilled (slots : List ComputationFillSlot) (seen : Bool) : ScanResult :=
  scanSlots .secondFilled seen slots

/-- Execute the family's scan program. Each callback invocation starts at the first operand:
composite guards restart, and may switch from instantiated to declared candidates. -/
def evalComputationUsing [Monad m] (operator : FieldFillQuantifier)
    (scan : ScanKind → m ScanResult) : m ComputationConditionResult := do
  match operator with
  | .allFieldsFilled =>
      match ← scan .anyDeclaredEmpty with
      | .found => pure .notTrue
      | .exhausted => pure .holds
      | .poison cause => pure (.poison cause)
  | .noFieldFilled =>
      match ← scan .anyFilled with
      | .found => pure .notTrue
      | .exhausted => pure .holds
      | .poison cause => pure (.poison cause)
  | .atLeastOneFieldFilled =>
      match ← scan .anyFilled with
      | .found => pure .holds
      | .exhausted => pure .notTrue
      | .poison cause => pure (.poison cause)
  | .moreThanOneFieldFilled =>
      match ← scan .secondFilled with
      | .found => pure .holds
      | .exhausted => pure .notTrue
      | .poison cause => pure (.poison cause)
  | .notAllFieldsFilled =>
      match ← scan .anyDeclaredEmpty with
      | .found => pure .holds
      | .exhausted => pure .notTrue
      | .poison cause => pure (.poison cause)
  | .notExactlyOneFieldFilled =>
      match ← scan .anyFilled with
      | .exhausted => pure .holds
      | .poison cause => pure (.poison cause)
      | .found =>
          match ← scan .secondFilled with
          | .found => pure .holds
          | .exhausted => pure .notTrue
          | .poison cause => pure (.poison cause)
  | .fieldsNotCollectivelyFilled =>
      match ← scan .anyFilled with
      | .exhausted => pure .notTrue
      | .poison cause => pure (.poison cause)
      | .found =>
          match ← scan .anyDeclaredEmpty with
          | .found => pure .holds
          | .exhausted => pure .notTrue
          | .poison cause => pure (.poison cause)

/-- Effectful direct reads share the scan transition; a deciding prefix cannot reach a later
addressing failure or poison (spec/09 §3.2). -/
def scanReadM [Monad m] (kind : ScanKind) (read : slot → m ComputationFillSlot) :
    List slot → Bool → m ScanResult
  | [], _ => pure .exhausted
  | slot :: rest, seen => do
      match step kind seen (← read slot) with
      | .inl next => scanReadM kind read rest next
      | .inr result => pure result

def evalComputationRead [Monad m] (operator : FieldFillQuantifier)
    (read : slot → m ComputationFillSlot) (slots : List slot) : m ComputationConditionResult :=
  operator.evalComputationUsing fun kind => scanReadM kind read slots false

/-- Materialized and addressed consumers execute the same scan program. -/
def evalComputation (operator : FieldFillQuantifier)
    (slots : List ComputationFillSlot) : ComputationConditionResult :=
  Id.run (operator.evalComputationUsing fun kind => pure (match kind with
    | .anyFilled => scanAnyFilled slots
    | .anyDeclaredEmpty => scanAnyDeclaredEmpty slots
    | .secondFilled => scanSecondFilled slots false))

private theorem scanAnyFilled_omittedRun (before suffix : List ComputationFillSlot) (count : Nat) :
    scanAnyFilled (before ++ List.replicate count .uninstantiated ++ suffix) =
      scanAnyFilled (before ++ suffix) := by
  induction before with
  | nil =>
      induction count with
      | zero => rfl
      | succ count ih => simpa [scanAnyFilled, scanSlots, scanRead, step, List.replicate_succ] using ih
  | cons head rest ih => cases head <;> simp_all [scanAnyFilled, scanSlots, scanRead, step]

private theorem scanAnyDeclaredEmpty_omittedRun (before suffix : List ComputationFillSlot)
    (count : Nat) :
    scanAnyDeclaredEmpty (before ++ List.replicate (count + 1) .uninstantiated ++ suffix) =
      scanAnyDeclaredEmpty (before ++ [.uninstantiated] ++ suffix) := by
  induction before with
  | nil => simp [scanAnyDeclaredEmpty, scanSlots, scanRead, step, List.replicate_succ]
  | cons head rest ih => cases head <;> simp_all [scanAnyDeclaredEmpty, scanSlots, scanRead, step]

private theorem scanSecondFilled_omittedRun (before suffix : List ComputationFillSlot)
    (count : Nat) (seen : Bool) :
    scanSecondFilled (before ++ List.replicate count .uninstantiated ++ suffix) seen =
      scanSecondFilled (before ++ suffix) seen := by
  induction before generalizing seen with
  | nil =>
      induction count with
      | zero => rfl
      | succ count ih => simpa [scanSecondFilled, scanSlots, scanRead, step, List.replicate_succ] using ih
  | cons head rest ih => cases head <;> cases seen <;> simp_all [scanSecondFilled, scanSlots, scanRead, step]

/-- Every nonempty run of declared omissions has the same meaning as one marker at that exact
position. This permits the checked operand core's open-tail bit to supply all seven scans. -/
theorem evalComputation_omittedRun (operator : FieldFillQuantifier)
    (before suffix : List ComputationFillSlot) (count : Nat) :
    operator.evalComputation (before ++ List.replicate (count + 1) .uninstantiated ++ suffix) =
      operator.evalComputation (before ++ [.uninstantiated] ++ suffix) := by
  have one : [.uninstantiated] = List.replicate 1 (ComputationFillSlot.uninstantiated) := rfl
  cases operator <;> simp only [evalComputation, evalComputationUsing, Id.run, bind, pure, scanAnyDeclaredEmpty_omittedRun] <;>
    rw [one] <;> simp only [scanAnyFilled_omittedRun, scanSecondFilled_omittedRun]

end FieldFillQuantifier

end A12Kernel
