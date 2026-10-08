import A12Kernel.Semantics.FirstFilledScan
import A12Kernel.Semantics.NumericComputationResult
import A12Kernel.Semantics.BooleanApplication
import A12Kernel.Semantics.Correlation
import A12Kernel.Semantics.ScalarEquality
import A12Kernel.Semantics.ValueList

/-! # Resolved `FirstFilledValue`

This capsule scans one or more resolved homogeneous field-list operands in authored order after expansion and `Having` filtering. It stops at the first present value or first unavailable cell and enters each operand's filter only when that slot is reached. A reached selection with no concrete cell is observed as a not-given prefix before a later operand; the combiner's separate omitted-tail flag still affects only its all-exhausted identity. Number and exact-token families share this ordered mechanism; the bounded Boolean computation specializes it through a typed canonical-token adapter rather than widening every generic value-list operator to Boolean.
-/

namespace A12Kernel

/-- Apply the computation iterator's one-kept-successor traversal to any first-filled target classifier. The filter owns candidate order and poison timing; the supplied classifier owns only the current kept target. -/
def scanFilteredComputationFirstFilled
    (condition : CorrelatedHaving) (filterContext : CorrelationContext)
    (outer : Env) (cell : Env → ValueListCell kind)
    (environments : List Env) (hasUninstantiatedTail : Bool)
    (state : FirstFilledScanState) :
    Except CorrelationRuntimeFault (FirstFilledScanState ⊕ FirstFilledScanResult kind) := do
  let entered := state.enter hasUninstantiatedTail true
  let consume := fun current environment =>
    match current.step (cell environment) with
    | .continue next => .inl next
    | .done result => .inr result
  match ← condition.scanComputation filterContext outer consume
      environments entered with
  | .exhausted next => pure (.inl next)
  | .terminated result => pure (.inr result)
  | .poison cause => pure (.inr (.unavailable cause))

/-- Addressed filtered computation delegates filter and target failure timing to the shared one-kept-successor scan. Structural failures stay in `Except`; formal poison remains semantic unavailability. -/
def scanFilteredComputationFirstFilledResolving
    (condition : CorrelatedHaving)
    (filterContext : ResolvingCorrelationContext Error)
    (outer : Env) (cell : Env → Except Error (ValueListCell kind))
    (environments : List Env) (hasUninstantiatedTail : Bool)
    (state : FirstFilledScanState) :
    Except Error (FirstFilledScanState ⊕ FirstFilledScanResult kind) := do
  let entered := state.enter hasUninstantiatedTail true
  let consume := fun current environment => do
    match current.step (← cell environment) with
    | .continue next => pure (.inl next)
    | .done result => pure (.inr result)
  match ← condition.scanComputationResolving filterContext outer consume
      environments entered with
  | .exhausted next => pure (.inl next)
  | .terminated result => pure (.inr result)
  | .poison cause => pure (.inr (.unavailable cause))

/-- One reached computation `FirstFilledValue` operand of any kind, as its carrier resolves it at
the scan's environment: a direct cell, a star's in-capacity rows, a filtered star's rows, or a
group's resolved cells. Each carrier owns only the resolution and its cells' classifier. -/
inductive FirstFilledComputationSelection (kind : ValueListKind) where
  | cell (cell : ValueListCell kind)
  | rows (environments : List Env) (hasUninstantiatedTail : Bool) (cell : Env → ValueListCell kind)
  | filtered (condition : CorrelatedHaving) (filterContext : CorrelationContext)
      (environments : List Env) (hasUninstantiatedTail : Bool) (cell : Env → ValueListCell kind)
  | side (side : ResolvedValueListSide kind)

namespace FirstFilledComputationSelection

/-- Scan one reached selection: a star with no row reached is a not-given prefix, and a filter owns
its candidates' order and poison timing. -/
def scan (outer : Env) (state : FirstFilledScanState) :
    FirstFilledComputationSelection kind → Except CorrelationRuntimeFault (FirstFilledScanState ⊕ FirstFilledScanResult kind)
  | .cell reached => match state.step reached with
      | .continue next => pure (.inl next)
      | .done result => pure (.inr result)
  | .rows environments hasUninstantiatedTail classify =>
      pure (scanFirstFilledItems classify environments
        (state.enterSelection environments.isEmpty hasUninstantiatedTail false))
  | .filtered condition filterContext environments hasUninstantiatedTail classify =>
      scanFilteredComputationFirstFilled condition filterContext outer classify environments
        hasUninstantiatedTail state
  | .side resolved => pure (scanFirstFilledItems id resolved.cells (state.enterOperand resolved))

end FirstFilledComputationSelection

/-- Scan authored operands in order, resolving each only once every earlier one has fallen through,
so a later operand's structural failure is never reached past a selected value. The caller closes an
exhausted scan with its family's identity. -/
def scanComputationFirstFilledSelections (outer : Env) (runtimeFault : CorrelationRuntimeFault → Error)
    (resolve : α → Except Error (FirstFilledComputationSelection kind)) :
    List α → FirstFilledScanState → Except Error (FirstFilledScanState ⊕ FirstFilledScanResult kind)
  | [], state => pure (.inl state)
  | operand :: remaining, state => do
      match ← ((← resolve operand).scan outer state).mapError runtimeFault with
      | .inl next => scanComputationFirstFilledSelections outer runtimeFault resolve remaining next
      | .inr result => pure (.inr result)

private def scanFirstFilledCells
    (cells : List (ValueListCell kind)) (state : FirstFilledScanState) :
    FirstFilledScanState ⊕ FirstFilledScanResult kind :=
  scanFirstFilledItems id cells state

/-- A nonempty homogeneous resolved operand list in authored encounter order. -/
structure FirstFilledOperands (kind : ValueListKind) where
  first : ResolvedValueListSide kind
  rest : List (ResolvedValueListSide kind)

/-- Compatibility name for the established Number API. -/
abbrev FirstFilledNumberOperands := FirstFilledOperands .number

/-- The exact-token operand specialization. -/
abbrev FirstFilledTokenOperands := FirstFilledOperands .token

private def scanFirstFilledOperands :
    List (ResolvedValueListSide kind) → FirstFilledScanState →
      FirstFilledScanState ⊕ FirstFilledScanResult kind
  | [], state => .inl state
  | side :: sides, state =>
      match scanFirstFilledCells side.cells (state.enterOperand side) with
      | .inl next => scanFirstFilledOperands sides next
      | .inr result => .inr result

/-- Select the first usable Number across nonempty resolved operand slots. Each slot's filter and cells are observed only after every earlier slot has fallen through. -/
def evalFirstFilledNumberOperands
    (operands : FirstFilledNumberOperands) : FirstFilledNumberResult :=
  match scanFirstFilledOperands (operands.first :: operands.rest) {} with
  | .inl state => state.finish
  | .inr result => result.asNumber

/-- Select the first usable Number from one resolved operand. An explicit, uninstantiated, or otherwise cell-free reached selection contributes fillable zero; the operand's resolved `Having` clause also makes any selected value fillable. -/
def evalFirstFilledNumber
    (side : ResolvedValueListSide .number) : FirstFilledNumberResult :=
  evalFirstFilledNumberOperands { first := side, rest := [] }

/-- Select the first usable exact token across nonempty resolved operand slots. Exhaustion retains no synthetic String or Enumeration value. -/
def evalFirstFilledTokenOperands
    (operands : FirstFilledTokenOperands) : FirstFilledTokenResult :=
  match scanFirstFilledOperands (operands.first :: operands.rest) {} with
  | .inl _ => .noValue
  | .inr result => result.asToken

/-- Select the first usable exact token from one resolved operand. -/
def evalFirstFilledToken
    (side : ResolvedValueListSide .token) : FirstFilledTokenResult :=
  evalFirstFilledTokenOperands { first := side, rest := [] }

/-- Select the first usable Boolean from one resolved unfiltered operand. The typed adapter reuses the exact-token scan without exposing Boolean through unrelated generic value-list operators. -/
def evalFirstFilledBoolean
    (cells : List FirstFilledBooleanCell) :
    FirstFilledBooleanComputationResult :=
  let tokenCell : FirstFilledBooleanCell → ValueListCell .token
    | .present true => .present "true"
    | .present false => .present "false"
    | .empty => .empty
    | .unknown cause => .unknown cause
  let tokenSide : ResolvedValueListSide .token := {
    cells := cells.map tokenCell
    hasUninstantiatedTail := false
    hasHaving := false
  }
  match evalFirstFilledToken tokenSide with
  | .value "true" _ => .value true
  | .value "false" _ => .value false
  | .value _ _ => .poison .malformed
  | .noValue => .noValue
  | .unavailable cause => .poison cause



namespace FirstFilledTokenResult

/-- Validation compares an available token exactly and retains whether an earlier empty/filter could displace it. Exhaustion suppresses the comparison. -/
def asValidationOperand : FirstFilledTokenResult → SimpleComparisonOperand String
  | .value token notGiven => .value token (!notGiven)
  | .noValue => .notEvaluated
  | .unavailable cause => .unknown cause

/-- Computation retains the selected exact token, clean no-value, or first formal poison without choosing a target family. -/
def asComputationResult : FirstFilledTokenResult → TokenComputationResult
  | .value token _ => .value token
  | .noValue => .noValue
  | .unavailable cause => .poison cause

end FirstFilledTokenResult

end A12Kernel
