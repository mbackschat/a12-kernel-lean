import A12Kernel.Semantics.NumericComputationResult
import A12Kernel.Semantics.Correlation
import A12Kernel.Semantics.ScalarEquality
import A12Kernel.Semantics.ValueList

/-! # Resolved `FirstFilledValue`

This capsule scans one or more resolved homogeneous field-list operands in authored order after expansion and `Having` filtering. It stops at the first present value or first unavailable cell and enters each operand's filter only when that slot is reached. A reached selection with no concrete cell is observed as a not-given prefix before a later operand; the combiner's separate omitted-tail flag still affects only its all-exhausted identity. Number and exact-token families share this ordered mechanism but retain different all-exhausted results and phase projections.
-/

namespace A12Kernel

/-- The resolved Number selection before a validation or computation consumer interprets it. `notGiven` retains the kernel-observed polarity contribution of an empty prefix, an uninstantiated empty selection, or a `Having` filter. -/
inductive FirstFilledNumberResult where
  | value (amount : Rat) (notGiven : Bool)
  | unavailable (cause : FormalCause)
  deriving Repr, DecidableEq

/-- The resolved String/stored-Enumeration selection. Unlike Number, an exhausted token family has no synthetic value. -/
inductive FirstFilledTokenResult where
  | value (token : String) (notGiven : Bool)
  | noValue
  | unavailable (cause : FormalCause)
  deriving Repr, DecidableEq

/-- Computation projection shared by exact-token result families without assigning String or Enumeration target semantics. -/
inductive TokenComputationResult where
  | value (token : String)
  | noValue
  | poison (cause : FormalCause)
  deriving Repr, DecidableEq

/-- The prefix fact retained while an ordered first-filled scan can still change. -/
structure FirstFilledScanState where
  emptyBefore : Bool := false
  encounteredHaving : Bool := false
  omittedTailSeen : Bool := false
  deriving Repr, DecidableEq

/-- One kind-neutral scan result before the consuming family supplies its all-exhausted identity and phase projections. -/
inductive FirstFilledScanResult (kind : ValueListKind) where
  | value (atom : ValueListAtom kind) (notGiven : Bool)
  | unavailable (cause : FormalCause)

/-- One shared scan step either continues after an empty cell or terminates at the first value or formal unavailability. -/
inductive FirstFilledScanStep (kind : ValueListKind) where
  | continue (state : FirstFilledScanState)
  | done (result : FirstFilledScanResult kind)

namespace FirstFilledScanState

/-- Enter one reached operand's metadata before inspecting its cells. A filter affects a later selected value; an omitted tail affects only the all-exhausted identity. -/
def enter (state : FirstFilledScanState)
    (hasUninstantiatedTail hasHaving : Bool) : FirstFilledScanState :=
  { state with
    encounteredHaving := state.encounteredHaving || hasHaving
    omittedTailSeen := state.omittedTailSeen || hasUninstantiatedTail }

/-- Enter one reached resolved selection. The runtime wrapper presents a selection with no concrete cell as a not-given prefix before continuing to a later authored operand; this remains distinct from the combiner's omitted-tail flag. -/
def enterSelection (state : FirstFilledScanState)
    (selectionEmpty hasUninstantiatedTail hasHaving : Bool) :
    FirstFilledScanState :=
  let entered := state.enter hasUninstantiatedTail hasHaving
  { entered with emptyBefore := entered.emptyBefore || selectionEmpty }

/-- Enter one resolved operand before inspecting its cells. -/
def enterOperand (state : FirstFilledScanState)
    (side : ResolvedValueListSide kind) : FirstFilledScanState :=
  state.enterSelection side.cells.isEmpty
    side.hasUninstantiatedTail side.hasHaving

/-- Consume one reached, relevant cell. Later consumers may place their own gates before invoking this step. -/
def step (state : FirstFilledScanState) :
    ValueListCell kind → FirstFilledScanStep kind
  | .present atom =>
      .done (.value atom (state.emptyBefore || state.encounteredHaving))
  | .empty => .continue { state with emptyBefore := true }
  | .unknown cause => .done (.unavailable cause)

/-- Close an exhausted scan with Number's zero identity and the exact accumulated missingness. -/
def finish (state : FirstFilledScanState) : FirstFilledNumberResult :=
  .value 0 (state.emptyBefore || state.omittedTailSeen || state.encounteredHaving)

end FirstFilledScanState

/-- Compatibility name for the established Number checked adapters. The scan state itself is kind-neutral. -/
abbrev FirstFilledNumberScanState := FirstFilledScanState

def FirstFilledScanResult.asNumber :
    FirstFilledScanResult .number → FirstFilledNumberResult
  | .value amount notGiven => .value amount notGiven
  | .unavailable cause => .unavailable cause

def FirstFilledScanResult.asToken :
    FirstFilledScanResult .token → FirstFilledTokenResult
  | .value token notGiven => .value token notGiven
  | .unavailable cause => .unavailable cause

/-- Lazily scan caller-owned items through one cell projection. A terminal value or unavailability prevents the projection from being applied to the suffix. -/
def scanFirstFilledItems (cell : α → ValueListCell kind) :
    List α → FirstFilledScanState →
      FirstFilledScanState ⊕ FirstFilledScanResult kind
  | [], state => .inl state
  | item :: items, state =>
      match state.step (cell item) with
      | .continue next => scanFirstFilledItems cell items next
      | .done result => .inr result

/-- The same prefix scan over a structurally failing cell projection. A terminal semantic result prevents every suffix projection, while a reached structural failure stays outside semantic unavailability. -/
def scanFirstFilledItemsResolving
    (cell : α → Except Error (ValueListCell kind)) :
    List α → FirstFilledScanState →
      Except Error (FirstFilledScanState ⊕ FirstFilledScanResult kind)
  | [], state => pure (.inl state)
  | item :: items, state => do
      match state.step (← cell item) with
      | .continue next =>
          scanFirstFilledItemsResolving cell items next
      | .done result => pure (.inr result)

/-- Apply the computation iterator's one-kept-successor traversal to any first-filled target classifier. The filter owns candidate order and poison timing; the supplied classifier owns only the current kept target. -/
def scanFilteredComputationFirstFilled
    (condition : CorrelatedHaving) (filterContext : CorrelationContext)
    (outer : Env) (cell : Env → ValueListCell kind)
    (environments : List Env) (hasUninstantiatedTail : Bool)
    (state : FirstFilledScanState) :
    FirstFilledScanState ⊕ FirstFilledScanResult kind :=
  let entered := state.enter hasUninstantiatedTail true
  let consume := fun current environment =>
    match current.step (cell environment) with
    | .continue next => .inl next
    | .done result => .inr result
  match condition.scanComputation filterContext outer consume
      environments entered with
  | .exhausted next => .inl next
  | .terminated result => .inr result
  | .poison cause => .inr (.unavailable cause)

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

namespace FirstFilledNumberResult

/-- Validation observes the selected amount together with the retained not-given/fillability classification. -/
def asValidationOperand : FirstFilledNumberResult → NumericOperand
  | .value amount true => .value amount .both
  | .value amount false => .value amount .fixed
  | .unavailable cause => .unknown cause

/-- Computation consumes the selected amount but treats reached formal invalidity as poison. -/
def asComputationResult : FirstFilledNumberResult → NumericComputationResult
  | .value amount _ => .value amount
  | .unavailable cause => .poison cause

end FirstFilledNumberResult

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
