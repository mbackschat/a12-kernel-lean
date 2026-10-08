import A12Kernel.Semantics.NumericComputationResult
import A12Kernel.Semantics.BooleanApplication
import A12Kernel.Semantics.ScalarEquality
import A12Kernel.Semantics.ValueList

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

/-- The first-filled specialization of the shared Boolean computation outcome. -/
abbrev FirstFilledBooleanComputationResult := BooleanComputationOutcome

/-- One typed Boolean cell before the private canonical-token scan adapter. -/
inductive FirstFilledBooleanCell where
  | present (value : Bool)
  | empty
  | unknown (cause : FormalCause)
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

/-- Boolean, temporal and DateRange selection retain typed payloads and missing-prefix provenance
without introducing those kinds into unrelated value-list operators (spec/07, FirstFilledValue). -/
def scanFirstFilledObservations : List (CellObservation α) → FirstFilledScanState →
    FirstFilledScanState ⊕ SimpleComparisonOperand α
  | [], state => .inl state
  | .empty :: rest, state => scanFirstFilledObservations rest { state with emptyBefore := true }
  | .value value :: _, state => .inr (.value value (!(state.emptyBefore || state.encounteredHaving)))
  | .unknown cause :: _, _ | .poison cause :: _, _ => .inr (.unknown cause)

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

end A12Kernel
