import A12Kernel.Semantics.Correlation
import A12Kernel.Elaboration.NumericComputation.Evaluation

namespace A12Kernel.Conformance.CorrelationResolving
open A12Kernel

private def items : RepeatableLevel := 10

private def count : FlatNumberField :=
  { id := 0, info := { scale := 0, signed := false } }

private def payload : FlatNumberField :=
  { id := 1, info := { scale := 0, signed := false } }

private def marker : FlatNumberField :=
  { id := 2, info := { scale := 0, signed := false } }

private def nestedItems : RepeatableLevel := 20

private inductive ResolvingProbeError where
  | unsupportedDateCalendar
  | temporalValueFailure
  | worldUnavailable
  | typeValidityValueFailure
  | groupUnavailable (path : GroupPath)
  | storedTextUnavailable (field : FieldId)
  | read (field : FieldId)
  | binding (cause : EnvBindingError)
  deriving Repr, DecidableEq

private def resolvingCell : CheckedCell :=
  { rawPresent := true, parsed := some (.num 1), findings := [] }

private def resolvingContext :
    ResolvingCorrelationContext ResolvingProbeError where
  read _ field :=
    if field == marker.id then .error (.read field) else .ok resolvingCell
  unsupportedDateCalendar := .unsupportedDateCalendar
  temporalValueFailure := .temporalValueFailure
  worldUnavailable := .worldUnavailable
  storedTextUnavailable := .storedTextUnavailable
  typeValidityValueFailure := .typeValidityValueFailure
  groupUnavailable := .groupUnavailable
  bindingError := .binding

private def resolvingFrame : CorrelationFrame :=
  { innerEnv := [(items, 1)]
    outerEnv := [(items, 1)] }

private def resolvingNumber (field : FieldId) : HavingNumberRef :=
  { origin := .inner, field := { id := field, info := count.info } }

private def falseThenBadRead : CorrelatedHaving :=
  .and
    (CorrelatedHaving.compareNumbers .notEqual
      (resolvingNumber payload.id) (resolvingNumber payload.id))
    (CorrelatedHaving.compareNumbers .equal
      (resolvingNumber marker.id) (resolvingNumber payload.id))

private inductive ResolvingTruthSnapshot where
  | truth (value : K)
  | computation (value : ComputationConditionResult)
  | error (cause : ResolvingProbeError)
  deriving Repr, DecidableEq

private def truthSnapshot :
    Except ResolvingProbeError K → ResolvingTruthSnapshot
  | .ok value => .truth value
  | .error cause => .error cause

private def computationSnapshot :
    Except ResolvingProbeError ComputationConditionResult →
      ResolvingTruthSnapshot
  | .ok value => .computation value
  | .error cause => .error cause

private def resolvingCandidate (row : RowIndex) : Env :=
  [(items, row)]

private def orderedResolvingContext :
    ResolvingCorrelationContext ResolvingProbeError where
  read environment field :=
    if environment == resolvingCandidate 3 && field == marker.id then
      .error (.read field)
    else
      .ok resolvingCell
  unsupportedDateCalendar := .unsupportedDateCalendar
  temporalValueFailure := .temporalValueFailure
  worldUnavailable := .worldUnavailable
  storedTextUnavailable := .storedTextUnavailable
  typeValidityValueFailure := .typeValidityValueFailure
  groupUnavailable := .groupUnavailable
  bindingError := .binding

private def trueResolvingHaving : CorrelatedHaving :=
  CorrelatedHaving.compareNumbers .equal
    (resolvingNumber marker.id) (resolvingNumber payload.id)

private inductive ResolvingTraversalSnapshot where
  | selected (environments : List Env)
  | exhausted (state : Nat)
  | terminated (result : Nat)
  | poison (cause : FormalCause)
  | error (cause : ResolvingProbeError)
  deriving Repr, DecidableEq

private def selectionSnapshot :
    Except ResolvingProbeError (List Env) → ResolvingTraversalSnapshot
  | .ok environments => .selected environments
  | .error cause => .error cause

private def scanSnapshot :
    Except ResolvingProbeError (ComputationHavingScanResult Nat Nat) →
      ResolvingTraversalSnapshot
  | .ok (.exhausted state) => .exhausted state
  | .ok (.terminated result) => .terminated result
  | .ok (.poison cause) => .poison cause
  | .error cause => .error cause

/- The generated validation filter tests known truth with Boolean short-circuiting (spec/07 §3). -/
example :
    truthSnapshot
      (falseThenBadRead.evalTruthInResolving resolvingContext resolvingFrame) =
        .truth .fls := by
  native_decide

/- Computation retains its distinct left-to-right short circuit: clean false decides `And` before the structurally failing right leaf is reached. -/
example :
    computationSnapshot
      (falseThenBadRead.evalComputationInResolving resolvingContext
        resolvingFrame) = .computation .notTrue := by
  native_decide

/- A missing repetition binding is the same explicit structural channel, not semantic UNKNOWN. -/
example :
    truthSnapshot (
      (CorrelatedHaving.compareRepetitions .equal
        { origin := .inner, source := .repeatable nestedItems }
        { origin := .outer, source := .repeatable items }).evalTruthInResolving
          resolvingContext resolvingFrame) =
        .error (.binding (.missingBinding nestedItems)) := by
  native_decide

/- Validation selection evaluates every candidate in encounter order, retains earlier successes, and still reports a later structural read failure. -/
example :
    selectionSnapshot (
      trueResolvingHaving.selectEnvironmentsResolving orderedResolvingContext []
        [resolvingCandidate 1, resolvingCandidate 3]) =
      .error (.read marker.id) := by
  native_decide

/- Computation's one-kept-successor scan evaluates the successor before the current target, so a structural failure there wins before target consumption. -/
example :
    let consume : Nat → Env →
        Except ResolvingProbeError (Nat ⊕ Nat) :=
      fun _ _ => .ok (.inr 7)
    scanSnapshot (
      trueResolvingHaving.scanComputationResolving orderedResolvingContext []
        consume [resolvingCandidate 1, resolvingCandidate 3] 0) =
      .error (.read marker.id) := by
  native_decide

/- Once a good successor exists, a terminal current target hides every later filter and its structural failures. -/
example :
    let consume : Nat → Env →
        Except ResolvingProbeError (Nat ⊕ Nat) :=
      fun _ _ => .ok (.inr 7)
    scanSnapshot (
      trueResolvingHaving.scanComputationResolving orderedResolvingContext []
        consume
        [resolvingCandidate 1, resolvingCandidate 2, resolvingCandidate 3] 0) =
      .terminated 7 := by
  native_decide

/- The computation arm's read-order pair. The filter decides a candidate before its target is read,
   so a target the filter excludes is never consumed and whatever consuming it would have raised
   never surfaces. Only the context differs between these two cases, so the excluded candidate's own
   selection is the whole difference — the same shape as the validation arm's pair, and the
   consequence that makes the eager formal-operand inventory a report rather than an abort. -/

private def emptyResolvingCell : CheckedCell :=
  { rawPresent := false, parsed := none, findings := [] }

private def absentAtSecondContext :
    ResolvingCorrelationContext ResolvingProbeError where
  read environment field :=
    if environment == resolvingCandidate 2 && field == marker.id then
      .ok emptyResolvingCell
    else
      .ok resolvingCell
  unsupportedDateCalendar := .unsupportedDateCalendar
  temporalValueFailure := .temporalValueFailure
  worldUnavailable := .worldUnavailable
  storedTextUnavailable := .storedTextUnavailable
  typeValidityValueFailure := .typeValidityValueFailure
  groupUnavailable := .groupUnavailable
  bindingError := .binding

private def markerFilledHaving : CorrelatedHaving :=
  CorrelatedHaving.presence .filled { origin := .inner, field := marker.id }

private def failAtSecond : Nat → Env →
    Except ResolvingProbeError (Nat ⊕ Nat) :=
  fun count environment =>
    if environment == resolvingCandidate 2 then .error (.read marker.id)
    else .ok (.inl (count + 1))

/-- Candidate 2's filter operand is absent, so it is dropped and its failing target is unread. -/
example :
    scanSnapshot (
      markerFilledHaving.scanComputationResolving absentAtSecondContext []
        failAtSecond
        [resolvingCandidate 1, resolvingCandidate 2, resolvingCandidate 3] 0) =
      .exhausted 2 := by
  native_decide

/- The control needs a context whose reads all succeed. `resolvingContext` would fail the *filter*
   on every candidate, so the same expectation would hold for the wrong reason and establish
   nothing about the target. -/
private def allPresentContext :
    ResolvingCorrelationContext ResolvingProbeError where
  read _ _ := .ok resolvingCell
  unsupportedDateCalendar := .unsupportedDateCalendar
  temporalValueFailure := .temporalValueFailure
  worldUnavailable := .worldUnavailable
  storedTextUnavailable := .storedTextUnavailable
  typeValidityValueFailure := .typeValidityValueFailure
  groupUnavailable := .groupUnavailable
  bindingError := .binding

/-- With every operand present, candidate 2 is kept and the identical target failure surfaces. -/
example :
    scanSnapshot (
      markerFilledHaving.scanComputationResolving allPresentContext []
        failAtSecond
        [resolvingCandidate 1, resolvingCandidate 2, resolvingCandidate 3] 0) =
      .error (.read marker.id) := by
  native_decide

/- A filter's disjunction is **commutative on the validation arm and order-sensitive on the
   computation arm**, which is the same asymmetry stated twice. Validation evaluates both disjuncts
   into strong-Kleene truth, where a true one dominates an unavailable one from either side.
   Computation reads left to right and the first reached poison aborts, so a clean true on the left
   decides before the unavailable operand is read while the reverse spelling poisons. Both spellings
   are Kernel-retained on one document whose cells never change, so authored order is the whole
   difference. A tool that reorders disjuncts preserves validation and changes computation. -/

private def poisonedResolvingCell : CheckedCell :=
  { rawPresent := true, parsed := none, findings := [.malformed] }

private def markerPoisonedContext :
    ResolvingCorrelationContext ResolvingProbeError where
  read _ field :=
    if field == marker.id then .ok poisonedResolvingCell else .ok resolvingCell
  unsupportedDateCalendar := .unsupportedDateCalendar
  temporalValueFailure := .temporalValueFailure
  worldUnavailable := .worldUnavailable
  storedTextUnavailable := .storedTextUnavailable
  typeValidityValueFailure := .typeValidityValueFailure
  groupUnavailable := .groupUnavailable
  bindingError := .binding

private def poisonedThenFilled : CorrelatedHaving :=
  .or
    (CorrelatedHaving.presence .filled { origin := .inner, field := marker.id })
    (CorrelatedHaving.presence .filled { origin := .inner, field := payload.id })

private def filledThenPoisoned : CorrelatedHaving :=
  .or
    (CorrelatedHaving.presence .filled { origin := .inner, field := payload.id })
    (CorrelatedHaving.presence .filled { origin := .inner, field := marker.id })

/-- Validation keeps the candidate under **either** spelling: the filled disjunct dominates. -/
example :
    truthSnapshot (poisonedThenFilled.evalTruthInResolving markerPoisonedContext
      { innerEnv := resolvingCandidate 1, outerEnv := [] }) = .truth .tru := by
  native_decide

example :
    truthSnapshot (filledThenPoisoned.evalTruthInResolving markerPoisonedContext
      { innerEnv := resolvingCandidate 1, outerEnv := [] }) = .truth .tru := by
  native_decide

/-- Computation poisons when the unavailable operand is authored first. -/
example :
    computationSnapshot (poisonedThenFilled.evalComputationInResolving markerPoisonedContext
      { innerEnv := resolvingCandidate 1, outerEnv := [] }) =
      .computation (.poison .malformed) := by
  native_decide

/-- And holds when the clean true is authored first, because the right operand is never read. -/
example :
    computationSnapshot (filledThenPoisoned.evalComputationInResolving markerPoisonedContext
      { innerEnv := resolvingCandidate 1, outerEnv := [] }) = .computation .holds := by
  native_decide

/- The same asymmetry at the **other** connective, with the dominating operand's polarity flipped:
   a conjunction short-circuits on a *false* operand where a disjunction short-circuits on a true
   one. Locking only the `Or` pair above would leave the account consistent with a conjunction that
   evaluates both operands eagerly, which is the mistake a consumer reordering `And` operands would
   make. -/

private def poisonedAndEmptyContext :
    ResolvingCorrelationContext ResolvingProbeError where
  read _ field :=
    if field == marker.id then .ok poisonedResolvingCell
    else if field == payload.id then .ok emptyResolvingCell
    else .ok resolvingCell
  unsupportedDateCalendar := .unsupportedDateCalendar
  temporalValueFailure := .temporalValueFailure
  worldUnavailable := .worldUnavailable
  storedTextUnavailable := .storedTextUnavailable
  typeValidityValueFailure := .typeValidityValueFailure
  groupUnavailable := .groupUnavailable
  bindingError := .binding

private def falseThenPoisoned : CorrelatedHaving :=
  .and
    (CorrelatedHaving.presence .filled { origin := .inner, field := payload.id })
    (CorrelatedHaving.presence .filled { origin := .inner, field := marker.id })

private def poisonedThenFalse : CorrelatedHaving :=
  .and
    (CorrelatedHaving.presence .filled { origin := .inner, field := marker.id })
    (CorrelatedHaving.presence .filled { origin := .inner, field := payload.id })

/-- Validation drops the candidate under **either** spelling: the false conjunct dominates. -/
example :
    truthSnapshot (falseThenPoisoned.evalTruthInResolving poisonedAndEmptyContext
      { innerEnv := resolvingCandidate 1, outerEnv := [] }) = .truth .fls := by
  native_decide

example :
    truthSnapshot (poisonedThenFalse.evalTruthInResolving poisonedAndEmptyContext
      { innerEnv := resolvingCandidate 1, outerEnv := [] }) = .truth .fls := by
  native_decide

/-- Computation drops the candidate when the false operand is authored first, because the
    unavailable one is never read. -/
example :
    computationSnapshot (falseThenPoisoned.evalComputationInResolving poisonedAndEmptyContext
      { innerEnv := resolvingCandidate 1, outerEnv := [] }) = .computation .notTrue := by
  native_decide

/-- Reordering the same two operands poisons instead, so an operand swap that validation cannot
    observe changes the computation outcome. -/
example :
    computationSnapshot (poisonedThenFalse.evalComputationInResolving poisonedAndEmptyContext
      { innerEnv := resolvingCandidate 1, outerEnv := [] }) =
      .computation (.poison .malformed) := by
  native_decide

/- Both newer leaves at **outer** origin read the captured environment, not the candidate. The
   kernel run that established this was authored against exactly this wiring, and a candidate-origin
   mis-wiring would pass every other case in this family, because every one of them binds the same
   row on both sides. Each pair below fills the field on one side only, so the origin is the whole
   difference. -/

private def outerOnlyContext :
    ResolvingCorrelationContext ResolvingProbeError where
  read environment field :=
    if field == marker.id then
      .ok (if environment == resolvingCandidate 9 then resolvingCell else emptyResolvingCell)
    else
      .ok resolvingCell
  unsupportedDateCalendar := .unsupportedDateCalendar
  temporalValueFailure := .temporalValueFailure
  worldUnavailable := .worldUnavailable
  storedTextUnavailable := .storedTextUnavailable
  typeValidityValueFailure := .typeValidityValueFailure
  groupUnavailable := .groupUnavailable
  bindingError := .binding

private def presenceAt (origin : HavingOrigin) : CorrelatedHaving :=
  CorrelatedHaving.presence .filled { origin, field := marker.id }

private def stringAt (origin : HavingOrigin) : CorrelatedHaving :=
  CorrelatedHaving.compareStringLiteral .equal
    { origin, operand := .string { id := marker.id } } "K"

/-- Candidate row 1's operand is empty and captured row 9's is filled, so only the outer-origin
    presence leaf holds. -/
example :
    truthSnapshot ((presenceAt .outer).evalTruthInResolving outerOnlyContext
      { innerEnv := resolvingCandidate 1, outerEnv := resolvingCandidate 9 }) =
      .truth .tru := by
  native_decide

example :
    truthSnapshot ((presenceAt .inner).evalTruthInResolving outerOnlyContext
      { innerEnv := resolvingCandidate 1, outerEnv := resolvingCandidate 9 }) =
      .truth .fls := by
  native_decide

/-- The String leaf routes its origin the same way: only the captured row carries the matching text,
    so the equality holds at outer origin and not at inner. -/
private def textOnOuterContext :
    ResolvingCorrelationContext ResolvingProbeError where
  read environment field :=
    if field == marker.id && environment == resolvingCandidate 9 then
      .ok { rawPresent := true, parsed := some (.str "K"), findings := [] }
    else if field == marker.id then
      .ok { rawPresent := true, parsed := some (.str "X"), findings := [] }
    else
      .ok resolvingCell
  unsupportedDateCalendar := .unsupportedDateCalendar
  temporalValueFailure := .temporalValueFailure
  worldUnavailable := .worldUnavailable
  storedTextUnavailable := .storedTextUnavailable
  typeValidityValueFailure := .typeValidityValueFailure
  groupUnavailable := .groupUnavailable
  bindingError := .binding

example :
    truthSnapshot ((stringAt .outer).evalTruthInResolving textOnOuterContext
      { innerEnv := resolvingCandidate 1, outerEnv := resolvingCandidate 9 }) =
      .truth .tru := by
  native_decide

example :
    truthSnapshot ((stringAt .inner).evalTruthInResolving textOnOuterContext
      { innerEnv := resolvingCandidate 1, outerEnv := resolvingCandidate 9 }) =
      .truth .fls := by
  native_decide

/- The String-equality leaf on the computation arm. An **absent** operand suppresses the comparison
   into an ordinary non-truth rather than poisoning, which is the branch that separates suppression
   from unavailability on this arm: only the latter aborts. Kernel-retained on the same channel that
   measured the presence leaf, where a filter naming an absent String drops its row and the
   aggregate still computes. A formally unavailable String stays unmeasured — the poison branch here
   is this theory's account, shared with every other checked String consumer. -/

private def stringHaving (expected : String) : CorrelatedHaving :=
  CorrelatedHaving.compareStringLiteral .equal
    { origin := .inner, operand := .string { id := marker.id } } expected

private def textCell (value : String) : CheckedCell :=
  { rawPresent := true, parsed := some (.str value), findings := [] }

private def stringContext (cell : CheckedCell) :
    ResolvingCorrelationContext ResolvingProbeError where
  read _ field := if field == marker.id then .ok cell else .ok resolvingCell
  unsupportedDateCalendar := .unsupportedDateCalendar
  temporalValueFailure := .temporalValueFailure
  worldUnavailable := .worldUnavailable
  storedTextUnavailable := .storedTextUnavailable
  typeValidityValueFailure := .typeValidityValueFailure
  groupUnavailable := .groupUnavailable
  bindingError := .binding

example :
    computationSnapshot ((stringHaving "K").evalComputationInResolving
      (stringContext (textCell "K"))
      { innerEnv := resolvingCandidate 1, outerEnv := [] }) = .computation .holds := by
  native_decide

example :
    computationSnapshot ((stringHaving "K").evalComputationInResolving
      (stringContext (textCell "X"))
      { innerEnv := resolvingCandidate 1, outerEnv := [] }) = .computation .notTrue := by
  native_decide

/-- The absent operand: non-true, **not** poison, so the enclosing aggregate stays computable. -/
example :
    computationSnapshot ((stringHaving "K").evalComputationInResolving
      (stringContext emptyResolvingCell)
      { innerEnv := resolvingCandidate 1, outerEnv := [] }) = .computation .notTrue := by
  native_decide

/- `FieldNotFilled` on the computation arm. The negative polarity is a genuine predicate rather than
   a negation of the positive one, so it needs its own rows here: it holds on a clean empty cell and
   poisons on an unavailable one, which is where a Boolean negation of the positive leaf would
   instead answer "holds". Internal only — the measured computation-arm rows use `FieldFilled`. -/

example :
    computationSnapshot ((CorrelatedHaving.presence .notFilled
        { origin := .inner, field := marker.id }).evalComputationInResolving
      (stringContext emptyResolvingCell)
      { innerEnv := resolvingCandidate 1, outerEnv := [] }) = .computation .holds := by
  native_decide

example :
    computationSnapshot ((CorrelatedHaving.presence .notFilled
        { origin := .inner, field := marker.id }).evalComputationInResolving
      (stringContext (textCell "K"))
      { innerEnv := resolvingCandidate 1, outerEnv := [] }) = .computation .notTrue := by
  native_decide

/-- The separator against a negated positive leaf: both polarities **poison** on an unavailable
    operand, so neither is the other's complement there. -/
example :
    computationSnapshot ((CorrelatedHaving.presence .notFilled
        { origin := .inner, field := marker.id }).evalComputationInResolving
      (stringContext poisonedResolvingCell)
      { innerEnv := resolvingCandidate 1, outerEnv := [] }) =
      .computation (.poison .malformed) := by
  native_decide

/-- The nearest contrast, and the reason the row above is worth locking: an *unavailable* operand
    does poison. This arm is internal — no measurement reaches a formally invalid String here. -/
example :
    computationSnapshot ((stringHaving "K").evalComputationInResolving
      (stringContext poisonedResolvingCell)
      { innerEnv := resolvingCandidate 1, outerEnv := [] }) =
      .computation (.poison .malformed) := by
  native_decide


private def storageContext : CorrelationContext := {
  read := fun _ _ => resolvingCell
  storedText := fun env field => if field == payload.id then
    some (if env == resolvingCandidate 1 then "candidate spelling" else "captured spelling") else none }

example : storageContext.asResolving.storedText (resolvingCandidate 1) payload.id = some "candidate spelling" ∧
    storageContext.asResolving.storedText (resolvingCandidate 2) payload.id = some "captured spelling" ∧
    storageContext.asResolving.storedTextUnavailable payload.id = .storedTextUnavailable payload.id := by native_decide

private def numericStorageContext : NumericComputationEvaluationContext := {
  scalar := {
    read := fun _ => resolvingCell
    addressed := some {
      document := { instantiatedRows := [], rawCells := fun _ => some "backing spelling" }
      read := fun _ _ => resolvingCell
      storedText := fun _ _ => some "backing spelling" } }
  document := { instantiatedRows := [], rawCells := fun _ => some "backing spelling" }
  outer := []
  filterRead := fun _ _ => resolvingCell
  filterStoredText := fun _ _ => some "filter spelling"
  starRead := fun _ _ => resolvingCell
  starStoredText := fun _ _ => some "current spelling" }

example : (numericStorageContext.scalarContext { fields := [] }).addressed.bind (fun view => view.storedText [] payload.id) =
      some "current spelling" ∧
    ({ numericStorageContext with starStoredText := fun _ _ => none }.scalarContext { fields := [] }).addressed.bind
      (fun view => view.storedText [] payload.id) = none ∧
    NumericComputationFault.isFilterValueFailure (.repeatableAddressing (.storedTextUnavailable payload.id)) = false := by
  native_decide

end A12Kernel.Conformance.CorrelationResolving
