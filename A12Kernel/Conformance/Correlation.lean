import A12Kernel.Semantics.Correlation

/-! # Captured outer-correlation conformance locks -/

namespace A12Kernel.Conformance.Correlation

open A12Kernel

private def items : RepeatableLevel := 10

private def count : FlatNumberField :=
  { id := 0, info := { scale := 0, signed := false } }

private def payload : FlatNumberField :=
  { id := 1, info := { scale := 0, signed := false } }

private def marker : FlatNumberField :=
  { id := 2, info := { scale := 0, signed := false } }

private def checkedNumber : RawCell → CheckedCell :=
  formalCheck { kind := .number count.info }

private def number (value : Rat) : RawCell :=
  .parsed (.num value)

private def rawContextOf (values : List RawCell) : SingleGroupValidationContext where
  group := items
  candidates := (List.range values.length).map (· + 1)
  read row fieldId :=
    if fieldId != count.id then checkedNumber .empty
    else match values[row - 1]? with
      | some value => checkedNumber value
      | none => checkedNumber .empty

private def contextOf (values : List Rat) : SingleGroupValidationContext :=
  rawContextOf (values.map fun value => .parsed (.num value))

private def distinct : SingleGroupValidationContext :=
  contextOf [5, 6, 9]

private def duplicates : SingleGroupValidationContext :=
  contextOf [5, 5, 9]

private def emptyAndZero : SingleGroupValidationContext :=
  rawContextOf [.empty, .parsed (.num 0)]

private def malformedSecond : SingleGroupValidationContext :=
  rawContextOf [.parsed (.num 5), .rejected .malformed]

private def correlatedConsumerContext
    (rows : List (RawCell × RawCell)) : SingleGroupValidationContext where
  group := items
  candidates := (List.range rows.length).map (· + 1)
  read row fieldId :=
    if fieldId == count.id then
      match rows[row - 1]? with
      | some (key, _) => checkedNumber key
      | none => checkedNumber .empty
    else if fieldId == payload.id then
      match rows[row - 1]? with
      | some (_, value) => checkedNumber value
      | none => checkedNumber .empty
    else if fieldId == marker.id then
      checkedNumber (.parsed (.num 1))
    else
      checkedNumber .empty

private def malformedFirstConsumer : SingleGroupValidationContext :=
  correlatedConsumerContext [
    (number 5, .rejected .malformed), (number 5, number 9)]

private def malformedSecondConsumer : SingleGroupValidationContext :=
  correlatedConsumerContext [
    (number 5, number 9), (number 5, .rejected .malformed)]

private def validConsumers : SingleGroupValidationContext :=
  correlatedConsumerContext [
    (number 5, number 8), (number 5, number 9)]

private def distinctConsumerKeys : SingleGroupValidationContext :=
  correlatedConsumerContext [
    (number 5, number 8), (number 6, number 9)]

private def mixedConsumers : SingleGroupValidationContext :=
  correlatedConsumerContext [
    (number 5, .rejected .malformed),
    (number 5, number 9),
    (number 5, number 10)]

private def emptyZeroFilterKeys : SingleGroupValidationContext :=
  correlatedConsumerContext [
    (.empty, number 8),
    (number 0, number 9)]

private def malformedFilterKeys : SingleGroupValidationContext :=
  correlatedConsumerContext [
    (.rejected .malformed, number 8),
    (number 5, number 9),
    (number 5, number 10)]

private def numericNotEqualRows : SingleGroupValidationContext :=
  correlatedConsumerContext [
    (number 5, .empty),
    (number 5, .empty),
    (number 9, number 10)]

private def repetitionEqualRows : SingleGroupValidationContext :=
  correlatedConsumerContext [
    (number 1, .empty),
    (number 2, number 9)]

private def repetitionLessRows : SingleGroupValidationContext :=
  correlatedConsumerContext [
    (number 1, number 8),
    (number 2, number 9),
    (number 3, number 10)]

private def emptyFirstMarker : SingleGroupValidationContext :=
  { validConsumers with read := fun row fieldId =>
      if row == 1 && fieldId == marker.id then checkedNumber .empty
      else validConsumers.read row fieldId }

private def innerCount : HavingNumberRef :=
  { origin := .inner, field := count }

private def outerCount : HavingNumberRef :=
  { origin := .outer, field := count }

private def repetition (origin : HavingOrigin) : HavingRepetitionRef :=
  { origin, level := items }

private def checkedHaving (condition : CorrelatedHaving)
    (inner : condition.usesInner = true) (outer : condition.usesOuter = true) :
    OriginCheckedCorrelatedHaving :=
  { condition, usesInner := inner, usesOuter := outer }

private def selfIncluded : SingleCorrelatedStar :=
  { valueField := count
    having := checkedHaving
      (.compareNumbers .equal innerCount outerCount) (by decide) (by decide) }

private def selfExcluded : SingleCorrelatedStar :=
  { valueField := count
    having := checkedHaving
      (.and
        (CorrelatedHaving.compareRepetitions .notEqual
          (repetition .inner) (repetition .outer))
        (CorrelatedHaving.compareNumbers .equal innerCount outerCount))
      (by decide) (by decide) }

private def selfExcludedPayload : SingleCorrelatedStar :=
  { valueField := payload, having := selfExcluded.having }

private def numberNotEqualPayload : SingleCorrelatedStar :=
  { valueField := payload
    having := checkedHaving
      (.compareNumbers .notEqual innerCount outerCount) (by decide) (by decide) }

private def repetitionEqualPayload : SingleCorrelatedStar :=
  { valueField := payload
    having := checkedHaving
      (.compareRepetitions .equal (repetition .inner) (repetition .outer))
      (by decide) (by decide) }

private def repetitionLessPayload : SingleCorrelatedStar :=
  { valueField := payload
    having := checkedHaving
      (.compareRepetitions .lessThan (repetition .inner) (repetition .outer))
      (by decide) (by decide) }

private def smallerInner : SingleCorrelatedStar :=
  { valueField := count
    having := checkedHaving
      (.compareNumbers .lessThan innerCount outerCount) (by decide) (by decide) }

private def smallerOrEqualInner : SingleCorrelatedStar :=
  { valueField := count
    having := checkedHaving
      (.or
        (CorrelatedHaving.compareNumbers .lessThan innerCount outerCount)
        (CorrelatedHaving.compareNumbers .equal innerCount outerCount))
      (by decide) (by decide) }

private def captured (rows : SingleGroupValidationContext) (outerRow : RowIndex) :
    CapturedSingleGroupContext :=
  { rows, outerRow }

private def checkError : Except CorrelationCheckError OriginCheckedCorrelatedHaving →
    Option CorrelationCheckError
  | .ok _ => none
  | .error error => some error

example : distinct.WellFormed := by
  native_decide

example : ¬({ distinct with candidates := [0] }).WellFormed := by
  native_decide

example : ¬({ distinct with candidates := [1, 1] }).WellFormed := by
  native_decide

example : selfIncluded.select (captured distinct 1) = [1] := by
  native_decide

example : selfIncluded.select (captured distinct 2) = [2] := by
  native_decide

example : selfIncluded.firingRows distinct = [1, 2, 3] := by
  native_decide

/-- Numeric comparison resolves empty to zero, so the empty row matches itself and the
    explicitly stored zero row at the filter boundary. -/
example : selfIncluded.select (captured emptyAndZero 1) = [1, 2] := by
  native_decide

/-- A malformed inner operand is unknown and therefore is not selected. -/
example : selfIncluded.select (captured malformedSecond 1) = [1] := by
  native_decide

/-- A malformed outer operand makes every comparison unknown, so no candidate is kept. -/
example : selfIncluded.select (captured malformedSecond 2) = [] := by
  native_decide

/-- Computation traversal locates the first kept row, then evaluates enough filters to
    prefetch its successor before yielding that row to the consuming operation. -/
example :
    selfIncluded.having.condition.scanComputation
        malformedSecond.asCorrelationContext
        (malformedSecond.envAt 1)
        (fun count _ => .inl (count + 1))
        (malformedSecond.candidates.map malformedSecond.envAt) 0 =
      (ComputationHavingScanResult.poison .malformed :
        ComputationHavingScanResult Nat Nat) := by
  native_decide

/-- Self-exclusion is authored, not inferred by the evaluator. -/
example : selfIncluded.select (captured distinct 2) ≠ [] := by
  native_decide

example : selfExcluded.firingRows distinct = [] := by
  native_decide

example : selfExcluded.select (captured duplicates 1) = [2] := by
  native_decide

example : selfExcluded.select (captured duplicates 2) = [1] := by
  native_decide

example : selfExcluded.select (captured duplicates 3) = [] := by
  native_decide

example : selfExcluded.firingRows duplicates = [1, 2] := by
  native_decide

/-- Row 1's malformed consumed value is outside its self-excluded selection; row 2's
    valid value is selected, so the guarded quantifier fires. -/
example :
    selfExcludedPayload.evalGuardedAnyFilledOn marker
      (captured malformedFirstConsumer 1) = .tru := by
  native_decide

/-- From row 2, the same malformed value is selected and makes the consumer unknown. -/
example :
    selfExcludedPayload.evalGuardedAnyFilledOn marker
      (captured malformedFirstConsumer 2) = .unknown := by
  native_decide

example :
    selfExcludedPayload.firingRowsOn marker malformedFirstConsumer = [1] := by
  native_decide

/-- Swapping only which consumed row is malformed mirrors the firing row. -/
example :
    selfExcludedPayload.firingRowsOn marker malformedSecondConsumer = [2] := by
  native_decide

example :
    selfExcludedPayload.firingRowsOn marker validConsumers = [1, 2] := by
  native_decide

/-- Empty Number filter keys compare as zero at both origins. Self-exclusion leaves the
    other row selected in each direction. -/
example :
    selfExcludedPayload.select (captured emptyZeroFilterKeys 1) = [2] ∧
    selfExcludedPayload.select (captured emptyZeroFilterKeys 2) = [1] ∧
    selfExcludedPayload.firingRowsOn marker emptyZeroFilterKeys = [1, 2] := by
  native_decide

/-- A malformed outer key selects nothing; as an inner key it drops locally while the
    two valid duplicate keys continue to select each other. -/
example :
    selfExcludedPayload.select (captured malformedFilterKeys 1) = [] ∧
    selfExcludedPayload.select (captured malformedFilterKeys 2) = [3] ∧
    selfExcludedPayload.select (captured malformedFilterKeys 3) = [2] ∧
    selfExcludedPayload.firingRowsOn marker malformedFilterKeys = [2, 3] := by
  native_decide

/-- Numeric inequality is separated from equality by putting the only filled consumer
    on the distinct-key row. -/
example :
    numberNotEqualPayload.select (captured numericNotEqualRows 1) = [3] ∧
    numberNotEqualPayload.select (captured numericNotEqualRows 2) = [3] ∧
    numberNotEqualPayload.select (captured numericNotEqualRows 3) = [1, 2] ∧
    numberNotEqualPayload.firingRowsOn marker numericNotEqualRows = [1, 2] := by
  native_decide

/-- Structural repetition equality selects only the captured row. -/
example :
    repetitionEqualPayload.select (captured repetitionEqualRows 1) = [1] ∧
    repetitionEqualPayload.select (captured repetitionEqualRows 2) = [2] ∧
    repetitionEqualPayload.firingRowsOn marker repetitionEqualRows = [2] := by
  native_decide

/-- Inner repetition less-than outer repetition selects ordered predecessors. -/
example :
    repetitionLessPayload.select (captured repetitionLessRows 1) = [] ∧
    repetitionLessPayload.select (captured repetitionLessRows 2) = [1] ∧
    repetitionLessPayload.select (captured repetitionLessRows 3) = [1, 2] ∧
    repetitionLessPayload.firingRowsOn marker repetitionLessRows = [2, 3] := by
  native_decide

/-- On a one-sided malformed operand, numeric inequality is not Boolean negation of
    equality: both comparisons are unknown. Whether the malformed key is inner or
    outer, neither comparison keeps the affected candidate. -/
example :
    let equal : CorrelatedHaving := .compareNumbers .equal innerCount outerCount
    let notEqual : CorrelatedHaving := .compareNumbers .notEqual innerCount outerCount
    let innerMalformed : SingleGroupFilterFrame := { innerRow := 1, outerRow := 2 }
    let outerMalformed : SingleGroupFilterFrame := { innerRow := 2, outerRow := 1 }
    equal.evalTruth malformedFilterKeys innerMalformed = .unknown ∧
    notEqual.evalTruth malformedFilterKeys innerMalformed = .unknown ∧
    equal.evalTruth malformedFilterKeys outerMalformed = .unknown ∧
    notEqual.evalTruth malformedFilterKeys outerMalformed = .unknown ∧
    selfIncluded.keeps (captured malformedFilterKeys 2) 1 = false ∧
    numberNotEqualPayload.keeps (captured malformedFilterKeys 2) 1 = false ∧
    selfIncluded.select (captured malformedFilterKeys 1) = [] ∧
    numberNotEqualPayload.select (captured malformedFilterKeys 1) = [] := by
  native_decide

/-- A selected valid cell satisfies the existential consumer even when another selected
    cell is malformed; kept invalidity is not global poison for this operator. -/
example :
    selfExcludedPayload.evalGuardedAnyFilledOn marker
      (captured mixedConsumers 3) = .tru := by
  native_decide

/-- Selection stability is load-bearing in the footprint theorem. The left selected
    consumer premise would be vacuous, yet changing only the filter keys changes the
    selection and the result. -/
example :
    selfExcludedPayload.select (captured distinctConsumerKeys 1) = [] ∧
    selfExcludedPayload.select (captured validConsumers 1) = [2] ∧
    selfExcludedPayload.evalGuardedAnyFilledOn marker
        (captured distinctConsumerKeys 1) = .fls ∧
    selfExcludedPayload.evalGuardedAnyFilledOn marker
        (captured validConsumers 1) = .tru := by
  native_decide

/-- Guard-observation agreement is also load-bearing when selection and selected
    consumer cells are identical. -/
example :
    selfExcludedPayload.select (captured emptyFirstMarker 1) =
        selfExcludedPayload.select (captured validConsumers 1) ∧
    selfExcludedPayload.evalGuardedAnyFilledOn marker
        (captured emptyFirstMarker 1) = .fls ∧
    selfExcludedPayload.evalGuardedAnyFilledOn marker
        (captured validConsumers 1) = .tru := by
  native_decide

/-- This asymmetric case distinguishes inner/outer routing from reversal or collapse. -/
example : smallerInner.select (captured distinct 1) = [] := by
  native_decide

example : smallerInner.select (captured distinct 2) = [1] := by
  native_decide

example : smallerInner.select (captured distinct 3) = [1, 2] := by
  native_decide

/- Correlated filters reuse the shared connective tree: `Or` retains both the ordered predecessor and reflexive branches. -/
example : smallerOrEqualInner.select (captured distinct 2) = [1, 2] := by
  native_decide

example : smallerInner.firingRows distinct = [2, 3] := by
  native_decide

example :
    checkError (CorrelatedHaving.compareNumbers .equal outerCount outerCount).check =
      some .missingInner := by
  decide

example :
    checkError (CorrelatedHaving.compareNumbers .equal innerCount innerCount).check =
      some .missingOuter := by
  decide

private def nestedItems : RepeatableLevel := 20

private inductive ResolvingProbeError where
  | read (field : FieldId)
  | binding (cause : EnvBindingError)
  deriving Repr, DecidableEq

private def resolvingCell : CheckedCell :=
  { rawPresent := true, parsed := some (.num 1), findings := [] }

private def resolvingContext :
    ResolvingCorrelationContext ResolvingProbeError where
  read _ field :=
    if field == marker.id then .error (.read field) else .ok resolvingCell
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

/- Validation's strong-Kleene connective still reaches the right leaf, so structural failure cannot be collapsed into UNKNOWN or hidden by a false left truth. -/
example :
    truthSnapshot
      (falseThenBadRead.evalTruthInResolving resolvingContext resolvingFrame) =
        .error (.read marker.id) := by
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
        { origin := .inner, level := nestedItems }
        { origin := .outer, level := items }).evalTruthInResolving
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
  bindingError := .binding

private def presenceAt (origin : HavingOrigin) : CorrelatedHaving :=
  CorrelatedHaving.presence .filled { origin, field := marker.id }

private def stringAt (origin : HavingOrigin) : CorrelatedHaving :=
  CorrelatedHaving.compareStringLiteral .equal
    { origin, field := { id := marker.id } } "K"

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
    { origin := .inner, field := { id := marker.id } } expected

private def textCell (value : String) : CheckedCell :=
  { rawPresent := true, parsed := some (.str value), findings := [] }

private def stringContext (cell : CheckedCell) :
    ResolvingCorrelationContext ResolvingProbeError where
  read _ field := if field == marker.id then .ok cell else .ok resolvingCell
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

end A12Kernel.Conformance.Correlation
