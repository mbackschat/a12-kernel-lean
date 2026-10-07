import A12Kernel.Semantics.Correlation

/-! # Captured outer-correlation conformance locks -/

namespace A12Kernel.Conformance.Correlation

local instance [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .ok a, .ok b => decidable_of_iff (a = b) (by simp)
  | .error a, .error b => decidable_of_iff (a = b) (by simp)
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

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
  { origin, source := .repeatable items }

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
      (.ok (ComputationHavingScanResult.poison .malformed) :
        Except CorrelationRuntimeFault (ComputationHavingScanResult Nat Nat)) := by
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

/- The `CurrentRepetition` self-exclusion idiom at runtime, as a **complement pair**. The two
   polarities partition the candidate set, and their counts sum to the unfiltered one — which is the
   form that refutes both wrong accounts at once. An implicit self-exclusion makes the reflexive
   spelling keep nothing; a marker-blind reading, comparing each candidate against itself, makes the
   inequality keep nothing and the equality keep everything. Kernel-retained: the inequality's
   count varies with *which* row is excluded, so no self-exclusion-blind account produces it. -/

private def selfExcludedOnly : SingleCorrelatedStar :=
  { valueField := count
    having := checkedHaving
      (.compareRepetitions .notEqual (repetition .inner) (repetition .outer))
      (by decide) (by decide) }

example :
    (List.range 3).map (fun index =>
        selfExcludedOnly.select (captured distinct (index + 1)))
      = [[2, 3], [1, 3], [1, 2]] := by
  native_decide

/-- Self-exclusion **nested under a disjunction** whose other disjunct is false on every candidate,
built from repetition comparisons so no new fixture is needed: `inner = inner` is true everywhere and
`inner < inner` is false everywhere. -/
private def selfExcludedNested : SingleCorrelatedStar :=
  { valueField := count
    having := checkedHaving
      (.and
        (CorrelatedHaving.compareRepetitions .equal
          (repetition .inner) (repetition .inner))
        (.or
          (CorrelatedHaving.compareRepetitions .notEqual
            (repetition .inner) (repetition .outer))
          (CorrelatedHaving.compareRepetitions .lessThan
            (repetition .inner) (repetition .inner))))
      (by decide) (by decide) }

/-- Nesting it changes nothing, which is the claim: the exclusion still tracks the **evaluating** row
    rather than a fixed one. Kernel-retained per row at a12-dmkits `eded8263`, where three rules over
    values `1, 2, 4` fire `6`, `5`, `3` at rows 1, 2, 3 and the no-exclusion rung `7` stays silent —
    distinct powers, so a fixed wrong exclusion would have fired one rung at every row. -/
example :
    (List.range 3).map (fun index =>
        selfExcludedNested.select (captured distinct (index + 1)))
      = [[2, 3], [1, 3], [1, 2]] := by
  native_decide

/-- The reflexive spelling keeps exactly the captured row, and the two selections partition the
    candidates on every outer row. The existing `repetitionEqualPayload` supplies the equality:
    selection does not depend on the value field, so no second fixture is warranted. -/
example : ∀ outerRow ∈ distinct.candidates,
    (selfExcludedOnly.select (captured distinct outerRow)).length
        + (repetitionEqualPayload.select (captured distinct outerRow)).length
      = distinct.candidates.length := by
  native_decide

/- A **correlated** filter feeding a per-row computed target, at exact per-row values rather than
   ladder thresholds. Neither arm can diverge on these documents because no cell is unavailable, so
   one sum stands for both; the arms' divergence has its own cases above. The reversed reading of
   `$` — marked as candidate, unmarked as captured — predicts `[0, 10, 30]` on the ascending keys
   and `[50, 0, 20]` on the rotated ones, so each document refutes it on its own rather than by
   agreeing with the other. -/

private def correlatedGreater : SingleCorrelatedStar :=
  { valueField := payload
    having := checkedHaving
      (.compareNumbers .lessThan outerCount innerCount) (by decide) (by decide) }

private def ascendingKeys : SingleGroupValidationContext :=
  correlatedConsumerContext [
    (number 1, number 10), (number 2, number 20), (number 3, number 30)]

private def rotatedKeys : SingleGroupValidationContext :=
  correlatedConsumerContext [
    (number 3, number 10), (number 1, number 20), (number 2, number 30)]

example :
    (List.range 3).map (fun index =>
        NumberFold.sumRows ascendingKeys payload
          (correlatedGreater.select (captured ascendingKeys (index + 1))))
      = [.value 50, .value 30, .value 0] := by
  native_decide

example :
    (List.range 3).map (fun index =>
        NumberFold.sumRows rotatedKeys payload
          (correlatedGreater.select (captured rotatedKeys (index + 1))))
      = [.value 0, .value 40, .value 10] := by
  native_decide

/-- An all-dropped correlated selection folds an available zero rather than clearing, which is the
    same answer the unfiltered fold gives an empty row set. -/
example :
    NumberFold.sumRows ascendingKeys payload
        (correlatedGreater.select (captured ascendingKeys 3)) = .value 0 := by
  native_decide

/-! ## A filter that cannot see the candidate is all-or-nothing

Measured on the Kernel at both carriers a non-reopened level can take: an above-the-star reference
on the operand's own path is constant within one host row, and a nonrepeatable leaf is constant
across the whole document ([checkpoint](../../docs/SOURCES.md#src-filter-reference-level-runtime)).
Three `Items` rows under one host row therefore all pass together or all fail together, and the
Kernel's own numbers were `30, 0, 50` against `30, 70, 50` on the same three rows — the middle cell
is the separator, identical candidates under two filters. Both filters below reference only the
captured environment, which is what makes them candidate-invariant. -/

private def hostEnv : Env := [(items, 2)]

private def candidateEnvs : List Env := [[(items, 1)], [(items, 2)], [(items, 3)]]

private def capturedOnly (op : CorrelationComparisonOp) : CorrelatedHaving :=
  CorrelatedHaving.compareRepetitions op
    { origin := .outer, source := .repeatable items } { origin := .outer, source := .repeatable items }

/-- The satisfied filter keeps **every** candidate, which is the host row whose gate holds. -/
example :
    (capturedOnly .equal).selectEnvironments distinct.asCorrelationContext hostEnv
      candidateEnvs = candidateEnvs := by
  native_decide

/-- The unsatisfied one keeps **none**, which is the sibling host row whose gate does not — and it
    is the same three candidates, so the difference is the filter and not the data. -/
example :
    (capturedOnly .lessThan).selectEnvironments distinct.asCorrelationContext hostEnv
      candidateEnvs = [] := by
  native_decide

/-- The law's hypothesis is discharged concretely, so
    `correlatedHaving_selectEnvironments_all_or_none` is not vacuous here: truth at
    this filter does not move when the candidate does. -/
example :
    ∀ first second : Env,
      (capturedOnly .equal).evalTruthIn distinct.asCorrelationContext
          { innerEnv := first, outerEnv := hostEnv }
        = (capturedOnly .equal).evalTruthIn distinct.asCorrelationContext
          { innerEnv := second, outerEnv := hostEnv } := by
  intro first second
  rfl


end A12Kernel.Conformance.Correlation
