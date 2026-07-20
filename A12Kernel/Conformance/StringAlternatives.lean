import A12Kernel.Semantics.StringAlternatives

/-! # Resolved String-alternative executable locks

These cases compose the existing first-match selector with one already-resolved String target. They distinguish selection from a wrong scan that resumes after the selected operation produces no value, poison, or target rejection.
-/

namespace A12Kernel.Conformance.StringAlternatives

open A12Kernel

private def valueOf : Except ε α → Option α
  | .ok value => some value
  | .error _ => none

private def probeId : FieldId := 0
private def sourceId : FieldId := 1
private def poisonId : FieldId := 2
private def targetId : FieldId := 3

private def checkedString (raw : RawCell) : CheckedCell :=
  formalCheck { kind := .string } raw

private def context (source poison : RawCell) : StringComputationContext where
  read field :=
    if field == probeId then checkedString .empty
    else if field == sourceId then checkedString source
    else if field == poisonId then checkedString poison
    else checkedString .empty

private def holding : ComputationCondition := .fieldNotFilled probeId
private def notHolding : ComputationCondition := .fieldFilled probeId
private def poisonedGuard : ComputationCondition := .fieldFilled poisonId

private def alternative (precondition : ComputationCondition)
    (operation : StringExpr) : ComputationAlternative StringExpr where
  precondition := precondition
  operation := operation

private def computation (alternatives : List (ComputationAlternative StringExpr))
    (policy : StringTargetLengthPolicy := .unconstrained)
    (prior : PriorStringTarget := .empty) : StringAlternativeComputation where
  targetField := targetId
  alternatives := alternatives
  targetPolicy := policy
  prior := prior

private def storedSeed : StoredString := ⟨"SEED", by decide⟩
private def storedFallback : StoredString := ⟨"FALLBACK", by decide⟩
private def storedAbcd : StoredString := ⟨"ABCD", by decide⟩
private def maxThree : StringTargetLengthPolicy := .maximum ⟨3, by decide⟩

/- The first holding operation ends the scan even though its empty field copy produces no value. -/
example :
    valueOf ((computation
      [alternative holding (.field sourceId),
       alternative holding (.literal "FALLBACK")]
      .unconstrained (.filled storedSeed)).evaluate (context .empty .empty)) =
        some { outcome := .noValue, delta := some .cleared } := by
  native_decide

/- Removing that selected empty operation exposes the later literal, so outcome-driven fallback is observably wrong. -/
example :
    valueOf ((computation
      [alternative holding (.literal "FALLBACK")]).evaluate (context .empty .empty)) =
        some { outcome := .accepted storedFallback,
               delta := some (.value storedFallback) } := by
  native_decide

/- A clean non-match still falls through before any operation is selected. -/
example :
    valueOf ((computation
      [alternative notHolding (.field sourceId),
       alternative holding (.literal "FALLBACK")]).evaluate (context .empty .empty)) =
        some { outcome := .accepted storedFallback,
               delta := some (.value storedFallback) } := by
  native_decide

/- Exhausting a nonempty table through clean nonmatches produces no value and clears a stale target. -/
example :
    valueOf ((computation
      [alternative notHolding (.literal "IGNORED"),
       alternative notHolding (.literal "ALSO_IGNORED")]
      .unconstrained (.filled storedSeed)).evaluate (context .empty .empty)) =
        some { outcome := .noValue, delta := some .cleared } := by
  native_decide

/- A selected target rejection is terminal; a later acceptable literal is not tried. -/
example :
    valueOf ((computation
      [alternative holding (.literal "ABCD"),
       alternative holding (.literal "OK")]
      maxThree).evaluate (context .empty .empty)) =
        some { outcome := .errored storedAbcd .tooLong,
               delta := some (.errored storedAbcd .tooLong) } := by
  native_decide

/- Poison while selecting aborts before the later holding alternative. -/
example :
    valueOf ((computation
      [alternative poisonedGuard (.literal "IGNORED"),
       alternative holding (.literal "FALLBACK")]).evaluate
        (context .empty (.rejected .malformed))) =
          some { outcome := .poison .malformed, delta := none } := by
  native_decide

/- Poison from the selected operation is also terminal and clears a stale target. -/
example :
    valueOf ((computation
      [alternative holding (.field sourceId),
       alternative holding (.literal "FALLBACK")]
      .unconstrained (.filled storedSeed)).evaluate
        (context (.rejected .declaredConstraint) .empty)) =
          some { outcome := .poison .declaredConstraint,
                 delta := some .cleared } := by
  native_decide

/- The total empty-list route is clean no-match; authoring legality remains a separate boundary. -/
example :
    valueOf ((computation [] .unconstrained (.filled storedSeed)).evaluate
      (context .empty .empty)) =
        some { outcome := .noValue, delta := some .cleared } := by
  native_decide

end A12Kernel.Conformance.StringAlternatives
