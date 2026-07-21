import A12Kernel.Semantics.ComputationCondition
import A12Kernel.Semantics.StringCascade

/-! # A12Kernel.Conformance.ComputationCondition — ordered computation-control locks -/

namespace A12Kernel.Conformance.ComputationCondition

open A12Kernel

private def probeId : FieldId := 0
private def bodyId : FieldId := 1
private def targetId : FieldId := 2

private def checkedBoolean (raw : RawCell) : CheckedCell :=
  formalCheck { kind := .boolean } raw

private def checkedString (raw : RawCell) : CheckedCell :=
  formalCheck { kind := .string } raw

private def context (probe body : CheckedCell) : StringComputationContext where
  read field :=
    if field == probeId then probe
    else if field == bodyId then body
    else checkedString .empty

private def fieldFilled : ComputationCondition := .fieldFilled probeId
private def fieldNotFilled : ComputationCondition := .fieldNotFilled probeId

private def emptyProbePoisonBody : StringComputationContext :=
  context (checkedBoolean .empty) (checkedString (.rejected .declaredConstraint))

private def filledProbePoisonBody : StringComputationContext :=
  context (checkedBoolean (.parsed (.bool false)))
    (checkedString (.rejected .declaredConstraint))

private def copyBody : StringComputationStep where
  targetField := targetId
  expression := .field bodyId
  targetPolicy := .unconstrained
  prior := .empty

private def alternative (precondition : ComputationCondition)
    (operation : α) : ComputationAlternative α where
  precondition := precondition
  operation := operation

private def storedOk : StoredString := ⟨"OK", by decide⟩

private def valueOf : Except α β → Option β
  | .ok value => some value
  | .error _ => none

example : fieldFilled.eval (context (checkedBoolean .empty) (checkedString .empty)) =
    .notTrue := by
  rfl

example : fieldNotFilled.eval (context (checkedBoolean .empty) (checkedString .empty)) =
    .holds := by
  rfl

example : fieldFilled.eval
    (context (checkedBoolean (.parsed (.bool false))) (checkedString .empty)) = .holds := by
  rfl

example : fieldNotFilled.eval
    (context (checkedBoolean (.parsed (.bool false))) (checkedString .empty)) = .notTrue := by
  rfl

example : fieldNotFilled.eval
    (context (checkedBoolean (.rejected .malformed)) (checkedString .empty)) =
      .poison .malformed := by
  rfl

example : fieldNotFilled.eval
    (context ((checkedBoolean .empty).withFinding .required) (checkedString .empty)) =
      .holds := by
  rfl

example : fieldNotFilled.eval
    (context ((checkedBoolean (.rejected .declaredConstraint)).withFinding .required)
      (checkedString .empty)) = .poison .declaredConstraint := by
  rfl

/- `And` stops after a clean not-true left operand, so the formally invalid right field is not read. -/
example :
    (ComputationCondition.and fieldFilled (.fieldFilled bodyId)).eval
      emptyProbePoisonBody = .notTrue := by
  rfl

/- Reversing the same operands reads the formally invalid field first and therefore poisons. -/
example :
    (ComputationCondition.and (.fieldFilled bodyId) fieldFilled).eval
      emptyProbePoisonBody = .poison .declaredConstraint := by
  rfl

/- A holding left operand does not decide `And`; the formally invalid right field is read. -/
example :
    (ComputationCondition.and fieldFilled (.fieldFilled bodyId)).eval
      filledProbePoisonBody = .poison .declaredConstraint := by
  rfl

/- `Or` stops after a clean holding left operand, so the formally invalid right field is not read. -/
example :
    (ComputationCondition.or fieldFilled (.fieldFilled bodyId)).eval
      filledProbePoisonBody = .holds := by
  rfl

/- Reversing the same operands exposes the otherwise-unread formally invalid field. -/
example :
    (ComputationCondition.or (.fieldFilled bodyId) fieldFilled).eval
      filledProbePoisonBody = .poison .declaredConstraint := by
  rfl

/- A clean not-true left operand does not decide `Or`; the formally invalid right field is read. -/
example :
    (ComputationCondition.or fieldFilled (.fieldFilled bodyId)).eval
      emptyProbePoisonBody = .poison .declaredConstraint := by
  rfl

/- The ordered `And` result is consumed before the String body, yielding quiet no-value. -/
example : copyBody.evaluateOutcomeWhen
    ((ComputationCondition.and fieldFilled (.fieldFilled bodyId)).eval
      emptyProbePoisonBody)
    emptyProbePoisonBody = .ok .noValue := by
  rfl

/- Reversing the same precondition operands poisons the target before the body can run. -/
example : copyBody.evaluateOutcomeWhen
    ((ComputationCondition.and (.fieldFilled bodyId) fieldFilled).eval
      emptyProbePoisonBody)
    emptyProbePoisonBody = .ok (.poison .declaredConstraint) := by
  rfl

/- Clean not-true skips a body that would otherwise poison. -/
example : copyBody.evaluateOutcomeWhen
    (fieldFilled.eval
      (context (checkedBoolean .empty) (checkedString (.rejected .declaredConstraint))))
    (context (checkedBoolean .empty) (checkedString (.rejected .declaredConstraint))) =
      .ok .noValue := by
  rfl

/- A poisoned presence read wins before a differently poisoned body can be read. -/
example : copyBody.evaluateOutcomeWhen
    (fieldNotFilled.eval
      (context (checkedBoolean (.rejected .malformed))
        (checkedString (.rejected .declaredConstraint))))
    (context (checkedBoolean (.rejected .malformed))
      (checkedString (.rejected .declaredConstraint))) =
      .ok (.poison .malformed) := by
  rfl

example : valueOf (copyBody.evaluateOutcomeWhen
    (fieldNotFilled.eval
      (context (checkedBoolean .empty) (checkedString (.parsed (.str "OK")))))
    (context (checkedBoolean .empty) (checkedString (.parsed (.str "OK"))))) =
      some (.accepted storedOk) := by
  native_decide

/- Quiet and poisoned dependency outcomes separate at the same downstream presence read. -/
example :
    ((context (checkedBoolean .empty) (checkedString .empty)).withDependencyOutcome
        probeId .noValue).map (fun updated => fieldNotFilled.eval updated) = .ok .holds := by
  rfl

example :
    ((context (checkedBoolean .empty) (checkedString .empty)).withDependencyOutcome
        probeId (.poison .malformed)).map
      (fun updated => fieldNotFilled.eval updated) = .ok (.poison .malformed) := by
  rfl

example : ComputationAlternative.selectFirst
    ([] : List (ComputationAlternative Nat))
    emptyProbePoisonBody = .noMatch := by
  rfl

/- A clean non-match falls through to the next declared alternative. -/
example : ComputationAlternative.selectFirst
    [alternative fieldFilled 1, alternative fieldNotFilled 2]
    emptyProbePoisonBody = .selected 2 := by
  native_decide

/- Overlapping preconditions select the first declared operation. -/
example : ComputationAlternative.selectFirst
    [alternative fieldNotFilled 1, alternative fieldNotFilled 2]
    emptyProbePoisonBody = .selected 1 := by
  native_decide

example : ComputationAlternative.selectFirst
    [alternative fieldFilled 1, alternative fieldFilled 2]
    emptyProbePoisonBody = .noMatch := by
  rfl

/- Selection stops before a poisoning later precondition is read. -/
example : ComputationAlternative.selectFirst
    [alternative fieldNotFilled 1, alternative (.fieldFilled bodyId) 2]
    emptyProbePoisonBody = .selected 1 := by
  native_decide

/- A poisoned precondition aborts before a later holding alternative can be selected. -/
example : ComputationAlternative.selectFirst
    [alternative (.fieldFilled bodyId) 1, alternative fieldNotFilled 2]
    emptyProbePoisonBody = .poison .declaredConstraint := by
  rfl

/- Earlier clean non-matches do not hide a later poison or permit selection beyond it. -/
example : ComputationAlternative.selectFirst
    [alternative fieldFilled 1, alternative (.fieldFilled bodyId) 2,
      alternative fieldNotFilled 3]
    emptyProbePoisonBody = .poison .declaredConstraint := by
  rfl

/- No common precondition leaves the guarded alternative table unchanged. -/
example : ComputationAlternative.expandCommonPrecondition
    none [alternative fieldNotFilled 1, alternative fieldFilled 2] =
      [alternative fieldNotFilled 1, alternative fieldFilled 2] := by
  rfl

/- A common precondition is left-conjoined to every guarded alternative without changing operation order. -/
example : ComputationAlternative.expandCommonPrecondition
    (some fieldFilled)
    [alternative fieldNotFilled 1, alternative (.fieldFilled bodyId) 2] =
      [alternative (.and fieldFilled fieldNotFilled) 1,
       alternative (.and fieldFilled (.fieldFilled bodyId)) 2] := by
  native_decide

/- A clean false common precondition suppresses every alternative guard, including a guard that would poison if reached. -/
example : ComputationAlternative.selectFirst
    (ComputationAlternative.expandCommonPrecondition
      (some fieldFilled)
      [alternative (.fieldFilled bodyId) 1, alternative fieldNotFilled 2])
    emptyProbePoisonBody = .noMatch := by
  native_decide

/- A poisoned common precondition wins before a cleanly holding alternative guard. -/
example : ComputationAlternative.selectFirst
    (ComputationAlternative.expandCommonPrecondition
      (some (.fieldFilled bodyId))
      [alternative fieldNotFilled 1, alternative fieldNotFilled 2])
    emptyProbePoisonBody = .poison .declaredConstraint := by
  native_decide

/- A holding common precondition preserves the original first-match result. -/
example : ComputationAlternative.selectFirst
    (ComputationAlternative.expandCommonPrecondition
      (some fieldNotFilled)
      [alternative fieldFilled 1, alternative fieldNotFilled 2])
    emptyProbePoisonBody = .selected 2 := by
  native_decide

/- These admitted String operation payloads contain no target or prior-target state. Selection ends at the first holding expression without inspecting its later result. -/
example : ComputationAlternative.selectFirst
    [alternative fieldNotFilled copyBody.expression,
      alternative fieldNotFilled (.literal "LATER")]
    (context (checkedBoolean .empty) (checkedString .empty)) =
      .selected copyBody.expression := by
  native_decide

/- Two legal singleton tables can differ at selection even though the selected String expression later produces clean no-value. -/
example :
    ComputationAlternative.selectFirst
        [alternative fieldFilled copyBody.expression]
        (context (checkedBoolean .empty) (checkedString .empty)) = .noMatch ∧
      ComputationAlternative.selectFirst
        [alternative fieldNotFilled copyBody.expression]
        (context (checkedBoolean .empty) (checkedString .empty)) =
          .selected copyBody.expression ∧
      copyBody.evaluateOutcome
        (context (checkedBoolean .empty) (checkedString .empty)) = .ok .noValue := by
  constructor
  · rfl
  constructor <;> rfl

end A12Kernel.Conformance.ComputationCondition
