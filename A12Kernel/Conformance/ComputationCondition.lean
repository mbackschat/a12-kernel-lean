import A12Kernel.Semantics.ComputationCondition
import A12Kernel.Semantics.StringCascade

/-! # A12Kernel.Conformance.ComputationCondition — computation presence and ordered-connective locks -/

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

end A12Kernel.Conformance.ComputationCondition
