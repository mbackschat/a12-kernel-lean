import A12Kernel.Semantics.ComputationCondition
import A12Kernel.Semantics.StringCascade

/-! # A12Kernel.Conformance.ComputationCondition — direct computation-presence locks -/

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
