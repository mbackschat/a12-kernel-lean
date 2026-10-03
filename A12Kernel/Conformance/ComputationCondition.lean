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
  targetPolicy := {}
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
      (fun updated => fieldNotFilled.eval updated) = .ok (.poison .computedDependency) := by
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

local instance [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .ok a, .ok b => decidable_of_iff (a = b) (by simp)
  | .error a, .error b => decidable_of_iff (a = b) (by simp)
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

private def numericSource : FlatNumberField := { id := probeId, info := { scale := 0, signed := true } }
private def numberContext (raw : RawCell) (row : Env := []) : ScalarComputationContext :=
  { read := fun _ => formalCheck { kind := .number numericSource.info } raw, row }
private def numericGuard (op : NumericComparisonOp) (right : Rat) : ComputationCondition :=
  .leaf (.numeric { op := .ordinary op, left := .binary .add (.atom (.field numericSource)) (.literal { value := 1, authoredScale := 0 }), right := .literal { value := right, authoredScale := 0 } })

example :
    ([.equal, .notEqual, .less, .lessEqual, .greater, .greaterEqual].map fun op =>
      (numericGuard op 3).evalChecked (numberContext (.parsed (.num 2)))) =
      [.ok .holds, .ok .notTrue, .ok .notTrue, .ok .holds, .ok .notTrue, .ok .holds] := by
  native_decide

example :
    ([.equal, .notEqual, .less, .lessEqual, .greater, .greaterEqual].map fun op =>
      (numericGuard op 3).evalChecked (numberContext .empty)) =
      [.ok .notTrue, .ok .holds, .ok .holds, .ok .holds, .ok .notTrue, .ok .notTrue] := by
  native_decide

private def coordinate : ComputationNumericAtom :=
  .repetition { path := ["Rows"], scope := [7], level := some 7 }
private def coordinateGuard : ComputationCondition :=
  .leaf (.numeric { op := .ordinary .greater, left := .atom coordinate, right := .literal { value := 0, authoredScale := 0 } })

example :
    ([[], [(7, 0)], [(7, 1), (7, 2)], [(7, 2)]].map fun row =>
      coordinateGuard.evalChecked (numberContext .empty row)) =
      [.error (.binding (.missingBinding 7)), .error (.binding (.zeroBinding 7)), .error (.binding (.duplicateBinding 7)), .ok .holds] := by
  native_decide

example :
    (ComputationCondition.and (numericGuard .equal 3) coordinateGuard).evalChecked
      (numberContext .empty) = .ok .notTrue ∧
    (ComputationCondition.or (numericGuard .notEqual 3) coordinateGuard).evalChecked
      (numberContext .empty) = .ok .holds := by
  native_decide

example :
    let comparison : NumericComparisonOf ComputationNumericAtom :=
      { op := .ordinary .equal, left := .atom (.field numericSource), right := .atom coordinate }
    comparison.evalComputationWith (ComputationNumericAtom.read
      (numberContext (.rejected .declaredConstraint))) = .ok (.poison .declaredConstraint) := by
  native_decide

example :
    let comparison : NumericComparisonOf ComputationNumericAtom :=
      { op := .ordinary .equal, left := .binary .divide (.literal { value := 1, authoredScale := 0 }) (.literal { value := 0, authoredScale := 0 })
        right := .atom (.field numericSource) }
    comparison.evalComputationWith (ComputationNumericAtom.read
      (numberContext (.rejected .declaredConstraint))) = .ok (.poison .declaredConstraint) ∧
    comparison.evalComputationWith (ComputationNumericAtom.read
      (numberContext .empty)) = .ok .notTrue := by
  native_decide

example : ComputationAlternative.selectFirstChecked
    [alternative coordinateGuard 1, { operation := 2 }]
    (numberContext .empty) = .error (.binding (.missingBinding 7)) := by
  native_decide

private def missingFillContext : ComputationCondition :=
  .leaf (.fieldFill .allFieldsFilled [.expanded 1 [{ level := 7, repeatability := some 2 }] 0])

example :
    missingFillContext.evalChecked (numberContext .empty) = .error (.fieldFill .contextRequired) ∧
    (ComputationCondition.and (.fieldFilled 1) missingFillContext).evalChecked (numberContext .empty) =
      .ok .notTrue := by native_decide

private def booleanComparison (confirm : Bool) (op : EqualityOp) : ComputationCondition :=
  .leaf (.scalar (if confirm then .confirm op { id := 1 }
    else .boolean op { id := 1 } true))

example :
    ([false, true].map fun confirm =>
      (booleanComparison confirm .notEqual).evalChecked { read := fun _ => ({ rawPresent := false, parsed := none, findings := [] } : CheckedCell) }) =
      [.ok .notTrue, .ok .holds] := by native_decide

example :
    let required : ScalarComputationContext := {
      read := fun _ => { rawPresent := false, parsed := none, findings := [.required] } }
    (booleanComparison true .notEqual).evalChecked required = .ok .holds ∧
    (booleanComparison false .notEqual).evalChecked required = .ok .notTrue ∧
    (booleanComparison true .notEqual).evalChecked { read := fun _ => (checkedBoolean (.rejected .malformed)) } =
      .ok (.poison .malformed) := by
  dsimp only
  native_decide

example :
    let context : ScalarComputationContext := { read := fun _ => (checkedBoolean (.rejected .malformed)) }
    (ComputationCondition.or (.fieldNotFilled 2) (booleanComparison true .equal)).evalChecked
      { context with read := fun field => if field == 2 then ({ rawPresent := false, parsed := none, findings := [] } : CheckedCell) else context.read field } =
      .ok .holds := by
  dsimp only
  native_decide

end A12Kernel.Conformance.ComputationCondition
