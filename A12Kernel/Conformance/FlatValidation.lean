import A12Kernel.Semantics.FlatValidation

/-! # Flat validation conformance locks -/

namespace A12Kernel.Conformance.FlatValidation

open A12Kernel

private def numberField : FlatNumberField :=
  { id := 0, info := { scale := 2, signed := false } }

private def booleanField : FlatBooleanField :=
  { id := 1 }

private def confirmField : FlatConfirmField :=
  { id := 2 }

private def healthyField : FlatBooleanField :=
  { id := 3 }

private def brokenField : FlatNumberField :=
  { id := 4, info := { scale := 0, signed := false } }

private def checked (kind : FieldKind) (raw : RawCell) : CheckedCell :=
  formalCheck { kind := kind } raw

private def emptyContext : FlatContext where
  read fieldId :=
    if fieldId = numberField.id then checked (.number numberField.info) .empty
    else if fieldId = booleanField.id then checked .boolean .empty
    else checked .confirm .empty

private def branchingContext : FlatContext where
  read fieldId :=
    if fieldId = healthyField.id then checked .boolean (.parsed (.bool true))
    else checked (.number brokenField.info) (.rejected .malformed)

private def filledContext : FlatContext where
  read fieldId :=
    if fieldId = numberField.id then checked (.number numberField.info) (.parsed (.num 5))
    else if fieldId = booleanField.id then checked .boolean (.parsed (.bool false))
    else checked .confirm (.parsed (.conf true))

private def omissionAndBrokenContext : FlatContext where
  read fieldId :=
    if fieldId = brokenField.id then checked (.number brokenField.info) (.rejected .malformed)
    else checked (.number numberField.info) .empty

private def malformedConfirmContext : FlatContext where
  read _ := checked .confirm (.parsed (.conf false))

private def numberIsZero : FlatCondition :=
  .compare (.number .equal numberField 0)

private def booleanIsFalse : FlatCondition :=
  .compare (.boolean .equal booleanField false)

private def booleanIsNotFalse : FlatCondition :=
  .compare (.boolean .notEqual booleanField false)

private def numberIsFive : FlatCondition :=
  .compare (.number .equal numberField 5)

private def confirmIsTrue : FlatCondition :=
  .compare (.confirm .equal confirmField)

private def confirmIsNotTrue : FlatCondition :=
  .compare (.confirm .notEqual confirmField)

private def healthyTrue : FlatCondition :=
  .compare (.boolean .equal healthyField true)

private def healthyFalse : FlatCondition :=
  .compare (.boolean .equal healthyField false)

private def brokenIsZero : FlatCondition :=
  .compare (.number .equal brokenField 0)

private def numberIsNotZero : FlatCondition :=
  .compare (.number .notEqual numberField 0)

private def booleanNotFilled : FlatCondition :=
  .fieldNotFilled (.boolean booleanField)

private def brokenFilled : FlatCondition :=
  .fieldFilled (.number brokenField)

private def brokenNotFilled : FlatCondition :=
  .fieldNotFilled (.number brokenField)

private def healthyOrBroken : FlatCondition :=
  .or healthyTrue brokenIsZero

private def healthyAndBroken : FlatCondition :=
  .and healthyTrue brokenIsZero

private def healthyFalseAndBroken : FlatCondition :=
  .and healthyFalse brokenIsZero

private def omissionOrBroken : FlatCondition :=
  .or numberIsZero brokenIsZero

private def numberNotFilled : FlatCondition :=
  .fieldNotFilled (.number numberField)

private def negativeOrComparison : FlatCondition :=
  .or numberNotFilled numberIsZero

private def negativeAndComparison : FlatCondition :=
  .and numberNotFilled numberIsZero

private def twoNegativePredicates : FlatCondition :=
  .and numberNotFilled booleanNotFilled

private def positiveOrComparison : FlatCondition :=
  .or (.fieldFilled (.number numberField)) numberIsZero

example : numberIsZero.evalSelected emptyContext = .fired .omission := by
  native_decide

example : numberIsNotZero.evalSelected emptyContext = Verdict.notFired := by
  native_decide

example : numberIsFive.evalSelected filledContext = Verdict.fired .value := by
  native_decide

example : booleanIsFalse.evalSelected emptyContext = .notFired := by
  decide

example : booleanIsNotFalse.evalSelected emptyContext = Verdict.notFired := by
  decide

example : booleanIsFalse.evalSelected filledContext = Verdict.fired .value := by
  decide

example : confirmIsTrue.evalSelected emptyContext = Verdict.notFired := by
  decide

example : confirmIsNotTrue.evalSelected emptyContext = Verdict.fired .omission := by
  decide

example : confirmIsTrue.evalSelected filledContext = Verdict.fired .value := by
  decide

example : booleanNotFilled.evalSelected emptyContext = Verdict.fired .omission := by
  decide

example : brokenFilled.evalSelected branchingContext = Verdict.unknown := by
  decide

example : brokenNotFilled.evalSelected branchingContext = Verdict.unknown := by
  decide

example : confirmIsNotTrue.evalSelected malformedConfirmContext = Verdict.unknown := by
  decide

example : healthyOrBroken.evalSelected branchingContext = Verdict.fired .value := by
  decide

example : healthyAndBroken.evalSelected branchingContext = Verdict.unknown := by
  decide

example : healthyFalseAndBroken.evalSelected branchingContext = Verdict.notFired := by
  decide

example : omissionOrBroken.evalSelected omissionAndBrokenContext = Verdict.fired .omission := by
  native_decide

example : numberIsZero.evalFull emptyContext false = .notFired := by
  decide

example : numberIsZero.evalFull emptyContext true = .fired .omission := by
  native_decide

example : numberNotFilled.evalFull emptyContext false = Verdict.fired .omission := by
  decide

example : negativeOrComparison.evalFull emptyContext false = Verdict.fired .omission := by
  native_decide

example : negativeAndComparison.evalFull emptyContext false = Verdict.notFired := by
  decide

example : twoNegativePredicates.evalFull emptyContext false = Verdict.fired .omission := by
  decide

example : positiveOrComparison.evalFull emptyContext false = Verdict.notFired := by
  decide


example : rescaleHalfUp (1 / (2 * (10 ^ comparisonScale : Rat))) comparisonScale =
    1 / (10 ^ comparisonScale : Rat) := by
  native_decide

example : rescaleHalfUp (-(1 / (2 * (10 ^ comparisonScale : Rat)))) comparisonScale =
    -(1 / (10 ^ comparisonScale : Rat)) := by
  native_decide

/- These are helper-level boundary locks, not legal field fixtures. The kernel-backed
   whole-rule witness reaches scale 20 through arithmetic, which is outside this fragment. -/
example : rescaleHalfUp (4 / (10 ^ 20 : Rat)) comparisonScale = 0 := by
  native_decide

example : rescaleHalfUp (6 / (10 ^ 20 : Rat)) comparisonScale =
    1 / (10 ^ comparisonScale : Rat) := by
  native_decide

end A12Kernel.Conformance.FlatValidation
