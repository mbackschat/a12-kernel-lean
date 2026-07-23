import A12Kernel.Semantics.CrossLevelCorrelation

/-! # Two-level captured-environment correlation locks

This is one starred candidate level observed from a rule row whose captured environment
contains that level and one nested descendant. It is not a multi-star or join model.
-/

namespace A12Kernel.Conformance.CrossLevelCorrelation

open A12Kernel

private def parentLevel : RepeatableLevel := 10
private def childLevel : RepeatableLevel := 20

private def probe : FlatNumberField :=
  { id := 0, info := { scale := 0, signed := false } }

private def checkedNumber : RawCell → CheckedCell :=
  formalCheck { kind := .number probe.info }

private def present : CheckedCell :=
  checkedNumber (.parsed (.num 1))

private def readCell (_ : Env) (_ : FieldId) : CheckedCell :=
  present

private def rows : TwoLevelOuterStarContext where
  starLevel := parentLevel
  descendantLevel := childLevel
  candidates := [1, 2]
  read := readCell

private def captured (parentRow childRow : RowIndex) :
    CapturedTwoLevelOuterStarContext :=
  { rows, outerStarRow := parentRow, outerDescendantRow := childRow }

private def repetition (origin : HavingOrigin)
    (level : RepeatableLevel) : HavingRepetitionRef :=
  { origin, level }

private def diagonalCondition : CorrelatedHaving :=
  .and
    (CorrelatedHaving.compareRepetitions .equal
      (repetition .inner parentLevel) (repetition .outer parentLevel))
    (CorrelatedHaving.compareRepetitions .equal
      (repetition .inner parentLevel) (repetition .outer childLevel))

private def diagonalHaving : OriginCheckedCorrelatedHaving :=
  { condition := diagonalCondition, usesInner := by decide, usesOuter := by decide }

private def diagonalStar : SingleCorrelatedStar :=
  { valueField := probe, having := diagonalHaving }

example :
    (captured 1 2).outerEnv =
      [(parentLevel, 1), (childLevel, 2)] ∧
    (captured 1 2).rows.candidateEnv 2 = [(parentLevel, 2)] := by
  decide

/-- A diagonal outer environment exposes the same row at both named levels. -/
example : diagonalStar.selectCrossLevel (captured 1 1) = [1] := by
  native_decide

/-- The off-diagonal environment must not collapse `$P` and `$P/C` to one scalar row. -/
example : diagonalStar.selectCrossLevel (captured 1 2) = [] := by
  native_decide

/-- Replacing the real off-diagonal capture by one scalar coordinate changes truth. -/
example :
    let actual := (captured 1 2).frame 1
    let collapsed : CorrelationFrame :=
      { innerEnv := rows.candidateEnv 1
        outerEnv := [(parentLevel, 1), (childLevel, 1)] }
    diagonalCondition.evalTruthIn rows.asCorrelationContext actual = .fls ∧
    diagonalCondition.evalTruthIn rows.asCorrelationContext collapsed = .tru := by
  native_decide

/-- Missing or duplicate level bindings fail closed instead of choosing row zero or the
    first matching association. -/
example :
    let missing : CorrelationFrame :=
      { innerEnv := rows.candidateEnv 1
        outerEnv := [(parentLevel, 1)] }
    let duplicate : CorrelationFrame :=
      { innerEnv := rows.candidateEnv 1
        outerEnv := [(parentLevel, 1), (childLevel, 2), (childLevel, 1)] }
    diagonalCondition.evalTruthIn rows.asCorrelationContext missing = .unknown ∧
    diagonalCondition.evalTruthIn rows.asCorrelationContext duplicate = .unknown := by
  native_decide

/- Row zero is not a concrete captured repetition and therefore fails the same named lookup rather than participating in a comparison. -/
example :
    Env.uniqueRowAt? [(parentLevel, 0)] parentLevel = none := by
  native_decide

private inductive ResolvingProbeError where
  | read (field : FieldId)
  | binding (cause : EnvBindingError)
  deriving Repr, DecidableEq

private def resolvingCell : CheckedCell :=
  { rawPresent := true, parsed := some (.num 1), findings := [] }

private def resolvingContext :
    ResolvingCorrelationContext ResolvingProbeError where
  read _ field :=
    if field == 2 then .error (.read field) else .ok resolvingCell
  bindingError := .binding

private def resolvingFrame : CorrelationFrame :=
  { innerEnv := [(parentLevel, 1)]
    outerEnv := [(parentLevel, 1)] }

private def resolvingNumber (field : FieldId) : HavingNumberRef :=
  { origin := .inner, field := { id := field, info := probe.info } }

private def falseThenBadRead : CorrelatedHaving :=
  .and
    (CorrelatedHaving.compareNumbers .notEqual
      (resolvingNumber 1) (resolvingNumber 1))
    (CorrelatedHaving.compareNumbers .equal
      (resolvingNumber 2) (resolvingNumber 1))

private inductive ResolvingTruthSnapshot where
  | truth (value : K)
  | computation (value : ComputationConditionResult)
  | error (cause : ResolvingProbeError)
  deriving Repr, DecidableEq

private def truthSnapshot : Except ResolvingProbeError K → ResolvingTruthSnapshot
  | .ok value => .truth value
  | .error cause => .error cause

private def computationSnapshot : Except ResolvingProbeError
    ComputationConditionResult → ResolvingTruthSnapshot
  | .ok value => .computation value
  | .error cause => .error cause

private def resolvingCandidate (row : RowIndex) : Env :=
  [(parentLevel, row)]

private def orderedResolvingContext :
    ResolvingCorrelationContext ResolvingProbeError where
  read environment field :=
    if environment == resolvingCandidate 3 && field == 2 then
      .error (.read field)
    else
      .ok resolvingCell
  bindingError := .binding

private def trueResolvingHaving : CorrelatedHaving :=
  CorrelatedHaving.compareNumbers .equal
    (resolvingNumber 2) (resolvingNumber 1)

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
        .error (.read 2) := by
  native_decide

/- Computation retains its distinct left-to-right short circuit: clean false decides And before the structurally failing right leaf is reached. -/
example :
    computationSnapshot
      (falseThenBadRead.evalComputationInResolving resolvingContext
        resolvingFrame) = .computation .notTrue := by
  native_decide

/- A missing repetition binding is the same explicit structural channel, not a semantic UNKNOWN. -/
example :
    truthSnapshot (
      (CorrelatedHaving.compareRepetitions .equal
        { origin := .inner, level := childLevel }
        { origin := .outer, level := parentLevel }).evalTruthInResolving
          resolvingContext resolvingFrame) =
        .error (.binding (.missingBinding childLevel)) := by
  native_decide

/- Validation selection evaluates every candidate in encounter order, retains earlier successes, and still reports a later structural read failure. -/
example :
    selectionSnapshot (
      trueResolvingHaving.selectEnvironmentsResolving orderedResolvingContext []
        [resolvingCandidate 1, resolvingCandidate 3]) =
      .error (.read 2) := by
  native_decide

/- Computation's one-kept-successor scan evaluates the successor before the current target, so a structural failure there wins before target consumption. -/
example :
    let consume : Nat → Env →
        Except ResolvingProbeError (Nat ⊕ Nat) :=
      fun _ _ => .ok (.inr 7)
    scanSnapshot (
      trueResolvingHaving.scanComputationResolving orderedResolvingContext []
        consume [resolvingCandidate 1, resolvingCandidate 3] 0) =
      .error (.read 2) := by
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

end A12Kernel.Conformance.CrossLevelCorrelation
