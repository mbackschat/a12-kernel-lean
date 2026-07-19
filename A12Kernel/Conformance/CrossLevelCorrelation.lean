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
    (.compareRepetitions .equal
      (repetition .inner parentLevel) (repetition .outer parentLevel))
    (.compareRepetitions .equal
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

end A12Kernel.Conformance.CrossLevelCorrelation
