import A12Kernel.Semantics.RepetitionNotUnique

/-! # Resolved `RepetitionNotUnique` separating cases

These examples start after reference-scope selection, path expansion, and key-cell classification. They lock duplicate construction and per-row verdicts without adding checked paths, `@From`, partial relevance, message pointers, or whole-rule orchestration.
-/

namespace A12Kernel.Conformance.RepetitionNotUnique

open A12Kernel

private def orders : RepeatableLevel := 10

private def items : RepeatableLevel := 20

private def itemEnv (index : RowIndex) : Env :=
  [(items, index)]

private def nestedItemEnv (outer inner : RowIndex) : Env :=
  [(orders, outer), (items, inner)]

private def row (index : RowIndex) (key : List RepetitionKeyComponent) :
    ResolvedRepetitionKeyRow :=
  { row := itemEnv index, key }

private def nestedRow (outer inner : RowIndex)
    (key : List RepetitionKeyComponent) :
    ResolvedRepetitionKeyRow :=
  { row := nestedItemEnv outer inner, key }

private def number (value : Rat) : RepetitionKeyComponent :=
  .present (.number value)

private def token (value : String) : RepetitionKeyComponent :=
  .present (.token value)

private def result (row : RowIndex) (verdict : Verdict)
    (cluster : List RowIndex := []) : RepetitionNotUniqueResult :=
  { row := itemEnv row, verdict, cluster := cluster.map itemEnv }

private def nestedResult (outer inner : RowIndex) (verdict : Verdict)
    (cluster : List (RowIndex × RowIndex) := []) :
    RepetitionNotUniqueResult :=
  {
    row := nestedItemEnv outer inner
    verdict
    cluster := cluster.map fun coordinate => nestedItemEnv coordinate.1 coordinate.2
  }

/- Equal local indices beneath different outer rows denote different row identities; every duplicate fires and retains the complete cluster in scope order. -/
example :
    evalRepetitionNotUnique
        [nestedRow 1 1 [token "A"], nestedRow 2 1 [token "A"],
          nestedRow 2 2 [token "A"], nestedRow 3 1 [token "B"]] =
      [nestedResult 1 1 (.fired .value) [(1, 1), (2, 1), (2, 2)],
        nestedResult 2 1 (.fired .value) [(1, 1), (2, 1), (2, 2)],
        nestedResult 2 2 (.fired .value) [(1, 1), (2, 1), (2, 2)],
        nestedResult 3 1 .notFired] := by
  native_decide

/- Optional empty components participate once a key has content; matching empties make the duplicate omission-typed. -/
example :
    evalRepetitionNotUnique
        [row 1 [token "A", .empty], row 2 [token "A", .empty],
          row 3 [token "A", token "B"]] =
      [result 1 (.fired .omission) [1, 2],
        result 2 (.fired .omission) [1, 2],
        result 3 .notFired] := by
  native_decide

/- An all-empty key is skipped rather than becoming a duplicate null tuple. -/
example :
    evalRepetitionNotUnique
        [row 1 [.empty, .empty], row 2 [.empty, .empty]] =
      [result 1 .notFired, result 2 .notFired] := by
  native_decide

/- Lean retains required-empty and malformed current keys as UNKNOWN before external suppression; both rows are excluded from the duplicate relation, while optional-empty peers remain valid participants. -/
example :
    evalRepetitionNotUnique
        [row 1 [token "A", .unknown .required],
          row 2 [token "A", .empty],
          row 3 [token "A", .empty],
          row 4 [token "A", .unknown .malformed]] =
      [result 1 .unknown,
        result 2 (.fired .omission) [2, 3],
        result 3 (.fired .omission) [2, 3],
        result 4 .unknown] := by
  native_decide

private def authoredMessageVisible : Verdict → Bool
  | .fired _ => true
  | .notFired | .unknown => false

/- The kernel's authored-message observation cannot distinguish Lean's invalid-key refinement from a clean unique row. -/
example :
    let invalidRow := row 1 [token "A", .unknown .malformed]
    let uniqueRow := row 2 [token "B"]
    let rows := [invalidRow, uniqueRow]
    let invalid := (evalRepetitionNotUniqueRow rows invalidRow).verdict
    let unique := (evalRepetitionNotUniqueRow rows uniqueRow).verdict
    invalid = .unknown ∧ unique = .notFired ∧ invalid ≠ unique ∧
      authoredMessageVisible invalid = authoredMessageVisible unique := by
  native_decide

private def belowHalfUlp : Rat := 49 / ((10 : Rat) ^ 21)

/- Number components reuse scale-19 typed equality; unlike a Number, a token with the same spelling is a different key kind. -/
example :
    evalRepetitionNotUnique
        [row 1 [number 0], row 2 [number belowHalfUlp],
          row 3 [token "0"]] =
      [result 1 (.fired .value) [1, 2],
        result 2 (.fired .value) [1, 2],
        result 3 .notFired] := by
  native_decide

/- Composite tuple equality is positional and length-sensitive. -/
example :
    evalRepetitionNotUnique
        [row 1 [token "A", token "B"],
          row 2 [token "B", token "A"],
          row 3 [token "A"]] =
      [result 1 .notFired, result 2 .notFired, result 3 .notFired] := by
  native_decide

private def guardedRows : List ResolvedRepetitionKeyRow :=
  [row 1 [token "A"], row 2 [token "A"]]

/- Duplicate construction is branch-independent: a guard-false row does not fire, but removing it would change its partner's RNU verdict. -/
example :
    Verdict.conj .notFired
        (evalRepetitionNotUniqueRow guardedRows (row 1 [token "A"])).verdict =
        .notFired ∧
      Verdict.conj (.fired .value)
        (evalRepetitionNotUniqueRow guardedRows (row 2 [token "A"])).verdict =
        .fired .value ∧
      (evalRepetitionNotUniqueRow
        [row 2 [token "A"]] (row 2 [token "A"])).verdict =
        .notFired := by
  native_decide

end A12Kernel.Conformance.RepetitionNotUnique
