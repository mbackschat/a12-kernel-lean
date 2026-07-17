import A12Kernel.Semantics.FlatValidation
import A12Kernel.Semantics.StringComputation

/-! # A12Kernel.Conformance.StringIngestion — evaluated String ingestion locks

These examples cover the one-pass cache normalization from `spec/02-logic-and-formal-errors.md` and its shared UTF-16 `Length` use from `spec/06-strings-and-enumerations.md`. The reduced `.parsed (.str ...)` input is assumed admitted before this boundary; line-break permission, raw storage, enumeration ordering, and raw-type behavior remain outside the capsule.
-/

namespace A12Kernel.Conformance.StringIngestion

open A12Kernel

private def stringField : FlatStringField := { id := 17 }

private def checked (raw : RawCell) : CheckedCell :=
  formalCheck { kind := .string } raw

private def context (raw : RawCell) : FlatContext where
  read _ := checked raw

private def directEquals (expected : String) : FlatCondition :=
  .compare (.stringEqual stringField expected)

private def lengthLessThan (expected : Rat) : FlatCondition :=
  .compare (.stringLength .less stringField expected)

private def lengthGreaterOrEqual (expected : Rat) : FlatCondition :=
  .compare (.stringLength .greaterEqual stringField expected)

private def computationContext (raw : RawCell) : StringComputationContext where
  read _ := checked raw

example : normalizeEvaluatedString "AB\r\nCD" = "AB\nCD" := by
  decide

example : normalizeEvaluatedString "AB\nCD" = "AB\nCD" := by
  decide

example : normalizeEvaluatedString "AB\rCD" = "AB\rCD" := by
  decide

/- One ingestion pass replaces non-overlapping pairs. Applying the pass twice is observably wrong for an overlapping prefix. -/
example : normalizeEvaluatedString "\r\r\n" = "\r\n" := by
  decide

example :
    normalizeEvaluatedString (normalizeEvaluatedString "\r\r\n") !=
      normalizeEvaluatedString "\r\r\n" := by
  decide

example :
    (directEquals "\r\n").evalFull (context (.parsed (.str "\r\r\n"))) true =
      .fired .value := by
  decide

example :
    (directEquals "\n").evalFull (context (.parsed (.str "\r\r\n"))) true =
      .notFired := by
  decide

example :
    checked (.parsed (.str "AB\r\nCD")) =
      { rawPresent := true, parsed := some (.str "AB\nCD"), findings := [] } := by
  decide

/- An admitted CRLF-bearing input reaches rule evaluation with that pair represented as one LF. -/
example :
    (directEquals "AB\nCD").evalFull (context (.parsed (.str "AB\r\nCD"))) true =
      .fired .value := by
  decide

/- The normalized evaluated value differs from the pre-normalized input. -/
example :
    (directEquals "AB\r\nCD").evalFull (context (.parsed (.str "AB\r\nCD"))) true =
      .notFired := by
  decide

/- Length consumes the same normalized five-code-unit value, not the raw six-code-unit text. -/
example :
    (lengthLessThan 6).evalFull (context (.parsed (.str "AB\r\nCD"))) true =
      .fired .value := by
  native_decide

example :
    (lengthLessThan 5).evalFull (context (.parsed (.str "AB\r\nCD"))) true =
      .notFired := by
  native_decide

example :
    (lengthGreaterOrEqual 6).evalFull (context (.parsed (.str "AB\r\nCD"))) true =
      .notFired := by
  native_decide

example :
    (lengthGreaterOrEqual 2).evalFull (context (.parsed (.str "\r\r\n"))) true =
      .fired .value := by
  native_decide

/- An existing LF and a lone CR are preserved. -/
example :
    (directEquals "AB\nCD").evalFull (context (.parsed (.str "AB\nCD"))) true =
      .fired .value := by
  decide

example :
    (directEquals "AB\rCD").evalFull (context (.parsed (.str "AB\rCD"))) true =
      .fired .value := by
  decide

example :
    (lengthLessThan 6).evalFull (context (.parsed (.str "AB\rCD"))) true =
      .fired .value := by
  native_decide

/- Ingestion does not turn formal rejection into a value. -/
example :
    (directEquals "AB\nCD").evalFull (context (.rejected .declaredConstraint)) true =
      .unknown := by
  decide

/- Computation reads consume the same checked value; they do not normalize independently. -/
example :
    (StringExpr.field stringField.id).eval
      (computationContext (.parsed (.str "AB\r\nCD"))) =
      .ok (.text "AB\nCD") := by
  rfl

example :
    (StringExpr.field stringField.id).eval
      (computationContext (.parsed (.str "\r\r\n"))) =
      .ok (.text "\r\n") := by
  rfl

end A12Kernel.Conformance.StringIngestion
