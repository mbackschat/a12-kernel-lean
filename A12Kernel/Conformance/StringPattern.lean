import A12Kernel.Semantics.StringPattern

/-! # A12Kernel.Conformance.StringPattern — resolved String-pattern locks

These examples begin after a pattern has passed Java and kernel admission and has been resolved to a whole-value matcher. They lock checked String ingestion, empty suppression, formal unavailability, and the distinct `PatternMatched`/`PatternViolated` firing polarity without claiming a Java-compatible pattern compiler.
-/

namespace A12Kernel.Conformance.StringPattern

open A12Kernel

private def stringField : FlatStringField := { id := 17 }

private def context (raw : RawCell) : FlatContext where
  read _ := formalCheck { kind := .string } raw

private def matchesNormalizedWitness (value : String) : Bool :=
  value == "AB\nCD"

/- The matcher receives the normalized checked value, not the raw CRLF-bearing input. -/
example :
    (context (.parsed (.str "AB\r\nCD"))).evalResolvedStringPattern
      .matched stringField matchesNormalizedWitness =
      .fired .value := by
  decide

example :
    (context (.parsed (.str "AB\r\nCD"))).evalResolvedStringPattern
      .violated stringField matchesNormalizedWitness =
      .notFired := by
  decide

/- A present nonmatch reverses the two operators, and a fired result is always VALUE. -/
example :
    (context (.parsed (.str "different"))).evalResolvedStringPattern
      .matched stringField matchesNormalizedWitness =
      .notFired := by
  decide

example :
    (context (.parsed (.str "different"))).evalResolvedStringPattern
      .violated stringField matchesNormalizedWitness =
      .fired .value := by
  decide

/- Empty String is not evaluated by either operator. -/
example :
    (context (.parsed (.str ""))).evalResolvedStringPattern
      .matched stringField matchesNormalizedWitness =
      .notFired := by
  decide

example :
    (context (.parsed (.str ""))).evalResolvedStringPattern
      .violated stringField matchesNormalizedWitness =
      .notFired := by
  decide

/- Formal rejection remains unknown rather than becoming a pattern violation. -/
example :
    (context (.rejected .declaredConstraint)).evalResolvedStringPattern
      .matched stringField matchesNormalizedWitness =
      .unknown := by
  decide

example :
    (context (.rejected .declaredConstraint)).evalResolvedStringPattern
      .violated stringField matchesNormalizedWitness =
      .unknown := by
  decide

end A12Kernel.Conformance.StringPattern
