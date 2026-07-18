import A12Kernel.Evidence.StringCascadeProjection

/-! # Compact direct-cascade family locks

The synthetic bundle below fixes the proposed producer contract without claiming to be external evidence.
-/

namespace A12Kernel.Evidence.StringCascadeProjectionTest

open Lean
open A12Kernel
open A12Kernel.Evidence
open A12Kernel.Evidence.StringCascadeProjection

private def rawDigest := "7e38744283cf17f7f57fe0bce342084a8e2896fb99aa60c2a9f4fb52e185dc17"
private def qualificationDigest := "f581d82d7eb04929b38d4663bbb48a28f09c7399273cd5974cd59e739eca5d64"
private def nullable : Option String → Json | none => .null | some value => toJson value
private def value (target text : String) := Json.mkObj [("target", toJson target), ("value", toJson text)]
private def error (cause : String) := Json.mkObj [("target", toJson "mid"), ("attempted", toJson "ABCD"), ("cause", toJson cause)]
private def applied (target : String) (text : Option String) := Json.mkObj [("target", toJson target), ("value", nullable text)]
private def input (source priorMid : Option String) := Json.mkObj [
  ("source", nullable source), ("priorMid", nullable priorMid), ("priorOut", toJson "STALE")]
private def observed (clean changed errors : List Json) (cleared : List String)
    (mid out : Option String) := Json.mkObj [
  ("clean", toJson clean), ("changed", toJson changed), ("errors", toJson errors),
  ("cleared", toJson cleared), ("applied", toJson [applied "mid" mid, applied "out" out])]
private def caseJson (id : String) (input observed : Json) := Json.mkObj [
  ("id", toJson id), ("input", input), ("observed", observed)]

private def cases : List Json := [
  caseJson "source-abc-mid-old" (input (some "ABC") (some "OLD"))
    (observed [value "mid" "ABC", value "out" "ABC-X"] [value "mid" "ABC", value "out" "ABC-X"] [] [] (some "ABC") (some "ABC-X")),
  caseJson "source-abc-mid-abc" (input (some "ABC") (some "ABC"))
    (observed [value "mid" "ABC", value "out" "ABC-X"] [value "out" "ABC-X"] [] [] (some "ABC") (some "ABC-X")),
  caseJson "source-absent-mid-old" (input none (some "OLD"))
    (observed [value "out" "-X"] [value "out" "-X"] [] ["mid"] none (some "-X")),
  caseJson "source-absent-mid-absent" (input none none)
    (observed [value "out" "-X"] [value "out" "-X"] [] [] none (some "-X")),
  caseJson "source-abcd-mid-old" (input (some "ABCD") (some "OLD"))
    (observed [] [] [error "tooLong"] ["out"] none none)]

private def bundleJson (familyCases : List Json := cases) : Json := Json.mkObj [
  ("schemaVersion", toJson 1), ("kernelVersion", toJson "30.8.1"), ("families", toJson [
    Json.mkObj [
      ("id", toJson familyId), ("projectionId", toJson projectionId), ("projectionVersion", toJson projectionVersion),
      ("source", Json.mkObj [
        ("producer", toJson "a12-dmkits"), ("revision", toJson "1b5f463b89adc6cfb81b41121cd6c97855e8cbe3"),
        ("rawCapture", Json.mkObj [("path", toJson "packet/RECEIPT.json"), ("sha256", toJson rawDigest)]),
        ("qualification", Json.mkObj [
          ("policyId", toJson "kernel-route-confirmed-v1"),
          ("receipt", Json.mkObj [("path", toJson "qualification/RECEIPT.json"), ("sha256", toJson qualificationDigest)])])]),
      ("cases", toJson familyCases)]])]

private def familyFromText (input : String) : Except String ObservationBundle.Family := do
  let bundle ← ObservationBundle.Bundle.parseText input
  match bundle.families with
  | [family] => pure family
  | _ => throw "synthetic bundle must contain exactly one family"

private def fixtureFamily : Except String ObservationBundle.Family :=
  familyFromText bundleJson.compress

private def evaluateWithoutOverlay (cascade : StringDirectCascade)
    (context : StringComputationContext) : Except StringDirectCascadeFault StringDirectCascadeResult := do
  let producer ← cascade.producer.evaluate context |>.mapError .producer
  let consumer ← cascade.consumer.evaluate context |>.mapError .consumer
  pure { producer, consumer }

private def hasMismatches (expected : List String) : Except String (List String) → Bool
  | .ok actual => actual == expected
  | .error _ => false

private def rejects (needle : String) : Except String α → Bool
  | .error message => message.contains needle
  | .ok _ => false

private def rejectsText (needle input : String) : Bool :=
  match familyFromText input with
  | .ok family => rejects needle (decodeFamily family)
  | .error _ => false

private def mutateCase (family : ObservationBundle.Family) (id : String)
    (mutate : ObservationBundle.ObservationCase → ObservationBundle.ObservationCase) :=
  { family with cases := family.cases.map fun (case : ObservationBundle.ObservationCase) =>
      if case.id == id then mutate case else case }

example : hasMismatches [] (do mismatchIds replay (← fixtureFamily)) = true := by native_decide

example : hasMismatches
    ["source-abc-mid-old", "source-absent-mid-old", "source-abcd-mid-old"]
    (do mismatchIds (replayWith evaluateWithoutOverlay) (← fixtureFamily)) = true := by
  native_decide

example : hasMismatches ["source-abcd-mid-old"] (do
    let family ← fixtureFamily
    let mutated := { family with cases := family.cases.map fun
      (case : ObservationBundle.ObservationCase) =>
      if case.id == "source-abcd-mid-old" then
        { case with observed := case.observed.setObjVal! "errors" (toJson [error "tooShort"]) }
      else case }
    mismatchIds replay mutated) = true := by
  native_decide

example : (match fixtureFamily with
    | .error _ => false
    | .ok family =>
        let id := "source-abc-mid-old"
        let reversed := mutateCase family id fun case =>
          { case with observed := case.observed.setObjVal! "clean" (toJson [value "out" "ABC-X", value "mid" "ABC"]) }
        let duplicated := mutateCase family id fun case =>
          { case with observed := case.observed.setObjVal! "clean" (toJson [value "mid" "ABC", value "out" "ABC-X", value "out" "ABC-X"]) }
        hasMismatches [id] (mismatchIds replay reversed) &&
          hasMismatches [id] (mismatchIds replay duplicated)) = true := by
  native_decide

example : (match fixtureFamily with
    | .error _ => false
    | .ok family =>
        let firstId := "source-abc-mid-old"
        let wrongPolicy := { family with source := {
          family.source with qualification := family.source.qualification.map fun value =>
            { value with policyId := "other" } } }
        [
          rejects "compatibility identity" <| decodeFamily { family with id := "other" },
          rejects "producer" <| decodeFamily { family with source := { family.source with producer := "other" } },
          rejects "producer revision" <| decodeFamily {
            family with source := { family.source with revision := "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" } },
          rejects "qualification identity" <| decodeFamily {
            family with source := { family.source with qualification := none } },
          rejects "kernel-route-confirmed" <| decodeFamily wrongPolicy,
          rejectsText "raw receipt identity" <|
            bundleJson.compress.replace "packet/RECEIPT.json" "packet/OTHER.json",
          rejectsText "qualification receipt identity" <|
            bundleJson.compress.replace qualificationDigest rawDigest,
          rejects "five-case order" <| decodeFamily { family with cases := family.cases.reverse },
          rejects "input matrix" <| decodeFamily <| mutateCase family firstId fun case =>
            { case with input := input (some "WRONG") (some "OLD") },
          rejects "input: unknown member" <| decodeFamily <| mutateCase family firstId fun case =>
            { case with input := case.input.setObjVal! "extra" Json.null },
          rejects "observed: unknown member" <| decodeFamily <| mutateCase family firstId fun case =>
            { case with observed := case.observed.setObjVal! "extra" Json.null },
          rejects "unsupported target" <| decodeFamily <| mutateCase family firstId fun case =>
            { case with observed := case.observed.setObjVal! "clean" (toJson [value "wrong" "ABC"]) },
          rejects "unsupported target error" <| decodeFamily <|
            mutateCase family "source-abcd-mid-old" fun case =>
              { case with observed := case.observed.setObjVal! "errors" (toJson [error "other"]) }
        ].all id) = true := by
  native_decide

end A12Kernel.Evidence.StringCascadeProjectionTest
