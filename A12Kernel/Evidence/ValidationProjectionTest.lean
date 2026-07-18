import A12Kernel.Evidence.ValidationProjection

/-! # Compact validation-observation locks

These examples exercise the closed projections used by the remaining retained validation families. The detailed semantic matrices remain in `A12Kernel.Conformance`; this module guards only the evidence-facing loss of information and the compact family routes.
-/

namespace A12Kernel.Evidence.ValidationProjectionTest

open Lean
open A12Kernel
open A12Kernel.Evidence.ValidationProjection

private def fired (polarity : String) : Json :=
  Json.mkObj [("verdict", Json.mkObj [
    ("tag", toJson "fired"), ("polarity", toJson polarity)])]

private def requiredFired : Json :=
  Json.mkObj [
    ("verdict", Json.mkObj [
      ("tag", toJson "fired"), ("polarity", toJson "omission")]),
    ("message", Json.mkObj [
      ("code", toJson "mandatoryField"),
      ("pointer", toJson "/Order[1]/Quantity")])]

private def suppressed : Json :=
  Json.mkObj [("suppressed", toJson true)]

private def requiredInput (state : String) : Json :=
  Json.mkObj [("state", toJson state)]

private def operatorInput (model : String) (value : Json) (hasContent : Bool) : Json :=
  Json.mkObj [
    ("model", toJson model),
    ("value", value),
    ("hasContent", toJson hasContent)]

private def row (filter value : Json) : Json :=
  Json.mkObj [("filter", filter), ("value", value)]

private def iterationInput (filterEquals : Json) (sumEquals : Int)
    (rows : List Json) : Json :=
  Json.mkObj [
    ("filterEquals", filterEquals),
    ("sumEquals", toJson sumEquals),
    ("rows", toJson rows)]

private def message (rule polarity pointer : String) : Json :=
  Json.mkObj [
    ("rule", toJson rule),
    ("polarity", toJson polarity),
    ("pointer", toJson pointer)]

private def messages (values : List Json) : Json :=
  Json.mkObj [("messages", toJson values)]

private def agrees (expected : Json) : Except String Json → Bool
  | .ok actual => actual == expected
  | .error _ => false

private def authored (polarity : Option String) : Json :=
  Json.mkObj [("authored", match polarity with
    | none => Json.null
    | some value => Json.mkObj [("polarity", toJson value)])]

private def viewsAs (expected : Json) (observed : Json) : Bool :=
  agrees expected (publicObservationView observed)

private def rejects (fragment : String) : Except String α → Bool
  | .error message => message.contains fragment
  | .ok _ => false

example : verdictObservation (.fired .omission) == fired "omission" := by native_decide
example : verdictObservation .notFired == suppressed := by native_decide
example : verdictObservation .unknown == suppressed := by native_decide

example : agrees requiredFired (replayRequired (requiredInput "empty")) := by
  native_decide

example : agrees suppressed (replayRequired (requiredInput "rejected")) := by
  native_decide

example : agrees (messages [])
    (replayOperator (operatorInput "stringLength" Json.null false)) := by
  native_decide

example : agrees (messages [
      message "NUM_SIGNED_NE_NEG" "omission" "/Order[1]/Quantity",
      message "NUM_UNSIGNED_NE_NEG" "value" "/Order[1]/StockOnHand",
      message "NUM_UNSIGNED_NE_POS" "omission" "/Order[1]/StockOnHand"])
    (replayOperator (operatorInput "directionalNumber" Json.null true)) := by
  native_decide

example : agrees (authored (some "omission"))
    (replayIteration (iterationInput (toJson (1 : Int)) 7 [
      row (toJson "rejected") (toJson (100 : Int)),
      row (toJson (1 : Int)) (toJson (3 : Int)),
      row (toJson (1 : Int)) (toJson (4 : Int))])) := by
  native_decide

example : agrees (authored none)
    (replayIteration (iterationInput (toJson (1 : Int)) 7 [
      row (toJson (1 : Int)) (toJson "rejected"),
      row (toJson (1 : Int)) (toJson (3 : Int)),
      row (toJson (1 : Int)) (toJson (4 : Int))])) := by
  native_decide

example : viewsAs (Json.mkObj [("rejectionClass", toJson "missingInner")])
    (Json.mkObj [
      ("kernelCode", toJson "MVK_NO_ITERATION_FOR_WILDCARD"),
      ("rejectionClass", toJson "missingInner")]) := by
  native_decide

example : rejects "paired" (publicObservationView (Json.mkObj [
    ("kernelCode", toJson "MVK_INVALID_COMPARE_DEC_PLACES"),
    ("rejectionClass", toJson "missingInner")])) := by
  native_decide

example : rejects "together" (publicObservationView (Json.mkObj [
    ("rejectionClass", toJson "missingInner")])) := by
  native_decide

example : rejects "together" (publicObservationView (Json.mkObj [
    ("kernelCode", toJson "MVK_NO_ITERATION_FOR_WILDCARD")])) := by
  native_decide

end A12Kernel.Evidence.ValidationProjectionTest
