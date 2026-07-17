import A12Kernel.Evidence.StringCascadeSchema

/-! # Direct String-cascade evidence schema locks

These executable examples keep the operation-specific observation decoder closed before any retained packet is assigned A12 meaning.
-/

namespace A12Kernel.Evidence.StringCascade.SchemaTest

open Lean
open A12Kernel.Evidence.StringCascade

private def availableStringValue (value : String) : Json :=
  Json.mkObj [
    ("typed", Json.mkObj [
      ("availability", toJson "available"),
      ("kind", toJson "STRING"),
      ("value", toJson value)]),
    ("rendered", Json.mkObj [
      ("availability", toJson "available"),
      ("value", toJson value)])]

private def availableString : Json :=
  availableStringValue "ABC"

private def unavailableWithValue : Json :=
  Json.mkObj [
    ("availability", toJson "notExposedByRunner"),
    ("value", toJson "hidden")]

private def presentEmptyWithValue : Json :=
  Json.mkObj [
    ("pointer", toJson "/Cascade[1]/Mid"),
    ("state", toJson "presentEmpty"),
    ("value", availableString)]

private def presentValueEmpty : Json :=
  Json.mkObj [
    ("pointer", toJson "/Cascade[1]/Mid"),
    ("state", toJson "presentValue"),
    ("value", availableStringValue "")]

example : (match TransportValue.fromJson "value" availableString with
    | .ok value =>
        value.typed.kind == some "STRING" &&
        value.typed.value == some "ABC" &&
        value.rendered.kind == none &&
        value.rendered.value == some "ABC"
    | .error _ => false) = true := by
  native_decide

example : (ValueView.fromJson "value.typed" unavailableWithValue).isOk = false := by
  native_decide

example : (AppliedEntry.fromJson "applied" presentEmptyWithValue).isOk = false := by
  native_decide

example : (AppliedEntry.fromJson "applied" presentValueEmpty).isOk = false := by
  native_decide

end A12Kernel.Evidence.StringCascade.SchemaTest
