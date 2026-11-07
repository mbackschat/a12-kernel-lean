import A12Kernel.Reference.Dm.Validate
import A12Kernel.Reference.Dm.Document

/-! # A stored Number's runtime text keeps at most fifteen digits

Kernel 31.3.1 caps the scale of a stored Number's runtime text at fifteen less the stored value's integer
digits and rounds the dropped digits half up; kernel 31.1.1 padded and rescaled without a cap (a12-dmkits
KF681, `NumberRenderCapDiffTest` at `505683610`;
[inbound record](../../../docs/sources/inbound-handbacks.md#src-inbound-2026-11-07) §4). The carrier is the
letter's ledger: `Ledger` takes exactly ten decimals, `Rate` up to fourteen, and a rule fires when the rate
exceeds `1.12345678901234`.
-/

namespace A12Kernel.Dm.NumberRenderCapLocks

open Lean A12Kernel

private def number (minimum maximum : Nat) : Json :=
  Json.mkObj [("type", "NumberType"), ("NumberType", Json.mkObj [
    ("minFractionalDigits", toJson minimum), ("maxFractionalDigits", toJson maximum)])]

private def field (name : String) (type : Json) : Json :=
  Json.mkObj [("type", "Field"), ("id", .str s!"/Book/{name}"), ("name", .str name),
    ("Field", Json.mkObj [("fieldType", type)])]

private def ledgerModel : Json :=
  Json.mkObj [
    ("header", Json.mkObj [("id", "L_DM"), ("modelType", "document"), ("modelVersion", "29.8.0"),
      ("locales", Json.arr #[Json.mkObj [("code", "en_US")]])]),
    ("content", Json.mkObj [("modelInfo", Json.mkObj [("name", "L")]),
      ("modelConfig", Json.mkObj [("timeZone", "UTC"), ("conditionLanguage", Json.mkObj [("code", "en_US")])]),
      ("modelRoot", Json.mkObj [("rootGroups", Json.arr #[Json.mkObj [("type", "Group"), ("id", "/Book"),
        ("name", "Book"), ("Group", Json.mkObj [("elements", Json.arr #[
          field "Ledger" (number 10 10), field "Rate" (number 0 14)])])]])])])]

private def world : World := { now := { epochMillis := 0 } }

/-- A stored value's formal read on `field`: the text it reads as, or the code it draws. -/
private def formalRead (field : String) (value : Json) : Option String := do
  let dm ← (readModel ledgerModel).toOption
  let declaration ← dm.flat.fields.find? (·.name == field)
  let .number info := declaration.policy.kind | none
  let input ← (readDocument dm (Json.mkObj [("Book", Json.mkObj [(field, value)])])).toOption
  let cell ← input.data.cells.head?
  let stored := cell.numericDecimal.map NumericStoredInput.decimal |>.getD (.text cell.stored)
  pure <| match declaration.numericTargetConstraints.checkFormalRead info stored with
    | .ok (text, _) => text
    | .error error => error.errorCode

private def decimal (text : String) : Json := (Json.parse text).toOption.getD .null

private def rateRule : DmRule :=
  { group := ["Book"], name := "R", severity := "ERROR", errorCode := "R",
    condition := "[Rate] > 1.12345678901234", errorEntityRelPath := "../Rate" }

/-- Whether the rule `[Rate] > 1.12345678901234` fires on a stored rate. -/
private def rateFires (rate : String) : Option Bool := do
  let dm ← (readModel ledgerModel).toOption
  let checked ← (checkRule dm .english rateRule).toOption
  let input ← (readDocument dm (Json.mkObj [("Book", Json.mkObj [("Rate", decimal rate)])])).toOption
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler dm.flat).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  pure !(← (runRule world document checked).toOption).isEmpty

/-- Five integer digits leave room for all ten decimals; six and seven stop the pad at nine and eight, so
the fractional count answers where an uncapped pad's sixteen digits drew the total-length class. A quoted
number converts first and pads alike. -/
example : formalRead "Ledger" (decimal "12345") = some "12345.0000000000" ∧
    formalRead "Ledger" (decimal "123456") = some "zahlFalscheAnzahlNachkommastellen" ∧
    formalRead "Ledger" (decimal "1234567") = some "zahlFalscheAnzahlNachkommastellen" ∧
    formalRead "Ledger" (.str "123456") = some "zahlFalscheAnzahlNachkommastellen" := by
  native_decide

/-- A stored value with more than fifteen significant digits is rounded to fit, drawing no length class. -/
example : formalRead "Rate" (decimal "1234567890.1234567") = some "1234567890.12346" := by native_decide

/-- The kept digit of `1.123456789012345` is an even `4`, so half even would leave both rates equal to the
constant and neither would fire; half up fires on the first only. -/
example : rateFires "1.123456789012345" = some true ∧ rateFires "1.123456789012344" = some false := by
  native_decide

end A12Kernel.Dm.NumberRenderCapLocks
