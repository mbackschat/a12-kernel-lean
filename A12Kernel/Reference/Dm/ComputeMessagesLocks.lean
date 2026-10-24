import A12Kernel.Reference.Dm.ComputeMessages
import A12Kernel.Reference.Dm.Document

/-! # A computation call's formal-error channel and the reached temporal failure, through the reader

A Number target summing two temporal extractions reads left to right: an unresolvable model-zone gap
literal reached first ends the fold as a value failure and reports at the target, while a formally
invalid operand reached first poisons it silently. The channel beside the outcomes carries each
selected operand's code and the reached failure; an unrecognized Enumeration token draws the String
pattern class. Kernel oracle: the effects batch of the
[recursive temporal checkpoint](../../../docs/sources/temporal-and-message-probes.md#src-recursive-temporal-numeric-expression)
(`leftGap`, `rightGap` on `badClock`) and the
[presence-leaf checkpoint](../../../docs/sources/having-filter-probes.md#src-presence-leaf-operand-kinds),
which the population replay compares on every computation row.
-/

namespace A12Kernel.Dm.ComputeMessagesLocks
open A12Kernel A12Kernel.Dm Lean

private def field (name : String) (fieldType : Json) : Json :=
  Json.mkObj [("type", "Field"), ("name", Json.str name), ("Field", Json.mkObj [("fieldType", fieldType)])]

private def number (name : String) : Json :=
  field name (Json.mkObj [("type", "NumberType"), ("NumberType", Json.mkObj [("maxFractionalDigits", toJson (0 : Nat))])])

private def computation (name target operation : String) (precondition : Option String := none) : Json :=
  let alternative := Json.mkObj ((precondition.map fun guard => [("precondition", Json.str guard)]).getD [] ++
    [("operation", Json.str operation)])
  Json.mkObj [("type", "Computation"), ("name", Json.str name), ("Computation", Json.mkObj [
    ("computedFieldRelPath", Json.str s!"../{target}"), ("computationAlternatives", Json.arr #[alternative]),
    ("errorMessage", Json.arr #[Json.mkObj [("locale", "en_US"), ("text", "m")]])])]

private def gap : String := "HoursFromTime(TimeFromDateTime(\"31.03.2024T02:30:00\"))"

private def modelJson : Json :=
  let form := [field "Clock" (Json.mkObj [("type", "TimeType"), ("TimeType", Json.mkObj [("format", "HH:mm:ss")])]),
    field "Kind" (Json.mkObj [("type", "EnumerationType"), ("EnumerationType", Json.mkObj [("values", Json.arr #[
      Json.mkObj [("value", "A")], Json.mkObj [("value", "B")]])])]),
    number "Left", number "Right", number "Hit",
    computation "LeftComp" "Left" s!"{gap}+HoursFromTime(/Form/Clock)",
    computation "RightComp" "Right" s!"HoursFromTime(/Form/Clock)+{gap}",
    computation "HitComp" "Hit" "1" (some "[Kind] == \"A\"")]
  Json.mkObj [("header", Json.mkObj [("locales", Json.arr #[Json.mkObj [("code", "en_US")]])]),
    ("content", Json.mkObj [("modelConfig", Json.mkObj [("timeZone", "Europe/Berlin"),
        ("conditionLanguage", Json.mkObj [("code", "en_US")])]),
      ("modelRoot", Json.mkObj [("rootGroups", Json.arr #[Json.mkObj [("type", "Group"), ("name", "Form"),
        ("Group", Json.mkObj [("repeatability", toJson (1 : Nat)), ("elements", Json.arr form.toArray)])]])])])]

/-- The call's outcomes and its formal-error channel on a document with every target seeded. -/
private def run (clock kind : String) : Option (List ComputedOutcome × List ComputedMessage) := do
  let model ← (readModel modelJson).toOption
  let input ← (readDocument model (Json.mkObj [("Form", Json.mkObj [("Clock", Json.str clock), ("Kind", Json.str kind),
    ("Left", "9"), ("Right", "9"), ("Hit", "9")])])).toOption
  if !input.refusals.isEmpty then none
  let world : World := { now := { epochMillis := 0 }, modelZoneRules := ModelZone.concreteRules }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model.flat).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  (runModelComputationsWithMessages model .english world prepared checked).toOption

private def cleared (targets : List String) : List ComputedOutcome :=
  targets.map ({ pointer := s!"Form/{·}", outcome := "cleared" })

/-- Both targets clear, but only the one whose gap is reached before the invalid `Clock` reports; the
invalid operand and token report at their own cells. -/
example : (run "bad" "Z" == some (cleared ["Left", "Right", "Hit"],
    [{ pointer := "Form/Clock", code := "datumFormatFalsch" }, { pointer := "Form/Kind", code := "stringFalschesMuster" },
      { pointer := "Form/Left", code := "berechnungsWertFehler" }])) = true := by native_decide

/-- A valid `Clock` lets both orders reach the gap, and a computed instance carries no message. -/
example : (run "10:00:00" "A" == some (cleared ["Left", "Right"] ++ [{ pointer := "Form/Hit", outcome := "value 1" }],
    [{ pointer := "Form/Left", code := "berechnungsWertFehler" },
      { pointer := "Form/Right", code := "berechnungsWertFehler" }])) = true := by native_decide

end A12Kernel.Dm.ComputeMessagesLocks
