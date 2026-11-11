import Lean.Data.Json
import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.Validate
import A12Kernel.Reference.Dm.Replay
import A12Kernel.Reference.Dm.LoneSurrogate

/-! # A `$`-marked read inside `Having` makes the rule iterate its level

A filtered aggregate over `Rows*` whose body compares each candidate row with `[$Reports/Limit]` reads
`Reports` only through that captured reference, and the rule iterates `Reports` all the same
([spec/07 §1.1](../../../spec/07-repetition-and-iteration.md#11-iteration-scope)): with limits 1 and 2
the rule fires at the second report alone, whose limit admits both rows. A rule that left `Reports`
unbound would evaluate once at its first coordinate and stay silent, the defect a12-dmkits' interpreter
had. The rows are a12-dmkits' KF691 matrix on kernel 31.3.1, both strategies agreeing
([inbound 2026-11-11e](../../../docs/sources/inbound-test-data-generator.md#src-inbound-2026-11-11e)):
`Sum` and `NumberOfFilledFields`, the captured read alone or beside `FieldFilled(Reports/Limit)`, and
both groups declaring 3 or 6 rows, on each side of spec/07 §1.3's product bound of 5. -/

namespace A12Kernel.Dm.CapturedHavingScopeLocks

open Lean

private def world : World := { now := { epochMillis := 0 } }

private def number (name : String) (minimum maximum : Nat) : String :=
  s!"\{\"type\":\"Field\",\"name\":\"{name}\",\"Field\":\{\"fieldType\":\{\"type\":\"NumberType\"," ++
  s!"\"NumberType\":\{\"maxFractionalDigits\":0,\"minValue\":{minimum},\"maxValue\":{maximum}}}," ++
  "\"requirednessConfig\":{\"mode\":\"absoluteOrRelativeToNextRepAncestor\"}}}"

private def rows (name field : String) (capacity : Nat) : String :=
  s!"\{\"type\":\"Group\",\"name\":\"{name}\",\"Group\":\{\"repeatability\":{capacity}," ++
  s!"\"elements\":[{number field 1 2}]}}"

/-- The model: a fixed `Parcel` with a required `Anchor`, two sibling groups of `capacity` rows and one
ERROR rule reporting on `Reports/Limit`. -/
private def model (capacity : Nat) (condition : String) : String :=
  "{\"header\":{\"id\":\"captured\",\"modelVersion\":\"29.8.0\",\"locales\":[{\"code\":\"en_US\"}]}," ++
  "\"content\":{\"modelInfo\":{\"name\":\"captured\"},\"modelConfig\":{\"conditionLanguage\":" ++
  "{\"code\":\"en_US\"}},\"modelRoot\":{\"rootGroups\":[{\"type\":\"Group\",\"name\":\"Parcel\"," ++
  s!"\"Group\":\{\"elements\":[{number "Anchor" 1 1},{rows "Rows" "Amount" capacity}," ++
  s!"{rows "Reports" "Limit" capacity},\{\"type\":\"Rule\",\"name\":\"CapturedLimit\",\"Rule\":\{" ++
  s!"\"errorEntityRelPath\":\"../Reports/Limit\",\"errorCode\":\"CAPTURED\"," ++
  s!"\"errorCondition\":{(Json.str condition).compress},\"severity\":\"ERROR\"," ++
  "\"errorMessage\":[{\"locale\":\"en_US\",\"text\":\"over\"}]}}]}}]}}}"

/-- Each message's code and concrete coordinates, `none` when the model or document is not read whole. -/
private def messages (modelText documentText : String) : Option (List (String × List Nat)) := do
  let dm ← ((parseModelJson modelText).bind (readModel ·)).toOption
  if !dm.refusals.isEmpty then none
  let language ← Language.ofCode? dm.conditionLanguage
  let input ← ((parseDocumentJson documentText).toOption.bind (readDocument dm · |>.toOption))
  if !input.refusals.isEmpty then none
  let locale ← (localeKey "en_US").toOption
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler dm.flat).toOption
  let checked ← (checkDocument prepared locale input.data).toOption
  let validated ← checked.fullValidationDocument.toOption
  let fired ← dm.rules.flatMapM fun rule => do
    let checkedRule ← (checkValidationRule dm language rule world).toOption
    (runValidationRule world validated checkedRule).toOption
  pure (fired.map fun message => (message.errorCode, message.errorAddress.coordinates.filterMap fun
    | .concrete index => some index
    | _ => none))

private def filtered (aggregate : String) : String :=
  s!"{aggregate}(Rows*/Amount Having [Rows/Amount] <= [$Reports/Limit]) > 1"

/-- The four conditions: each aggregate, its captured read alone and beside the explicit read. -/
private def conditions : List String :=
  ["Sum", "NumberOfFilledFields"].flatMap fun aggregate =>
    [filtered aggregate, s!"FieldFilled(Reports/Limit) And {filtered aggregate}"]

private def oneReport : String :=
  "{\"Parcel\":{\"Anchor\":1,\"Rows\":[{\"Amount\":1},{\"Amount\":2}],\"Reports\":[{\"Limit\":1}]}}"

private def twoReports : String :=
  "{\"Parcel\":{\"Anchor\":1,\"Rows\":[{\"Amount\":1},{\"Amount\":2}],\"Reports\":[{\"Limit\":1},{\"Limit\":2}]}}"

/-- One report admits one row and stays silent; of two, the second admits both rows and fires there. -/
example : [3, 6].all (fun capacity => conditions.all fun condition =>
      messages (model capacity condition) oneReport == some [] &&
      messages (model capacity condition) twoReports == some [("CAPTURED", [2])]) = true := by
  native_decide

end A12Kernel.Dm.CapturedHavingScopeLocks
