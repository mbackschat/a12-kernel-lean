import A12Kernel.Reference.Dm.ModelComputation
import A12Kernel.Reference.Dm.ComputationCheck
import A12Kernel.Reference.Dm.ComputeMessages
import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.EntryFrameFixture

/-! # A suppressed Enumeration calculation on a repeatable target and from `FirstFilledValue`

The remaining carriers of the preamble that lifts `MVK_ERROR_INVALID_ENUM_CALCULATION`
([spec/09 §4.3](../../spec/09-computations.md#43-number-string-enumeration-and-custom-targets)): a direct
field into a repeatable target, and `FirstFilledValue` into a fixed and a repeatable one. a12-dmkits KF298
measures the runtime from a String field source on a fixed target only
([inbound record](../../../docs/sources/inbound-handbacks.md#src-inbound-2026-11-07)). The runtime rows
here are therefore derived from the target's own check, which the measured rows establish, and unmeasured
on their carrier. The controls separate the account in which the preamble lifts every class; the
`FirstFilledValue` rows additionally separate a scan that falls through a rejected token from the one that
judges the first filled token.
-/

namespace A12Kernel.Dm.SuppressedEnumerationRowCalculationLocks

open Lean

private inductive Host where
  | form
  | rows

private def enumeration (id name values : String) : String :=
  r#"{"type":"Field","id":"@ID@","name":"@NAME@","Field":{"fieldType":{"type":"EnumerationType","EnumerationType":{"values":[@VALUES@]}}}}"#
    |>.replace "@ID@" id |>.replace "@NAME@" name |>.replace "@VALUES@" values

private def plain (values : List String) : String :=
  ",".intercalate (values.map fun value => "{\"value\":\"" ++ value ++ "\"}")

private def labelled : String :=
  r#"{"value":"A","label":[{"locale":"en_US","text":"Alpha"}]},{"value":"9","label":[{"locale":"en_US","text":"Nine"}]}"#

/-- `Wide` declares `Alpha`, the spelling of `Out`'s label of `A`, and `B`, which `Out` lacks. -/
private def wide : List String := ["A", "9", "B", "Alpha"]

private def computation (id relative operation preamble : String) : String :=
  r#"{"type":"Computation","id":"@ID@","name":"OutC","Computation":{"computedFieldRelPath":"@REL@","computationAlternatives":[{"operation":"@OPERATION@"}],"additionalParserInformation":"@PREAMBLE@","errorMessage":[{"locale":"en_US","text":"computed check"}]}}"#
    |>.replace "@ID@" id |>.replace "@REL@" relative |>.replace "@OPERATION@" operation
    |>.replace "@PREAMBLE@" preamble

/-- One computation lives in the fixed group or in the repeatable one, so each model carries exactly one. -/
private def modelSource (host : Host) (operation preamble : String) : String :=
  let formComputation := match host with
    | .form => "," ++ computation "/Form/OutC" "../Out" operation preamble
    | .rows => ""
  let rowComputation := match host with
    | .form => ""
    | .rows => "," ++ computation "/Form/Rows/ROutC" "../ROut" operation preamble
  r#"{"content":{"modelConfig":{"conditionLanguage":{"code":"en_US"}},"modelRoot":{"rootGroups":[
{"type":"Group","id":"/Form","name":"Form","Group":{"repeatability":1,"elements":[
{"type":"Field","id":"/Form/Text","name":"Text","Field":{"fieldType":{"type":"StringType"}}},"#
    ++ enumeration "/Form/Wide" "Wide" (plain wide) ++ "," ++ enumeration "/Form/Wide2" "Wide2" (plain ["A", "9", "B"])
    ++ "," ++ enumeration "/Form/Out" "Out" labelled ++ formComputation
    ++ r#",{"type":"Group","id":"/Form/Rows","name":"Rows","Group":{"repeatability":2,"elements":[
{"type":"Field","id":"/Form/Rows/RText","name":"RText","Field":{"fieldType":{"type":"StringType"}}},"#
    ++ enumeration "/Form/Rows/RWide" "RWide" (plain wide) ++ ","
    ++ enumeration "/Form/Rows/RWide2" "RWide2" (plain ["A", "9", "B"]) ++ ","
    ++ enumeration "/Form/Rows/ROut" "ROut" labelled ++ rowComputation ++ "]}}]}}]}}}"

private def suppressCalculation : String := "@SuppressWarning(MVK_ERROR_INVALID_ENUM_CALCULATION)"

private def model (host : Host) (operation : String) (preamble := suppressCalculation) : Option DmModel := do
  let dm ← (readModel (checkedEntryFrame
    (← (Json.parse (modelSource host operation preamble)).toOption))).toOption
  if dm.refusals.isEmpty && dm.computations.length == 1 then some dm else none

/-- The computation's static verdict: `admitted`, or the class it is refused on. -/
private def verdict (host : Host) (operation : String) (preamble := suppressCalculation) : Option String := do
  let dm ← model host operation preamble
  let computation ← dm.computations.head?
  match checkComputation dm .english computation with
  | .ok _ => pure "admitted"
  | .error refusal => pure (refusal.kernelClass?.getD s!"unclassified {refusal.detail}")

private def cellsJson (cells : List (String × String)) : List (String × Json) :=
  cells.map fun (name, value) => (name, Json.str value)

/-- The target's change at each instance and the call's message channel, for a document seeding the
target. A row whose target keeps its value reports no change, so each row here seeds a different one. -/
private def run (host : Host) (operation : String) (form : List (String × String))
    (rows : List (List (String × String)) := []) : Option (List String × List String) := do
  let dm ← model host operation
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler dm.flat).toOption
  let rowsJson := if rows.isEmpty then [] else
    [("Rows", Json.arr (rows.map fun row => Json.mkObj (cellsJson row)).toArray)]
  let data ← (readDocument dm (Json.mkObj [("Form", Json.mkObj (cellsJson form ++ rowsJson))])).toOption
  if !data.refusals.isEmpty then none
  let checked ← (checkDocument prepared "en_US" data.data).toOption
  let (results, messages) ← (runModelComputationsWithMessages dm .english world prepared checked).toOption
  let target : String := match host with
    | .form => "/Out"
    | .rows => "/ROut"
  pure ((results.filter (·.pointer.endsWith target)).map (fun result => result.pointer ++ " " ++ result.outcome),
    messages.map toString)

-- Controls: each member is refused the calculation's class without the preamble and admitted with it, and
-- the scale-warning preamble alone leaves the class standing.
example :
    verdict .rows "[RText]" (preamble := "") = some "MVK_ERROR_INVALID_ENUM_CALCULATION" &&
    verdict .rows "[RText]" = some "admitted" &&
    verdict .rows "[RText]" (preamble := "@SuppressWarning(MVK_INVALID_COMPARE_DEC_PLACES)") =
      some "MVK_ERROR_INVALID_ENUM_CALCULATION" &&
    verdict .form "FirstFilledValue(Wide, Wide2)" (preamble := "") = some "MVK_ERROR_INVALID_ENUM_CALCULATION" &&
    verdict .form "FirstFilledValue(Wide, Wide2)" = some "admitted" &&
    verdict .form "FirstFilledValue(Wide, Wide2)" (preamble := "@SuppressWarning(MVK_INVALID_COMPARE_DEC_PLACES)") =
      some "MVK_ERROR_INVALID_ENUM_CALCULATION" &&
    verdict .rows "FirstFilledValue(RWide, RWide2)" (preamble := "") = some "MVK_ERROR_INVALID_ENUM_CALCULATION" &&
    verdict .rows "FirstFilledValue(RWide, RWide2)" = some "admitted" &&
    verdict .rows "FirstFilledValue(RWide, RWide2)" (preamble := "@SuppressWarning(MVK_INVALID_COMPARE_DEC_PLACES)") =
      some "MVK_ERROR_INVALID_ENUM_CALCULATION" := by
  native_decide

-- A direct String field into a repeatable target: a declared token stores, a declared value's label or an
-- undeclared text errors the target without a message, and an empty text clears it, in each row alone.
example :
    run .rows "[RText]" [] [[("RText", "9"), ("ROut", "A")]] = some (["Form/Rows/ROut value 9"], []) &&
    run .rows "[RText]" [] [[("RText", "Alpha"), ("ROut", "A")]] = some (["Form/Rows/ROut errored Alpha"], []) &&
    run .rows "[RText]" [] [[("RText", "Z"), ("ROut", "A")]] = some (["Form/Rows/ROut errored Z"], []) &&
    run .rows "[RText]" [] [[("RText", ""), ("ROut", "A")]] = some (["Form/Rows/ROut cleared"], []) &&
    run .rows "[RText]" []
      [[("RText", "9"), ("ROut", "A")], [("RText", "Z"), ("ROut", "A")]] =
      some (["Form/Rows/ROut value 9", "Form/Rows[2]/ROut errored Z"], []) := by
  native_decide

-- A wider Enumeration field into a repeatable target is judged by the same target check; `Alpha` is a
-- token of the wider declaration spelling the target's label of `A`.
example :
    verdict .rows "[RWide]" (preamble := "") = some "MVK_ERROR_INVALID_ENUM_CALCULATION" &&
    verdict .rows "[RWide]" = some "admitted" &&
    run .rows "[RWide]" [] [[("RWide", "A"), ("ROut", "9")]] = some (["Form/Rows/ROut value A"], []) &&
    run .rows "[RWide]" [] [[("RWide", "B"), ("ROut", "9")]] = some (["Form/Rows/ROut errored B"], []) &&
    run .rows "[RWide]" [] [[("RWide", "Alpha"), ("ROut", "9")]] = some (["Form/Rows/ROut errored Alpha"], []) := by
  native_decide

-- `FirstFilledValue` into a fixed target: the first filled member's token is the one the target judges, so
-- an empty first member falls through to a second whose token is judged, and an undeclared first token
-- errors the target rather than falling through to a later declared one.
example :
    run .form "FirstFilledValue(Wide, Wide2)" [("Wide", "9"), ("Out", "A")] = some (["Form/Out value 9"], []) &&
    run .form "FirstFilledValue(Wide, Wide2)" [("Wide", "Alpha"), ("Out", "A")] =
      some (["Form/Out errored Alpha"], []) &&
    run .form "FirstFilledValue(Wide, Wide2)" [("Wide", "B"), ("Wide2", "A"), ("Out", "9")] =
      some (["Form/Out errored B"], []) &&
    run .form "FirstFilledValue(Wide, Wide2)" [("Wide", ""), ("Wide2", "9"), ("Out", "A")] =
      some (["Form/Out value 9"], []) &&
    run .form "FirstFilledValue(Wide, Wide2)" [("Wide", ""), ("Wide2", "B"), ("Out", "9")] =
      some (["Form/Out errored B"], []) &&
    run .form "FirstFilledValue(Wide, Wide2)" [("Out", "A")] = some (["Form/Out cleared"], []) := by
  native_decide

-- The same rows into a repeatable target, each row scanning its own members; two rows resolve apart.
example :
    run .rows "FirstFilledValue(RWide, RWide2)" [] [[("RWide", "9"), ("ROut", "A")]] =
      some (["Form/Rows/ROut value 9"], []) &&
    run .rows "FirstFilledValue(RWide, RWide2)" [] [[("RWide", "Alpha"), ("ROut", "A")]] =
      some (["Form/Rows/ROut errored Alpha"], []) &&
    run .rows "FirstFilledValue(RWide, RWide2)" [] [[("RWide", "B"), ("RWide2", "A"), ("ROut", "9")]] =
      some (["Form/Rows/ROut errored B"], []) &&
    run .rows "FirstFilledValue(RWide, RWide2)" [] [[("RWide", ""), ("RWide2", "9"), ("ROut", "A")]] =
      some (["Form/Rows/ROut value 9"], []) &&
    run .rows "FirstFilledValue(RWide, RWide2)" [] [[("RWide", ""), ("RWide2", "B"), ("ROut", "9")]] =
      some (["Form/Rows/ROut errored B"], []) &&
    run .rows "FirstFilledValue(RWide, RWide2)" [] [[("ROut", "A")]] = some (["Form/Rows/ROut cleared"], []) &&
    run .rows "FirstFilledValue(RWide, RWide2)" []
      [[("RWide", "9"), ("ROut", "A")], [("RWide", "B"), ("RWide2", "A"), ("ROut", "A")]] =
      some (["Form/Rows/ROut value 9", "Form/Rows[2]/ROut errored B"], []) := by
  native_decide

end A12Kernel.Dm.SuppressedEnumerationRowCalculationLocks
