import A12Kernel.Reference.Dm.ModelComputation
import A12Kernel.Reference.Dm.ComputationCheck
import A12Kernel.Reference.Dm.ComputeMessages
import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.EntryFrameFixture

/-! # A suppressed Enumeration calculation on a fixed target

A computation whose preamble names `MVK_ERROR_INVALID_ENUM_CALCULATION` is admitted where the calculation
would draw that class, and its target judges each attempted text at runtime (spec/09 §4.3). The text-source
rows are a12-dmkits KF298's, measured on both strategies (31.3.1 Letter J §5,
[inbound record](../../../docs/sources/inbound-handbacks.md#src-inbound-2026-11-07)): a declared token is
stored, a declared value's label or an undeclared text leaves the target errored without a message, and an
empty text clears a seeded target. The wider Enumeration source is judged by the same target check, derived
and unmeasured; the controls separate the account in which the preamble lifts every class.
-/

namespace A12Kernel.Dm.SuppressedEnumerationCalculationLocks

open Lean

private def modelSource (operation preamble : String) : String :=
  r#"{"content":{"modelConfig":{"conditionLanguage":{"code":"en_US"}},"modelRoot":{"rootGroups":[
{"type":"Group","name":"Form","Group":{"repeatability":1,"elements":[
{"type":"Field","id":"/Form/Text","name":"Text","Field":{"fieldType":{"type":"StringType"}}},
{"type":"Field","id":"/Form/Wide","name":"Wide","Field":{"fieldType":{"type":"EnumerationType","EnumerationType":{"values":[{"value":"A"},{"value":"9"},{"value":"B"}]}}}},
{"type":"Field","id":"/Form/Count","name":"Count","Field":{"fieldType":{"type":"NumberType","NumberType":{"maxFractionalDigits":0}}}},
{"type":"Field","id":"/Form/Out","name":"Out","Field":{"fieldType":{"type":"EnumerationType","EnumerationType":{"values":[{"value":"A","label":[{"locale":"en_US","text":"Alpha"}]},{"value":"9","label":[{"locale":"en_US","text":"Nine"}]}]}}}},
{"type":"Computation","id":"/Form/OutC","name":"OutC","Computation":{"computedFieldRelPath":"../Out","computationAlternatives":[{"operation":"OPERATION"}],"additionalParserInformation":"PREAMBLE","errorMessage":[{"locale":"en_US","text":"computed check"}]}}]}}]}}}"#
    |>.replace "OPERATION" (operation.replace "\"" "\\\"") |>.replace "PREAMBLE" preamble

private def suppressCalculation : String := "@SuppressWarning(MVK_ERROR_INVALID_ENUM_CALCULATION)"

private def model (operation : String) (preamble := suppressCalculation) : Option DmModel := do
  let dm ← (readModel (checkedEntryFrame (← (Json.parse (modelSource operation preamble)).toOption))).toOption
  if dm.refusals.isEmpty && dm.computations.length == 1 then some dm else none

/-- The computation's static verdict: `admitted`, or the class it is refused on. -/
private def verdict (operation : String) (preamble := suppressCalculation) : Option String := do
  let dm ← model operation preamble
  let computation ← dm.computations.head?
  match checkComputation dm .english computation with
  | .ok _ => pure "admitted"
  | .error refusal => pure (refusal.kernelClass?.getD s!"unclassified {refusal.detail}")

/-- The target's change projection and the call's message channel, for a document seeding `Out`. -/
private def run (operation : String) (cells : List (String × String)) : Option (String × List String) := do
  let dm ← model operation
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler dm.flat).toOption
  let data ← (readDocument dm (Json.mkObj [("Form", Json.mkObj
    (cells.map fun (name, value) => (name, Json.str value)))])).toOption
  if !data.refusals.isEmpty then none
  let checked ← (checkDocument prepared "en_US" data.data).toOption
  let (results, messages) ← (runModelComputationsWithMessages dm .english world prepared checked).toOption
  let outcome := ((results.find? (·.pointer.endsWith "/Out")).map (·.outcome)).getD "unchanged"
  pure (outcome, messages.map toString)

-- KF298: the preamble admits a String source, which the calculation refuses without it.
example :
    verdict "[Text]" = some "admitted" &&
    verdict "[Text]" (preamble := "") = some "MVK_ERROR_INVALID_ENUM_CALCULATION" := by
  native_decide

-- KF298's runtime from a text: a declared token stores, a label or an undeclared text errors the target
-- without a message, and an empty text clears it.
example :
    run "[Text]" [("Text", "9"), ("Out", "A")] = some ("value 9", []) &&
    run "[Text]" [("Text", "Alpha"), ("Out", "A")] = some ("errored Alpha", []) &&
    run "[Text]" [("Text", "Z"), ("Out", "A")] = some ("errored Z", []) &&
    run "[Text]" [("Text", ""), ("Out", "A")] = some ("cleared", []) := by
  native_decide

-- A wider Enumeration source is admitted under the preamble and judged by the same target check; derived
-- from the target check, unmeasured for this source kind.
example :
    verdict "[Wide]" (preamble := "") = some "MVK_ERROR_INVALID_ENUM_CALCULATION" &&
    verdict "[Wide]" = some "admitted" &&
    run "[Wide]" [("Wide", "A"), ("Out", "9")] = some ("value A", []) &&
    run "[Wide]" [("Wide", "B"), ("Out", "9")] = some ("errored B", []) := by
  native_decide

-- The preamble lifts only the calculation's class: the scale-warning preamble leaves it standing (spec/12
-- §4, measured), and a Number source keeps the comparison's class and a literal outside the domain the
-- literal's (both derived: the preamble names neither).
example :
    verdict "[Text]" (preamble := "@SuppressWarning(MVK_INVALID_COMPARE_DEC_PLACES)") =
      some "MVK_ERROR_INVALID_ENUM_CALCULATION" &&
    verdict "[Count]" = some "MVK_INVALID_COMPARE_TO_ENUM_OR_STRING" &&
    verdict "\"Z\"" = some "MVK_INVALID_STRING_CONSTANT_FOR_ENUM_COMPARISON" := by
  native_decide

end A12Kernel.Dm.SuppressedEnumerationCalculationLocks
