import A12Kernel.Reference.Dm.Replay
import A12Kernel.Reference.Dm.LoneSurrogate
import A12Kernel.Reference.Dm.Compute

/-! # Members a law reads trimmed or in range, and a reader takes as written

The declaration laws read an Enumeration `sValue` after Java's `trim` and ignore a String length outside
`1..99999`; full validation's staging and the rule readers take the member as written. The `sValue` rows
are peer [KF574](../../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf574) (a12-dmkits `e6490efb6`, both
strategies), the length rows the [October 21 letter](../../../docs/sources/inbound-handbacks.md#src-inbound-2026-10-21)'s
§2.2. Each model is written as text and parsed as the readers parse a model file. -/

namespace A12Kernel.Dm.WrittenMemberLocks

open Lean A12Kernel

private def world : World := { now := { epochMillis := 0 } }

private def field (name typeName body : String) : String :=
  s!"\{\"type\":\"Field\",\"name\":\"{name}\",\"Field\":\{\"fieldType\":\{\"type\":\"{typeName}\",\"{typeName}\":{body}}}}"

private def rule (name code condition : String) : String :=
  s!"\{\"type\":\"Rule\",\"name\":\"{name}\",\"Rule\":\{\"errorEntityRelPath\":\"../Qty\",\"errorCode\":\"{code}\",\"errorCondition\":{(toJson condition).compress},\"severity\":\"ERROR\",\"errorMessage\":[\{\"locale\":\"en_US\",\"text\":\"m\"}]}}"

private def built? (text : String) : Option DmModel := do
  let dm ← ((parseModelJson text).bind readModel).toOption
  if dm.refusals.isEmpty then some dm else none

/-- KF574's order: a keyed `Lines` whose Enumeration index `ServiceLevel` {`STD`, `EXPRESS`} declares
`sValue`; `SL_STD` fires on `STD`, `SL_OTHER` on any other value. -/
private def order (sValue : String) : Option DmModel :=
  built? ("{\"content\":{\"modelInfo\":{},\"modelConfig\":{\"conditionLanguage\":{\"code\":\"en_US\"}},\"modelRoot\":{\"rootGroups\":[{\"type\":\"Group\",\"name\":\"Order\",\"Group\":{\"elements\":[{\"type\":\"Group\",\"name\":\"Lines\",\"Group\":{\"repeatability\":10,\"indexFieldName\":\"ServiceLevel\",\"elements\":["
    ++ field "ServiceLevel" "EnumerationType"
      s!"\{\"values\":[\{\"value\":\"STD\"},\{\"value\":\"EXPRESS\"}],\"sValue\":{(toJson sValue).compress}}" ++ ","
    ++ field "Qty" "NumberType" "{\"maxFractionalDigits\":0}" ++ "," ++ field "Echo" "StringType" "{}" ++ ","
    ++ rule "SlStd" "SL_STD" "[Qty] >= 0 And [ServiceLevel] == \"STD\"" ++ ","
    ++ rule "SlOther" "SL_OTHER" "[Qty] >= 0 And [ServiceLevel] != \"STD\"" ++ "]}}]}}]}}}")

/-- The `code@pointer` messages full validation reports for one `Lines` row per entry, each `(Qty,
ServiceLevel)`, the index absent when empty. -/
private def fired (sValue : String) (lines : List (String × String)) : Option (List String) := do
  let dm ← order sValue
  let row := fun (qty, level) =>
    Json.mkObj ([("Qty", Json.str qty)] ++ if level.isEmpty then [] else [("ServiceLevel", Json.str level)])
  let input ← (readDocument dm (Json.mkObj [("Order", Json.mkObj [
    ("Lines", Json.arr (lines.map row).toArray)])])).toOption
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler dm.flat).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let validated ← checked.fullValidationDocument.toOption
  let messages ← dm.rules.mapM fun definition => do
    let rule ← (checkValidationRule dm .english definition world).toOption
    (runValidationRule world validated rule).toOption
  pure (messages.flatten.map fun message => s!"{message.errorCode}@{(observe dm.flat message).pointer}")

/-- KF574: a padded and a blank `sValue` are admitted by their trim, then staged as written, so the
single row's index counts as filled and differs from `STD`. The control stages `STD`; the same padded
text typed into the cell fails its formal check, so neither rule reads it. -/
example :
    fired "STD" [("5", "")] = some ["SL_STD@Order/Lines/Qty"] ∧
    fired " STD" [("5", "")] = some ["SL_OTHER@Order/Lines/Qty"] ∧
    fired " " [("5", "")] = some ["SL_OTHER@Order/Lines/Qty"] ∧
    fired "STD" [("5", " STD")] = some [] := by
  native_decide

/-- The outcomes a computation `Echo := [ServiceLevel]` reports over one `Lines` row holding only `Qty`. -/
private def echoed (sValue : String) : Option (List String) := do
  let dm ← order sValue
  let input ← (readDocument dm (Json.mkObj [("Order", Json.mkObj [
    ("Lines", Json.arr #[Json.mkObj [("Qty", Json.str "5")]])])])).toOption
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler dm.flat).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let computation : DmComputation :=
    { group := ["Order", "Lines"]
      name := "EchoComp"
      targetRelPath := "../Echo"
      commonPrecondition := none
      alternatives := [{ precondition := none, operation := "[ServiceLevel]" }]
      errorCodesToSuppress := [] }
  let (_, lowered) ← (lowerComputation dm.flat .english computation).toOption
  pure ((← (runComputations world prepared checked [lowered]).toOption).map fun outcome =>
    s!"{outcome.pointer} {outcome.outcome}")

/-- KF574's computation row: the padded default is staged for a computation as written. -/
example : echoed "STD" = some ["Order/Lines/Echo value STD"] ∧
    echoed " STD" = some ["Order/Lines/Echo value  STD"] := by
  native_decide

/-- The staged text, the index's preliminary findings and the declaration law's trimmed reading: a
padded default draws no `mandatoryField`, and an `sValue` whose trim names no value fails the build. -/
example :
    ((order " STD").bind fun dm => do
      let input ← (readDocument dm (Json.mkObj [("Order", Json.mkObj [
        ("Lines", Json.arr #[Json.mkObj [("Qty", Json.str "5")]])])])).toOption
      let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler dm.flat).toOption
      let preliminary ← ((← (checkDocument prepared "en_US" input.data).toOption).applyFullIndexPreliminary).toOption
      pure (preliminary.defaulted.map (·.stored), preliminary.findings.length)) = some ([" STD"], 0) ∧
    (order "std").isNone ∧ (order " STD").isNone := by
  native_decide

/-- A form with a digit String `Code` and a `Day` of `codeBody`, a Number `N`, and a keyed `Tags`
whose String index `Key` declares `keyBody`. -/
private def form (codeBody keyBody : String) : Option DmModel :=
  built? ("{\"content\":{\"modelInfo\":{},\"modelConfig\":{\"conditionLanguage\":{\"code\":\"en_US\"}},\"modelRoot\":{\"rootGroups\":[{\"type\":\"Group\",\"name\":\"Form\",\"Group\":{\"elements\":["
    ++ field "Code" "StringType" codeBody ++ "," ++ field "Day" "StringType" codeBody ++ ","
    ++ field "N" "NumberType" "{\"maxFractionalDigits\":0}" ++ ","
    ++ "{\"type\":\"Group\",\"name\":\"Tags\",\"Group\":{\"repeatability\":5,\"indexFieldName\":\"Key\",\"elements\":["
    ++ field "Key" "StringType" keyBody ++ "," ++ field "Amount" "NumberType" "{\"maxFractionalDigits\":0}"
    ++ "]}}]}}]}}}")

/-- The class a rule reporting on `N` draws for `condition`, `admitted`, or the refusal's detail when it
carries no class, so a classless refusal fails a row rather than passing as any expected class. -/
private def verdict (dm : DmModel) (condition : String) : String :=
  let guarded := "FieldFilled(N) And " ++ condition
  let rule : DmRule :=
    { group := ["Form"], name := "R", errorCode := "R", errorEntityRelPath := "../N", condition := guarded
      severity := "ERROR" }
  match checkValidationRule dm .english rule world with
  | .ok _ => "admitted"
  | .error refusal => refusal.kernelClass?.getD refusal.detail

/-- §2.2's three readers, the codeless member sentences being the declaration pass's (spec/01 §1):
`(written, FieldValueAsNumber(Code) under that maxLength, the key under that maxLength beside minLength 2,
the key under that minLength beside maxLength 3)`. -/
private def lengthRows : List (String × String × String × String) := [
  ("0", "admitted", "admitted", "admitted"),
  ("100000", "MVK_NO_CONVERT_IN_NUMBER", "admitted", "MVK_INDEX_VALUE_INVALID"),
  ("-1", "MVK_NO_CONVERT_IN_NUMBER", "admitted", "admitted"),
  ("-5", "admitted", "admitted", "admitted")]

private def dated : String := "DayFromDate(Date(Day, \"01\", \"2024\")) > 0"

/-- A rule reader judges with the written length, while the inversion law ignores a member outside its
range, so neither `2 > 0` nor `100000 > 3` fails the build. The Date reader draws its format class in
every column; its `maxLength` 2 control, like the others, is admitted. -/
example :
    lengthRows.all (fun (written, number, keyMaximum, keyMinimum) =>
      let key := "[Tags/Amount For \"AB\"] > 0"
      ((form s!"\{\"pattern\":\"[0-9]+\",\"maxLength\":{written}}" s!"\{\"minLength\":2,\"maxLength\":{written}}").map
          fun dm => (verdict dm "FieldValueAsNumber(Code) > 0", verdict dm key,
            verdict dm dated)) ==
        some (number, keyMaximum, "MVK_WRONG_DATE_FORMAT_FOR_OP") &&
      ((form "{\"pattern\":\"[0-9]+\",\"maxLength\":15}" s!"\{\"minLength\":{written},\"maxLength\":3}").map
          (verdict · key)) == some keyMinimum) ∧
    ((form "{\"pattern\":\"[0-9]+\",\"maxLength\":15}" "{\"minLength\":2,\"maxLength\":3}").map
      (verdict · "FieldValueAsNumber(Code) > 0")) = some "admitted" ∧
    ((form "{\"pattern\":\"[0-9]+\",\"maxLength\":2}" "{\"minLength\":2,\"maxLength\":3}").map
      (verdict · dated)) = some "admitted" := by
  native_decide

end A12Kernel.Dm.WrittenMemberLocks
