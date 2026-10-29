import A12Kernel.Reference.Dm.ParallelValidation
import A12Kernel.Reference.Dm.EntryFrameFixture

/-! # `RuleGroup` over a group that declares no field, through the reader

A rule declared in a group with no field of its own, its error field outside that group, reads
`RuleGroup` as that empty group. The [empty-group models](../../../evidence/kernel-30.8.1/captures/k22-static-s4-2026-10-24/rulegroup/)
measure every group carrier asked drawing `MVK_GROUP_IS_EMPTY`, beside an admitted rule of the same
placement that reads the error field directly (`rg1`–`rg10`, `model check`, 2026-10-24). The `rule check`
route cannot author this placement, its precheck refusing an error field outside the rule's group, so
the rows are model rules.
-/

namespace A12Kernel.Dm.EmptyRuleGroupLocks
open A12Kernel A12Kernel.Dm Lean

private def model (condition : String) : Json :=
  let title := Json.mkObj [("type", "Field"), ("name", "Title"),
    ("Field", Json.mkObj [("fieldType", Json.mkObj [("type", "StringType")])])]
  let rule := Json.mkObj [("type", "Rule"), ("name", "R"), ("Rule", Json.mkObj [
    ("errorEntityRelPath", "../../Title"), ("errorCode", "R"), ("severity", "ERROR"),
    ("errorCondition", Json.str condition)])]
  let hollow := Json.mkObj [("type", "Group"), ("name", "Hollow"), ("Group", Json.mkObj [
    ("repeatability", toJson (1 : Nat)), ("elements", Json.arr #[rule])])]
  checkedEntryFrame <| Json.mkObj [("header", Json.mkObj [("locales", Json.arr #[Json.mkObj [("code", "en_US")]])]),
    ("content", Json.mkObj [("modelConfig", Json.mkObj [("conditionLanguage", Json.mkObj [("code", "en_US")])]),
      ("modelRoot", Json.mkObj [("rootGroups", Json.arr #[Json.mkObj [("type", "Group"), ("name", "Shop"),
        ("Group", Json.mkObj [("repeatability", toJson (1 : Nat)), ("elements", Json.arr #[title, hollow])])]])])])]

/-- The class the model's one rule draws, `none` when it is admitted. -/
private def ruleClass (condition : String) : Except String (Option String) := do
  let dm ← (readModel (model condition)).mapError reprStr
  let [rule] := dm.rules | throw "one rule expected"
  pure (match checkValidationRule dm .english rule with
    | .ok _ => none
    | .error refusal => refusal.kernelClass?.getD "unclassified")

example : (ruleClass "FieldFilled(/Shop/Title)").toOption = some none := by native_decide

example : ["NumberOfFilledFields(RuleGroup) > 0", "AtLeastOneFieldFilled(RuleGroup)", "NoFieldFilled(RuleGroup)",
    "GroupFilled(RuleGroup)", "AllFieldsFilled(RuleGroup)", "FieldValuesNotUnique(RuleGroup)", "Sum(RuleGroup) > 0",
    "NumberOfDifferentValues(RuleGroup) > 0", "GroupNotFilled(RuleGroup)"].all
      (fun condition => (ruleClass condition).toOption == some (some "MVK_GROUP_IS_EMPTY")) = true := by
  native_decide

end A12Kernel.Dm.EmptyRuleGroupLocks
