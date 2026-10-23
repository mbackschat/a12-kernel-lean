import A12Kernel.Reference.Dm.ModelComputation

namespace A12Kernel.Dm.DeclarationAdmissionLocks

open Lean

private def input (name : String) (code : Option Json) (extra : List (String × Json) := []) : Json :=
  Json.mkObj [("content", Json.mkObj [
    ("modelRoot", Json.mkObj [("rootGroups", toJson #[Json.mkObj [
      ("type", toJson "Group"), ("name", toJson "Form"),
      ("Group", Json.mkObj [("elements", toJson #[
        Json.mkObj [("type", toJson "Field"), ("name", toJson "Value"),
          ("Field", Json.mkObj [("fieldType", Json.mkObj [("type", toJson "StringType")])])],
        Json.mkObj [
        ("type", toJson "Rule"), ("name", toJson name),
        ("Rule", Json.mkObj ([("errorCondition", toJson "FieldFilled(Value)"),
          ("errorEntityRelPath", toJson "../Value")] ++
          code.toList.map (fun value => ("errorCode", value)) ++ extra))]])])]] )])])]

example : (readModel (input "Ordinary" (some (.str "CODE")))).isOk = true := by native_decide
example : (readModel (input "Ordinary" none)).isOk = false := by native_decide
example : (readModel (input "Ordinary" (some (.str "   ")))).isOk = false := by native_decide
example : (readModel (input "Ordinary" (some .null))).isOk = false := by native_decide
example : (readModel (input "" (some (.str "CODE")))).isOk = false := by native_decide
example : (readModel (input "1Rule" (some (.str "CODE")))).isOk = false := by native_decide
example : (readModel (input "Rule.Dot" (some (.str "CODE")))).isOk = false := by native_decide
example : (readModel (input "Vk_VkRule" (some (.str "CODE")))).isOk = false := by native_decide
example : ((readModel (input "Ordinary" (some (toJson (7 : Nat))))).toOption.bind
    (·.rules.head?)).map (·.errorCode) = some "7" := by native_decide

private def failure (name : String) (code : Option Json) (extra : List (String × Json) := []) :
    Option ModelReadFailure :=
  match readModelWithAdmission (input name code extra) with
  | .ok _ => none
  | .error error => some error

private def findings (name : String) (kinds : List DeclarationNotificationKind) : ModelReadFailure :=
  .declaration (.notifications (kinds.map fun kind => { declaration := ["Form", name], kind }))

example : failure "Ordinary" none = some (findings "Ordinary" [.missingCode, .emptyCode]) := by native_decide
example : failure "Ordinary" (some (.str "")) =
    some (findings "Ordinary" [.missingCode, .emptyCode]) := by native_decide
example : failure "Ordinary" (some (.str "   ")) =
    some (findings "Ordinary" [.missingCode]) := by native_decide
example : failure "Ordinary" (some (.str "\u000b")) =
    some (findings "Ordinary" [.missingCode]) := by native_decide
example : failure "Ordinary" (some (.str "\u00a0")) =
    some (findings "Ordinary" [.codeContent]) := by native_decide
example : failure "Ordinary" (some (.str "A-B")) =
    some (findings "Ordinary" [.codeContent]) := by native_decide
example : failure "Ordinary" (some (.str " Ä_1 B ")) = none := by native_decide
example : failure "xmlRule" (some (.str "CODE")) = none := by native_decide
example : failure "1Rule" (some (.str "CODE")) = some (findings "1Rule" [.nameContent]) := by native_decide
example : failure "Rule.Dot" (some (.str "CODE")) = some (findings "Rule.Dot" [.nameContent]) := by native_decide
example : failure "_Rule" (some (.str "CODE")) = some (findings "_Rule" [.nameContent]) := by native_decide
example : failure "Vk_VkRule" (some (.str "")) =
    some (findings "Vk_VkRule" [.reservedName, .missingCode, .emptyCode]) := by native_decide
example : failure "Bad.Name" (some (.str "")) =
    some (findings "Bad.Name" [.nameContent, .missingCode, .emptyCode]) := by native_decide
example : failure "vk_vk.Bad" (some (.str "CODE")) =
    some (findings "vk_vk.Bad" [.nameContent]) := by native_decide
example : failure "" (some (.str "")) =
    some (.declaration (.buildFailure ["Form", ""])) := by native_decide
example : failure "Vk_VkRule" (some .null) =
    some (.declaration (.unreadable ["Form", "Vk_VkRule"] "errorCode")) := by native_decide
example : failure "Ordinary" (some (Json.mkObj [])) =
    some (.declaration (.unreadable ["Form", "Ordinary"] "errorCode")) := by native_decide

/- Both alphabets judge the value after Java's `trim`, which keeps an em space; a number written as
   the code is its text; a supplementary scalar draws the repertoire notification in place of every
   alphabet class (October 21 letter §2.5). -/
example :
    failure "Probe\t" (some (.str "\tC")) = none ∧
    failure "Probe\u2003" (some (.str "C")) = some (findings "Probe\u2003" [.nameContent]) ∧
    failure "Ordinary" (some (.str "C\u2003")) = some (findings "Ordinary" [.codeContent]) ∧
    failure "Probe😀" (some (.str "C😀")) = some (findings "Probe😀" [.supplementaryCharacter]) ∧
    failure "Ordinary" (some (toJson (-7 : Int))) = some (findings "Ordinary" [.codeContent]) := by
  native_decide

private def deleted : List (String × Json) :=
  [("variantFilter", Json.mkObj [("filterType", "ONLY"), ("variants", Json.arr #["Other"])])]

/- A rule the variant filter deletes keeps only the empty-code notification, which reads emptiness and
   not blankness, so neither its name nor a blank code is judged and a deleted blank name builds
   (October 21 letter §2.6, §2.11). -/
example :
    failure "Ordinary" (some (.str "")) deleted = some (findings "Ordinary" [.emptyCode]) ∧
    failure "Ordinary" none deleted = some (findings "Ordinary" [.emptyCode]) ∧
    failure "Ordinary" (some (.str " ")) deleted = none ∧
    failure "\t" (some (.str "CODE")) deleted = none ∧
    failure "1Rule" (some (.str "A-B")) deleted = none ∧
    failure "\t" (some (.str "CODE")) = some (.declaration (.buildFailure ["Form", "\t"])) := by
  native_decide

private def checkedRule (name code : String) : Option (Bool × Option DeclarationAdmissionFailure) := do
  let model ← (readModel (input "Ordinary" (some (.str "CODE")))).toOption
  let rule ← model.rules.head?
  match checkRule model .english { rule with name, errorCode := code } with
  | .ok _ => some (true, none)
  | .error error => some (false, error.declarationFailure?)

example : checkedRule "Ordinary" "CODE" = some (true, none) := by native_decide
example : checkedRule "vk_vkRule" "   " = some (false, some (.notifications [
    { declaration := ["Form", "vk_vkRule"], kind := .reservedName },
    { declaration := ["Form", "vk_vkRule"], kind := .missingCode }])) := by native_decide

private def computation (name : String) : Option (Bool × Option DeclarationAdmissionFailure) := do
  let model ← (readModel (input "Ordinary" (some (.str "CODE")))).toOption
  match lowerComputation model.flat .english {
      group := ["Form"], name, targetRelPath := "../Value", commonPrecondition := none,
      alternatives := [{ precondition := none, operation := "\"result\"" }], errorCodesToSuppress := [] } with
  | .ok _ => some (true, none)
  | .error error => some (false, error.declarationFailure?)

example : computation "Ordinary" = some (true, none) := by native_decide
example : computation "Vk_VkCalculation" = some (false, some (.notifications [
    { declaration := ["Form", "Vk_VkCalculation"], kind := .reservedName }])) := by native_decide

-- A computation's name meets the error-code content law as well as the name law (`cpn-dash`,
-- `cpn-umlaut`, `cpn-digit`); the code alphabet admits an umlaut and a digit but not a hyphen.
example : computation "Calc-x" = some (false, some (.notifications [
    { declaration := ["Form", "Calc-x"], kind := .nameContent },
    { declaration := ["Form", "Calc-x"], kind := .codeContent }])) := by native_decide

example : computation "Prem😀" = some (false, some (.notifications [
    { declaration := ["Form", "Prem😀"], kind := .supplementaryCharacter }])) ∧
    computation "Premium " = some (true, none) := by native_decide
example : computation "Calcä" = some (false, some (.notifications [
    { declaration := ["Form", "Calcä"], kind := .nameContent }])) := by native_decide
example : computation "1Calc" = some (false, some (.notifications [
    { declaration := ["Form", "1Calc"], kind := .nameContent }])) := by native_decide

example : (match ExecutableDeclaration.admitAll [
    { group := ["Form"], name := "vk_vkRule", kind := .rule (.text "") },
    { group := ["Form"], name := "Other", kind := .rule .unreadable }] with
      | .ok _ => none | .error error => some error) =
    some (.unreadable ["Form", "Other"] "errorCode") := by native_decide

example : DeclarationNotificationKind.nameContent.diagnostic? = none ∧
    DeclarationNotificationKind.missingCode.diagnostic? = some .errorCodeMissing := by native_decide

end A12Kernel.Dm.DeclarationAdmissionLocks
