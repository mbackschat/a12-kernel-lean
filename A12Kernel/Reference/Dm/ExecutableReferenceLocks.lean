import A12Kernel.Reference.Dm.ParallelValidation
import A12Kernel.Elaboration.ValidationMessageRendering

/-! # A reference naming a rule or a computation names nothing

Kernel 31.1.1 answers a path naming a rule or a computation as one naming nothing in every slot measured: a
computation's target, a rule's error target, a condition operand and a message parameter, each control naming a
field being admitted (a12-dmkits `CheckerExecutableAsReferenceAgreementTest` at `35a09951f`, KF674;
[inbound record](../../../docs/sources/inbound-handbacks.md#src-inbound-2026-11-05b)). The rows below hold Lean's
answer for each executable path equal to its answer for a path naming nothing, and for the error target that
answer is the Kernel's pair, the declaration gate's absent error field.
-/

namespace A12Kernel.Dm.ExecutableReferenceLocks

open Lean A12Kernel

private def element (kind id name : String) (body : List (String × Json)) : Json :=
  Json.mkObj [("type", .str kind), ("id", .str id), ("name", .str name), (kind, Json.mkObj body)]

private def message : Json := Json.arr #[Json.mkObj [("locale", "en_US"), ("text", "x")]]

/-- `Policy` with `Holder`, `Premium` and `Note`, the rule `HolderRequired`, the computation `Fee` of `Premium`
and, when a target is given, a second computation `Copy` targeting it. -/
private def policy (copyTarget : Option String := none) : Json :=
  Json.mkObj [
    ("header", Json.mkObj [("id", "P_DM"), ("modelType", "document"), ("modelVersion", "29.4.0"),
      ("locales", Json.arr #[Json.mkObj [("code", "en_US")]])]),
    ("content", Json.mkObj [("modelInfo", Json.mkObj [("name", "P")]),
      ("modelConfig", Json.mkObj [("timeZone", "UTC"), ("conditionLanguage", Json.mkObj [("code", "en_US")])]),
      ("modelRoot", Json.mkObj [("rootGroups", Json.arr #[element "Group" "/Policy" "Policy" [("elements", Json.arr (#[
        element "Field" "/Policy/Holder" "Holder" [("fieldType", Json.mkObj [("type", "StringType")])],
        element "Field" "/Policy/Premium" "Premium" [("fieldType", Json.mkObj [("type", "NumberType"),
          ("NumberType", Json.mkObj [("maxFractionalDigits", toJson 0)])])],
        element "Field" "/Policy/Note" "Note" [("fieldType", Json.mkObj [("type", "StringType")])],
        element "Rule" "/Policy/HolderRequired" "HolderRequired" [("errorEntityRelPath", "../Holder"),
          ("errorCode", "HR"), ("severity", "ERROR"), ("errorCondition", "FieldNotFilled(Holder)"), ("errorMessage", message)],
        element "Computation" "/Policy/Fee" "Fee" [("computedFieldRelPath", "../Premium"),
          ("computationAlternatives", Json.arr #[Json.mkObj [("operation", "5")]]), ("errorMessage", message)]] ++
        (copyTarget.map fun target => #[element "Computation" "/Policy/Copy" "Copy" [("computedFieldRelPath", .str target),
          ("computationAlternatives", Json.arr #[Json.mkObj [("operation", "5")]]), ("errorMessage", message)]]).getD #[]))]])])])]

/-- A rule in `Policy` reporting on `errorPath` under `condition`. -/
private def probeRule (errorPath condition : String) : DmRule :=
  { group := ["Policy"], name := "R", severity := "ERROR", errorCode := "R", condition
    errorEntityRelPath := errorPath }

/-- The rule's admission: `none` when admitted, else its classes. -/
private def ruleClass (errorPath condition : String) : Option String :=
  match readModel policy with
  | .error _ => some "no model"
  | .ok dm =>
      match checkValidationRule dm .english (probeRule errorPath condition) with
      | .ok _ => none
      | .error refusal => some (" ".intercalate refusal.kernelClasses)

/-- The named class of a message beside a rule reading `Note`, `none` when admitted. -/
private def messageClass (text : String) : Option String := do
  let dm ← (readModel policy).toOption
  let .ordinary checked ← (checkValidationRule dm .english (probeRule "../Note" "FieldFilled(Note)")).toOption
    | none
  match elaborateValidationMessageTemplate dm.flat .english (.rule checked) text with
  | .ok _ => none
  | .error error => some ((error.namedRuleDiagnostic?.map (·.kernelCode)).getD "unclassed")

/-- The reader's refusals of the model whose `Copy` targets `target`. -/
private def targetRefusals (target : String) : Option (List String) :=
  (readModel (policy (some target))).toOption.map (·.refusals.map (·.2))

private def notFound : Option (List String) := some ["codeless:computed-field-not-found"]

/-- The declaration gate's pair for an absent error field. -/
private def missing : Option String := some "MVK_ERROR_FIELD_MISSING MVK_MISSING_ERROR_FIELD"

/-- Each slot answers an executable's path as it answers a path naming nothing, beside an admitted control. -/
example :
    targetRefusals "../Note" = some [] ∧
    targetRefusals "../HolderRequired" = notFound ∧ targetRefusals "../Fee" = notFound ∧
    targetRefusals "../Nothing" = notFound ∧
    ruleClass "../Note" "FieldFilled(Note)" = none ∧
    ruleClass "../HolderRequired" "FieldFilled(Note)" = missing ∧
    ruleClass "../Fee" "FieldFilled(Note)" = missing ∧
    ruleClass "../Nothing" "FieldFilled(Note)" = missing ∧
    ruleClass "../Nothing" "FieldFilled(Nowhere" = missing ∧
    ruleClass "../Note" "FieldFilled(Note) And FieldFilled(Holder)" = none ∧
    ruleClass "../Note" "FieldFilled(Note) And FieldFilled(HolderRequired)" = some "MVK_INVALID_ENTITY" ∧
    ruleClass "../Note" "FieldFilled(Note) And FieldFilled(/Policy/HolderRequired)" = some "MVK_INVALID_ENTITY" ∧
    ruleClass "../Note" "FieldFilled(Note) And FieldFilled(Fee)" = some "MVK_INVALID_ENTITY" ∧
    messageClass "a $Note$" = none ∧
    messageClass "a $HolderRequired$" = some "INVALID_ENTITY" := by
  native_decide

end A12Kernel.Dm.ExecutableReferenceLocks
