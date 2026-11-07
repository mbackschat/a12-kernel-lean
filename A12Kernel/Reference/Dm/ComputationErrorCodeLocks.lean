import A12Kernel.Reference.Dm.ComputationCheck
import A12Kernel.Reference.Dm.GeneratedComputationRule

/-! # A computation's declared code and its suppression members

Format 29.5.0 gives a computation an optional `errorCode` that codes its generated validation; only an absent
or `null` member falls back to the name, and a declared code takes the name's place in the code alphabet (a12-dmkits
KF678). Format 29.8.0 adds the free-text `additionalParserInformation` beside the legacy `errorCodesToSuppress`
list (KF298). Both measured on kernel 31.3.1, 2026-11-07
([inbound record](../../../docs/sources/inbound-handbacks.md#src-inbound-2026-11-07) §5). The pragma's own
grammar is locked in `SuppressionPragmaLocks`.
-/

namespace A12Kernel.Dm.ComputationErrorCodeLocks

open Lean A12Kernel

private def element (kind name : String) (body : List (String × Json)) : Json :=
  Json.mkObj [("type", .str kind), ("id", .str s!"/Policy/{name}"), ("name", .str name), (kind, Json.mkObj body)]

/-- `Policy` with a Number `Amount` and the computation `name` of it, carrying `members` beside its target and
alternative. -/
private def policy (name : String) (members : List (String × Json)) : Json :=
  Json.mkObj [
    ("header", Json.mkObj [("id", "P_DM"), ("modelType", "document"), ("modelVersion", "29.8.0"),
      ("locales", Json.arr #[Json.mkObj [("code", "en_US")]])]),
    ("content", Json.mkObj [("modelInfo", Json.mkObj [("name", "P")]),
      ("modelConfig", Json.mkObj [("timeZone", "UTC"), ("conditionLanguage", Json.mkObj [("code", "en_US")])]),
      ("modelRoot", Json.mkObj [("rootGroups", Json.arr #[element "Group" "Policy" [("elements", Json.arr #[
        element "Field" "Amount" [("fieldType", Json.mkObj [("type", "NumberType"),
          ("NumberType", Json.mkObj [("maxFractionalDigits", toJson 0)])])],
        element "Computation" name ([("computedFieldRelPath", Json.str "../Amount"),
          ("computationAlternatives", Json.arr #[Json.mkObj [("operation", "5")]])] ++ members)])]])])])]

/-- The declaration notifications the model draws, `[]` when admitted, `none` when the reader refuses it. -/
private def notifications (name : String) (members : List (String × Json)) :
    Option (List DeclarationNotificationKind) :=
  match readModelWithAdmission (policy name members) with
  | .ok _ => some []
  | .error (.declaration (.notifications findings)) => some (findings.map (·.kind))
  | .error _ => none

/-- The code the generated validation fires under. -/
private def generatedCode (members : List (String × Json)) : Option String := do
  let dm ← (readModel (policy "Fee" members)).toOption
  let computation ← dm.computations.head?
  pure (← computation.generatedRule? .english).errorCode

/-- The class the computation check reports, `admitted`, or `no model`. -/
private def checkOutcome (members : List (String × Json)) : String :=
  match readModel (policy "Fee" members) with
  | .error _ => "no model"
  | .ok dm => match dm.computations.head? with
    | none => "no computation"
    | some computation => match checkComputation dm .english computation with
      | .ok _ => "admitted"
      | .error refusal => refusal.detail

private def code (value : Json) : List (String × Json) := [("errorCode", value)]

/-- Only absence or `null` takes the name; a declared code, a number's text included, codes the validation. -/
example :
    generatedCode [] = some "Fee" ∧ generatedCode (code .null) = some "Fee" ∧
    generatedCode (code "PREMIUM_MISMATCH") = some "PREMIUM_MISMATCH" ∧
    generatedCode (code "PREMIUM MISMATCH") = some "PREMIUM MISMATCH" ∧
    generatedCode (code (toJson (7 : Nat))) = some "7" := by
  native_decide

/-- The empty code is the discriminating row: it draws the missing-code class alone rather than falling back
to the name. A list leaves no model. -/
example :
    notifications "Fee" [] = some [] ∧ notifications "Fee" (code .null) = some [] ∧
    notifications "Fee" (code "PREMIUM_MISMATCH") = some [] ∧ notifications "Fee" (code "PRÄMIE") = some [] ∧
    notifications "Fee" (code (toJson (7 : Nat))) = some [] ∧
    notifications "Fee" (code "PREMIUM-MISMATCH") = some [.codeContent] ∧
    notifications "Fee" (code "") = some [.missingCode] ∧
    notifications "Fee" (code "   ") = some [.missingCode] ∧
    notifications "Fee" (code (Json.arr #["A"])) = none := by
  native_decide

/-- A declared code takes the name's place in the code alphabet: `Prem.ium` beside `PREMIUM` draws the name's
class alone, and `Premium` beside `PREM-IUM` the code's. -/
example :
    notifications "Prem.ium" (code "PREMIUM") = some [.nameContent] ∧
    notifications "Prem.ium" [] = some [.nameContent, .codeContent] ∧
    notifications "Premium" (code "PREM-IUM") = some [.codeContent] := by
  native_decide

private def text (value : Json) : String × Json := ("additionalParserInformation", value)
private def list (value : Json) : String × Json := ("errorCodesToSuppress", value)

/-- An explicit `null` in either member is absence, and a numeric text or entry is read as its text and then
refused by the preamble. A non-list legacy member refuses the model, even beside a stored text. -/
example :
    checkOutcome [text .null, list .null] = "admitted" ∧
    checkOutcome [text "@SuppressWarning(MVK_INVALID_COMPARE_DEC_PLACES)"] = "admitted" ∧
    checkOutcome [text (toJson (7 : Nat))] = "MVK_UNEXPECTED_TOKEN" ∧
    checkOutcome [list (Json.arr #[toJson (7 : Nat)])] = "MVK_UNEXPECTED_TOKEN" ∧
    checkOutcome [text "@SuppressWarning(MVK_INVALID_COMPARE_DEC_PLACES)", list "MVK_X"] = "no model" ∧
    checkOutcome [list (Json.mkObj [])] = "no model" := by
  native_decide

end A12Kernel.Dm.ComputationErrorCodeLocks
