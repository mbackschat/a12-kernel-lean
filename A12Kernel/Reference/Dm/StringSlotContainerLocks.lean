import A12Kernel.Reference.Dm.Model

/-! # A JSON container in a string slot leaves no model

Kernel 31.1.1 refuses to read a model whose rule `errorCode`, `errorEntityRelPath` or `errorCondition`, whose
computation alternative's `operation` or `precondition`, or whose group `indexFieldName` holds an object or an
array, each of the four shapes `{}`, an object with content, `[]` and an array holding a text, beside an admitted
control (a12-dmkits `StringSlotContainerLawsTest` at `35a09951f`, KF304, extended to `errorCode` by Letter G;
[inbound record](../../../docs/sources/inbound-handbacks.md#src-inbound-2026-11-05b)). Before the change the DM
reader read a container in the rule's path and condition and in the precondition as an empty text.
-/

namespace A12Kernel.Dm.StringSlotContainerLocks

open Lean A12Kernel

private def field (name : String) (fieldType : Json) : Json :=
  Json.mkObj [("type", "Field"), ("id", .str s!"/P/{name}"), ("name", .str name),
    ("Field", Json.mkObj [("fieldType", fieldType)])]

private def number : Json :=
  Json.mkObj [("type", "NumberType"), ("NumberType", Json.mkObj [("maxFractionalDigits", toJson 0)])]

/-- `P` with Numbers `A` and `B`, a repeatable `Rows` indexed by its String `K`, a rule on `A` and a computation of
`B`, each element's body passed through the edit given for it. -/
private def model (rule alternative group : Json → Json) : Json :=
  Json.mkObj [
    ("header", Json.mkObj [("id", "P_DM"), ("modelType", "document"), ("modelVersion", "29.4.0"),
      ("locales", Json.arr #[Json.mkObj [("code", "en_US")]])]),
    ("content", Json.mkObj [("modelInfo", Json.mkObj [("name", "P")]),
      ("modelConfig", Json.mkObj [("timeZone", "UTC"), ("conditionLanguage", Json.mkObj [("code", "en_US")])]),
      ("modelRoot", Json.mkObj [("rootGroups", Json.arr #[Json.mkObj [("type", "Group"), ("id", "/P"), ("name", "P"),
        ("Group", Json.mkObj [("elements", Json.arr #[field "A" number, field "B" number,
          Json.mkObj [("type", "Group"), ("id", "/P/Rows"), ("name", "Rows"), ("Group", group (Json.mkObj [
            ("repeatability", toJson 3), ("indexFieldName", "K"),
            ("elements", Json.arr #[field "K" (Json.mkObj [("type", "StringType")])])]))],
          Json.mkObj [("type", "Rule"), ("id", "/P/R"), ("name", "R"), ("Rule", rule (Json.mkObj [
            ("errorEntityRelPath", "../A"), ("errorCode", "C"), ("severity", "ERROR"), ("errorCondition", "FieldFilled(A)"),
            ("errorMessage", Json.arr #[Json.mkObj [("locale", "en_US"), ("text", "x")]])]))],
          Json.mkObj [("type", "Computation"), ("id", "/P/Co"), ("name", "Co"), ("Computation", Json.mkObj [
            ("computedFieldRelPath", "../B"),
            ("computationAlternatives", Json.arr #[alternative (Json.mkObj [("operation", "42"), ("precondition", "FieldFilled(A)")])]),
            ("errorMessage", Json.arr #[Json.mkObj [("locale", "en_US"), ("text", "x")]])])]])])]])])])]

private def containers : List Json :=
  [Json.mkObj [], Json.mkObj [("a", toJson 1)], Json.arr #[], Json.arr #["x"]]

private def builds (json : Json) : Bool := (readModel json).isOk

/-- The control builds, and every container in every slot leaves no model. A fractional number, unmeasured in
these slots, still builds: the change refuses containers only. -/
example :
    builds (model id id id) ∧
    (["errorCode", "errorEntityRelPath", "errorCondition"].all fun slot =>
      containers.all fun container => !builds (model (·.setObjVal! slot container) id id)) ∧
    (["operation", "precondition"].all fun slot =>
      containers.all fun container => !builds (model id (·.setObjVal! slot container) id)) ∧
    (containers.all fun container => !builds (model id id (·.setObjVal! "indexFieldName" container))) ∧
    builds (model (·.setObjVal! "errorCondition" (toJson (1.5 : Float))) id id) ∧
    builds (model id (·.setObjVal! "precondition" (toJson (1.5 : Float))) id) := by
  native_decide

end A12Kernel.Dm.StringSlotContainerLocks
