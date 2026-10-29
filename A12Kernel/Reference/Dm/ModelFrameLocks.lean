import A12Kernel.Reference.Dm.Model
import A12Kernel.Reference.Dm.ModelConsistencyRead
import A12Kernel.Reference.Dm.FieldTypeDeclarationRead
import A12Kernel.Elaboration.DeclarationReport

/-! # How the DM-JSON readers bind a model's frame

Each expectation is a Kernel row of peer KF650 (a12-dmkits `413880f4b`,
`CheckerModelFrameAgreementTest`, Kernel gate, kernel 30.8.1, 2026-10-29), and every row the
`dmtool model check` grid admits agrees with the
[model frame members](../../../docs/sources/model-structure-and-declaration-probes.md#src-model-frame-members)
checkpoint. A member the Kernel cannot bind leaves no model, a read failure in every reader. The four
check-only shapes build a model whose consistency check fails without a class: the consistency and
declaration readers report the unbuilt model, and the evaluation reader refuses it as the runtime route
does ([check route](../../../docs/sources/model-structure-and-declaration-probes.md#src-model-frame-check-route)).

Three kinds of row are deliberately absent. Rows the Kernel answers with a class of its own: an absent
`modelInfo.name`, a time zone it does not know and a version it refuses. A `modelVersion` written as an
object or an array, which neither source separates from a check-only shape. And a supported character
that is neither one character nor a range, on which the three readers do not agree. -/

namespace A12Kernel.Dm.ModelFrameLocks

open Lean A12Kernel

private def rule (condition : String) : Json :=
  Json.mkObj [("type", "Rule"), ("id", "/Form/R1"), ("name", "R1"), ("Rule", Json.mkObj [
    ("errorEntityRelPath", "../Gate"), ("errorCode", "R1"), ("errorCondition", Json.str condition),
    ("severity", "ERROR"), ("errorMessage", Json.arr #[Json.mkObj [("locale", "en_US"), ("text", "m")]])])]

/-- A sound model with every frame member written: a form with one String field and one rule. -/
private def base (condition : String := "FieldFilled(Gate)") : Json :=
  Json.mkObj [
    ("header", Json.mkObj [("id", "Frame_DM"), ("modelType", "document"), ("modelVersion", "28.4.0"),
      ("locales", Json.arr #[Json.mkObj [("code", "en_US")]])]),
    ("content", Json.mkObj [("modelInfo", Json.mkObj [("name", "Frame")]), ("modelConfig", Json.mkObj []),
      ("typeDefinitions", Json.arr #[]),
      ("modelRoot", Json.mkObj [("rootGroups", Json.arr #[Json.mkObj [("type", "Group"), ("id", "/Form"),
        ("name", "Form"), ("Group", Json.mkObj [("elements", Json.arr #[
          Json.mkObj [("type", "Field"), ("id", "/Form/Gate"), ("name", "Gate"),
            ("Field", Json.mkObj [("fieldType", Json.mkObj [("type", "StringType")])])],
          rule condition])])]])])])]

private def sound : Json := base

/-- `json` with the member at `path` replaced by `value`, or removed when `value` is `none`. -/
private def edited : List String → Option Json → Json → Json
  | [], _, json => json
  | [key], some value, json => json.setObjVal! key value
  | [key], none, .obj members => .obj (members.erase key)
  | key :: rest, value, json => match json.getObjVal? key with
      | .ok child => json.setObjVal! key (edited rest value child)
      | .error _ => json

/-- What all three readers make of a model, `none` when they disagree. -/
private inductive Verdict where
  | builds | noModel | checkOnly
  deriving DecidableEq

private def verdict (json : Json) : Option Verdict :=
  let model := (readModel json).isOk
  let consistency := match checkModelConsistency json with
    | .error _ => some Verdict.noModel
    | .ok (.notBuilt _ _) => some .checkOnly
    | .ok (.checked _) => some .builds
  let declaration := match fieldTypeDeclarationNotifications json fun _ => .compiled fun _ => true with
    | .error _ => some Verdict.noModel
    | .ok labels => some (if labels.any (·.1 == modelNotBuiltLabel) then .checkOnly else .builds)
  if consistency == declaration && model == (consistency == some .builds) then consistency else none

/-- The seven shapes the letter writes each member as; `none` removes it. -/
private def shapes : List (String × Option Json) :=
  [("absent", none), ("null", some .null), ("{}", some (Json.mkObj [])), ("[]", some (Json.arr #[])),
    ("\"x\"", some (Json.str "x")), ("5", some (toJson (5 : Nat))), ("true", some (Json.bool true))]

/-- The rows of one member, its expected verdict for each shape it is locked at. -/
private def member (path : List String) (expected : String → Option Verdict) : List (String × Json × Option Verdict) :=
  shapes.filterMap fun (shape, value) =>
    (expected shape).map fun verdict => (s!"{path} {shape}", edited path value sound, some verdict)

private def scalar (shape : String) : Bool := shape == "\"x\"" || shape == "5" || shape == "true"

/-- A text member binds any scalar as its text and leaves no model as a container; `null` binds unless
the Kernel marks the member non-null. -/
private def text (nonNull : Bool) (shape : String) : Verdict :=
  if shape == "{}" || shape == "[]" || (nonNull && shape == "null") then .noModel else .builds

/-- A list member binds an array and its absence; `null` binds unless the member is non-null. -/
private def list (nonNull : Bool) (shape : String) : Verdict :=
  if shape == "[]" || shape == "absent" || (!nonNull && shape == "null") then .builds else .noModel

/-- An object member binds an object, and its absence where the member is optional. -/
private def object (optional : Bool) (shape : String) : Verdict :=
  if shape == "{}" || (optional && shape == "absent") then .builds else .noModel

private def rows : List (String × Json × Option Verdict) :=
  (["id", "modelType", "description"].flatMap fun key => member ["header", key] (some <| text false ·)) ++
  (["variant", "branch", "revision", "comment", "joinedModelsInfo"].flatMap fun key =>
    member ["content", "modelInfo", key] (some <| text false ·)) ++
  member ["content", "modelInfo", "name"] (fun shape => if shape == "absent" then none else some (text true shape)) ++
  member ["content", "modelConfig", "decimalSeparator"] (some <| text true ·) ++
  member ["content", "modelConfig", "timeZone"] (fun shape => if scalar shape then none else some (text true shape)) ++
  member ["header", "modelVersion"] (fun shape =>
    if shape == "absent" || shape == "null" then some .checkOnly else none) ++
  (["labels", "annotations", "modelReferences"].flatMap fun key => member ["header", key] (some <| list false ·)) ++
  member ["header", "locales"] (fun shape =>
    some (if shape == "absent" || shape == "null" then .checkOnly else list false shape)) ++
  member ["content", "typeDefinitions"] (some <| list true ·) ++
  member ["content", "modelConfig", "supportedCharacters"] (some <| list true ·) ++
  member ["content", "modelRoot", "rootGroups"] (some <| list true ·) ++
  member ["header"] (fun shape => some (if shape == "{}" then .checkOnly else object false shape)) ++
  member ["content"] (fun shape => some (if shape == "{}" then .checkOnly else object false shape)) ++
  member ["content", "modelInfo"] (fun shape =>
    if shape == "{}" then none else some (if shape == "absent" then .checkOnly else object false shape)) ++
  member ["content", "modelConfig"] (some <| object true ·) ++
  member ["content", "modelRoot"] (some <| object true ·)

/-- Every frame member at every shape the letter locks, in all three readers. -/
example : rows.all fun (_, json, expected) => verdict json == expected := by
  native_decide

private def language (value : Json) (condition : String := "FieldFilled(Gate)") : Json :=
  edited ["content", "modelConfig", "conditionLanguage"] (some value) (base condition)

/-- A condition language is a text or an object whose `code` is a text, and a bare "de_DE" declares
German conditions exactly as `{"code":"de_DE"}` does; an unsupported code and every other shape leave no
model. -/
example :
    verdict (language (Json.str "en_US")) = some .builds ∧
    verdict (language (Json.mkObj [("code", "en_US")])) = some .builds ∧
    verdict (language (Json.str "de_DE") "FeldAngegeben(Gate)") = some .builds ∧
    verdict (language (Json.mkObj [("code", "de_DE")]) "FeldAngegeben(Gate)") = some .builds ∧
    ((readModel (language (Json.str "de_DE") "FeldAngegeben(Gate)")).toOption.map (·.conditionLanguage)) = some "de_DE" ∧
    [Json.mkObj [("code", "zz")], Json.mkObj [("code", "")]].all (fun value => verdict (language value) == some .noModel) ∧
    [Json.null, Json.mkObj [], Json.arr #[], toJson (5 : Nat), Json.bool true, Json.mkObj [("code", Json.null)],
      Json.mkObj [("code", Json.mkObj [])], Json.mkObj [("x", "en_US")]].all
      (fun value => verdict (language value) == some .noModel) := by
  native_decide

private def characters (entries : Array Json) : Json :=
  edited ["content", "modelConfig", "supportedCharacters"] (some (Json.arr entries)) sound

/-- A supported-character entry binds a text, a number or a boolean, and a container leaves no model,
while a `null` entry costs only the check. -/
example :
    [#[Json.str "a"], #[Json.str "a-z"], #[toJson (5 : Nat)]].all (fun entries => verdict (characters entries) == some .builds) ∧
    [#[Json.mkObj []], #[Json.arr #[]]].all (fun entries => verdict (characters entries) == some .noModel) ∧
    verdict (characters #[Json.null]) = some .checkOnly := by
  native_decide

/-- Over the sixteen presence combinations of the version, the model info, the configuration and the
model type, the check runs exactly when the version and the model info are both present; the last two
are the control that the rows do not merely count removals. The grid's broken-rule twin is not locked:
these readers do not judge a rule's condition, so it draws the sound rule's verdicts. -/
example :
    let members := [["header", "modelVersion"], ["content", "modelInfo"], ["content", "modelConfig"], ["header", "modelType"]]
    (List.range 16).all fun kept =>
      let absent := (members.zipIdx.filter fun (_, i) => kept &&& (1 <<< i) == 0).map (·.1)
      let json := absent.foldl (fun json path => edited path none json) sound
      verdict json == some (if absent.any (members.take 2).contains then .checkOnly else .builds) := by
  native_decide

end A12Kernel.Dm.ModelFrameLocks
