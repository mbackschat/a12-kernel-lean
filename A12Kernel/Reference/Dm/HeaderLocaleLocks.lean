import A12Kernel.Reference.Dm.Model
import A12Kernel.Reference.Dm.ModelConsistencyRead
import A12Kernel.Reference.Dm.FieldTypeDeclarationRead
import A12Kernel.Elaboration.DeclarationReport

/-! # How the DM-JSON readers read a header's declared locales

Each expectation is a Kernel row of the
[header locale codes](../../../docs/sources/model-structure-and-declaration-probes.md#src-header-locale-codes)
probe (`dmtool model check`, Kernel 30.8.1, 2026-10-29), declared beside "en_US" as the probe declares
it, or of peer KF290's message rows. The probe's `MVK_SUPP_LANGUAGES_DUPLICATE` rows are not locked: that
model-level class is not produced, so those models read as built. -/

namespace A12Kernel.Dm.HeaderLocaleLocks

open Lean A12Kernel

private def model (locales : Json) (elements : List Json := []) : Json :=
  Json.mkObj [("header", Json.mkObj [("locales", locales)]),
    ("content", Json.mkObj [("modelRoot", Json.mkObj [("rootGroups", Json.arr #[Json.mkObj [("type", "Group"),
      ("id", "/P"), ("name", "P"), ("Group", Json.mkObj [("elements", Json.arr elements.toArray)])]])])])]

private def declaring (codes : List String) : Json :=
  model (Json.arr (("en_US" :: codes).map fun code => Json.mkObj [("code", Json.str code)]).toArray)

private def bare (codes : List String) : Json := model (Json.arr (codes.map Json.str).toArray)

/-- What a reader makes of the model. -/
private inductive Verdict where
  | builds | notBuilt | unreadable | outsideProfile
  deriving DecidableEq

private def failed (message : String) : Verdict :=
  if (message.splitOn "outside the represented profile").length > 1 then .outsideProfile else .unreadable

/-- The verdict all three readers agree on, `none` when they disagree: the model reader's failure covers
both an unreadable and an unbuilt model, the consistency and declaration readers' outcomes separate them. -/
private def verdict (json : Json) : Option Verdict :=
  let consistency := match checkModelConsistency json with
    | .error message => failed message
    | .ok (.notBuilt _ _) => .notBuilt
    | .ok (.checked _) => .builds
  let declaration := match fieldTypeDeclarationNotifications json fun _ => .compiled fun _ => true with
    | .error message => failed message
    | .ok labels => if labels.any (·.1 == modelNotBuiltLabel) then .notBuilt else .builds
  let model := match readModel json with
    | .error message => failed message
    | .ok _ => .builds
  let modelAgrees := match consistency with
    | .builds => model == .builds
    | .outsideProfile => model == .outsideProfile
    | .notBuilt | .unreadable => model == .unreadable
  if consistency == declaration && modelAgrees then some consistency else none

/-- A tag-refused code, a private-use tail and a case variant build, as do `iw` beside `de` and a bare
text the dmtool index never parses (rows `s00`–`s13`, `s20`–`s27`, `s42`, `s49`, `p05`, `p08`, `t03`). -/
example :
    [["de"], ["und"], ["DE_419"], ["de__1996"], ["de_CH_x"], ["1_419"], ["de_CH_x_abc"], ["en_US_POSIX_x"],
      ["iw", "de"], ["de_CH_POSIX", "de_CH_posix"]].all (fun codes => verdict (declaring codes) == some .builds) ∧
    verdict (bare ["en_US", "de__1996"]) = some .builds := by
  native_decide

/-- A code the parser refuses leaves the model unreadable, bare or not (rows `s31`, `s32`, `s43`, `s48`). -/
example :
    [["en_us"], ["zh_Hans_CN"], ["de_CH-x"], ["en_US-POSIX"]].all (fun codes => verdict (declaring codes) == some .unreadable) ∧
    verdict (bare ["en_US", "en_us"]) = some .unreadable := by
  native_decide

/-- An empty language and two codes naming one locale fail the build, bare or not (rows `s14`, `s46`,
`s47`, `p00`–`p04`, `p06`, `t01`). -/
example :
    [["_CH"], ["_US_x"], [""], ["iw", "he"], ["ji", "yi"], ["in", "id"], ["de_CH", "de-CH"], ["DE_419", "de_419"],
      ["en_US"]].all (fun codes => verdict (declaring codes) == some .notBuilt) ∧
    verdict (bare ["en_US", "de_CH", "de-CH"]) = some .notBuilt := by
  native_decide

/-- A bare uppercase pair and a non-ASCII code are outside the represented profile, as "ja_JP_JP" is; the
Kernel fails the build on `US` and `CH` and admits `ée`. -/
example :
    [["US"], ["CH"], ["ée"], ["ja_JP_JP"]].all (fun codes => verdict (declaring codes) == some .outsideProfile) := by
  native_decide

/-- A rule's message answers the declared locale its parsed locale equals: "en_US" answers a declared
`en-US` and the reverse, while it does not answer a declared `en` (peer KF290 and KF158). -/
example :
    let presence (code locale : String) :=
      messagePresence (((builtHeaderLocales (model (Json.arr #[Json.mkObj [("code", Json.str code)]]))).toOption.getD []).map (·.key))
        ((localizedTextValue (Json.arr #[Json.mkObj [("locale", Json.str locale), ("text", "t")]])).toOption.getD [])
    (presence "en-US" "en_US").prefixed = [] ∧ (presence "en_US" "en-US").prefixed = [] ∧
    (presence "en" "en_US").prefixed = [.errorMessageMissing] := by
  native_decide

private def hintField (locales : List String) : Json :=
  Json.mkObj [("type", "Field"), ("id", "/P/H"), ("name", "H"), ("Field", Json.mkObj [("fieldType", Json.mkObj [
    ("type", "StringType"), ("StringType", Json.mkObj [("hintList", Json.arr (locales.map fun locale =>
      Json.mkObj [("locale", Json.str locale), ("values", Json.arr #["a"])]).toArray)])])])]

/-- Two hint-list entries for one locale fail the build, "en_US" beside `en-US` included (spec/01 §1.2),
while entries for two locales do not. -/
example :
    let labels (locales : List String) :=
      ((fieldTypeDeclarationNotifications (model (Json.arr #[Json.mkObj [("code", "en_US")]]) [hintField locales])
        fun _ => .compiled fun _ => true).toOption.getD []).map (·.1)
    labels ["en_US", "en-US"] = [modelNotBuiltLabel] ∧ !(labels ["en_US", "de_DE"]).contains modelNotBuiltLabel := by
  native_decide

end A12Kernel.Dm.HeaderLocaleLocks
