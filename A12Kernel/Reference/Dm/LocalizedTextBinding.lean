import Lean.Data.Json
import A12Kernel.Reference.Dm.LocaleSpelling
import A12Kernel.Reference.Dm.ModelFrame

/-! # How the Kernel's DM-JSON reader binds a localized-text member

A label, helper text, description or message is a localized-text member: entries of a `locale` and a
`text`. The Kernel binds every such member before any variant filter, so a member it cannot bind leaves
no model, a read failure here and never a Kernel class (peer KF646, measured 2026-10-29 on twelve
carriers, `docs/sources/inbound-handbacks.md#src-inbound-2026-10-29`):

* The member's own value is iterated as a JSON node: a list yields its elements, an object its values,
  and any other scalar nothing, so `"x"`, `5` and `[]` bind with no text. `null` is unbindable.
* Each entry must carry a string `locale` that parses as a locale and a string `text`; an entry that is
  not an object, or lacks either key, or holds another kind there, is unbindable.

An entry's locale is kept as its parsed `ParsedLocale.key`, so `en-US` and "en_US" are one locale. Peer
KF290 measured that identity on a rule's message and spec/01's no-model table on a hint list; the other
carriers are assumed to compare as they do, since one parser reads them all.

Lean's JSON objects keep their keys sorted, so an object-valued member yields its entries in key order
rather than as written; which of two entries for one locale wins is not stated for that shape. -/

namespace A12Kernel.Dm

open Lean

/-- A locale spelling keyed by its parsed form, or kept as written where the parser refuses it, for a
carrier whose refused spelling is unmeasured, such as a hint list's locale. A spelling outside the
represented profile stays an error. -/
def localeKey (spelling : String) : Except String String := do
  return match ← parseLocale? spelling with
    | some locale => locale.key
    | none => spelling

private def localizedTextEntry (entry : Json) : Except String (String × String) := do
  let .ok (.str locale) := entry.getObjVal? "locale"
    | throw s!"localized text {entry.compress} has no string locale"
  let .ok (.str text) := entry.getObjVal? "text"
    | throw s!"localized text {entry.compress} has no string text"
  let some parsed ← parseLocale? locale | throw s!"locale {locale} does not parse"
  pure (parsed.key, text)

/-- The entries of a localized-text member's value, as `(locale, text)` pairs, each locale its parsed
`ParsedLocale.key`. -/
def localizedTextValue (value : Json) : Except String (List (String × String)) :=
  match value with
  | .null => throw "a localized-text member is null"
  | .arr entries => entries.toList.mapM localizedTextEntry
  | .obj entries => entries.toList.mapM (localizedTextEntry ·.2)
  | _ => pure []

/-- The localized-text member `key` of `json`; an absent member, or a `json` that is no object, has no
entries. -/
def localizedTextMember (json : Json) (key : String) : Except String (List (String × String)) :=
  match json.getObjVal? key with
  | .error _ => pure []
  | .ok value => localizedTextValue value

private def bindMembers (json : Json) (keys : List String) : Except String Unit :=
  keys.forM fun key => discard <| localizedTextMember json key

private def member (json : Json) (key : String) : Json :=
  (json.getObjVal? key).toOption.getD .null

/-- Bind every localized-text member of an element and of the elements below it, whatever variant
filter it carries: the descriptions on every element, a field's label, helper text and requiredness
message, the message of the String or Enumeration body its type names and each Enumeration value's
label, a group's label, and a rule's message and each value of its variant messages. -/
private partial def bindElement (element : Json) : Except String Unit := do
  bindMembers element ["externalDescription", "internalDescription"]
  match (element.getObjValAs? String "type").toOption with
  | some "Field" =>
      let body := member element "Field"
      bindMembers body ["label", "helperText"]
      bindMembers (member body "requirednessConfig") ["errorMessage"]
      let fieldType := member body "fieldType"
      match (fieldType.getObjValAs? String "type").toOption with
      | some "StringType" => bindMembers (member fieldType "StringType") ["errorMessage"]
      | some "EnumerationType" =>
          let enumeration := member fieldType "EnumerationType"
          bindMembers enumeration ["errorMessage"]
          for value in (enumeration.getObjValAs? (Array Json) "values").toOption.getD #[] do
            bindMembers value ["label"]
      | _ => pure ()
  | some "Group" =>
      let body := member element "Group"
      bindMembers body ["label"]
      for child in (body.getObjValAs? (Array Json) "elements").toOption.getD #[] do bindElement child
  | some "Rule" =>
      let body := member element "Rule"
      bindMembers body ["errorMessage"]
      if let .obj variants := member body "variantErrorMessages" then
        for (_, value) in variants.toList do
          discard <| localizedTextValue value
  | _ => pure ()

/-- Bind every localized-text member of a model's `content` the Kernel's reader binds, failing on the
first that cannot bind: each element's under every root group, and each type definition's description. -/
def bindLocalizedTextMembers (content : Json) : Except String Unit := do
  for definition in (content.getObjValAs? (Array Json) "typeDefinitions").toOption.getD #[] do
    bindMembers definition ["internalDescription"]
  let roots := ((member content "modelRoot").getObjValAs? (Array Json) "rootGroups").toOption.getD #[]
  roots.forM bindElement

/-- The locales a model's header declares, in declaration order: each `locales` entry an object's string
`code` or a bare text, judged alike (header locale codes checkpoint,
`docs/sources/model-structure-and-declaration-probes.md#src-header-locale-codes`). A code the parser
refuses leaves the model unreadable; `declaredLocaleFailure?` judges what the build then refuses. A
`locales` member that is no list leaves no model, while an absent or `null` one declares nothing here
and costs the model its check (`bindModelFrame`, peer KF650). An entry that is neither a text nor an
object with a string `code` is outside the represented profile, since no row measures it. -/
def headerLocales (json : Json) : Except String (List ParsedLocale) := do
  let header := (json.getObjVal? "header").toOption.getD (Json.mkObj [])
  let entries := ((← frameList header "locales").getD #[]).toList
  let codes ← entries.mapM fun entry => match entry with
    | .str code => pure code
    | _ => match entry.getObjVal? "code" with
      | .ok (.str code) => pure code
      | _ => throw s!"header locale {entry.compress} carries no string code, outside the represented profile"
  codes.mapM fun code => do
    let some locale ← parseLocale? code | throw s!"header locale {code} does not parse"
    pure locale

/-- The header's declared locales as the Kernel builds them: unreadable as `headerLocales` states, and
failing the build as `declaredLocaleFailure?` states. -/
def builtHeaderLocales (json : Json) : Except String (List ParsedLocale) := do
  let locales ← headerLocales json
  match declaredLocaleFailure? locales with
  | some (.languageEmpty key) => throw s!"header locale {key} has no language"
  | some (.repeated key) => throw s!"header locale {key} is declared twice"
  | none => pure locales

end A12Kernel.Dm
