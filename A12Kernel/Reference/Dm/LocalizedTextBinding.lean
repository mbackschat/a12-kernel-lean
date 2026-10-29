import Lean.Data.Json

/-! # How the Kernel's DM-JSON reader binds a localized-text member

A label, helper text, description or message is a localized-text member: entries of a `locale` and a
`text`. The Kernel binds every such member before any variant filter, so a member it cannot bind leaves
no model, a read failure here and never a Kernel class (peer KF646, measured 2026-10-29 on twelve
carriers, `docs/sources/inbound-handbacks.md#src-inbound-2026-10-29`):

* The member's own value is iterated as a JSON node: a list yields its elements, an object its values,
  and any other scalar nothing, so `"x"`, `5` and `[]` bind with no text. `null` is unbindable.
* Each entry must carry a string `locale` that parses as a locale and a string `text`; an entry that is
  not an object, or lacks either key, or holds another kind there, is unbindable.

Lean's JSON objects keep their keys sorted, so an object-valued member yields its entries in key order
rather than as written; which of two entries for one locale wins is not stated for that shape. -/

namespace A12Kernel.Dm

open Lean

/-- Whether the Kernel's locale parser, `LocaleUtils.toLocale` of commons-lang3 3.20.0 as the measured
runtime ships it, takes `spelling`. The accepted shape is a lowercase two- or three-letter language,
optionally followed by an uppercase two-letter country or a three-digit area, and a nonempty variant
after a second separator; `_` and `-` both separate, `_` when present. A spelling may instead start with
its separator and an uppercase country, then optionally the same separator and a nonempty variant
(`_US`, `-US-x`), and the empty spelling is the root locale. In a two-segment spelling a three-digit area
is taken after any first segment, so "XX_123" parses while "XX_123_x" does not.

The rows are peer KF290's Kernel spellings and the jar's own verdicts, measured 2026-10-29
(`docs/sources/model-structure-and-declaration-probes.md#src-locale-spelling-grammar`). Two
cases depend on tables this account does not carry and are refused as outside the represented profile:
a bare two-letter uppercase spelling, which parses exactly when the JDK lists it as an ISO country
(`US` parses and `EN` does not), and a non-ASCII character, whose case and digit classes are Unicode's. -/
def localeSpellingParses (spelling : String) : Except String Bool := do
  let chars := spelling.toList
  if chars.any (·.val ≥ 128) then
    throw s!"locale {spelling} carries a non-ASCII character, outside the represented profile"
  let language (part : List Char) := (part.length == 2 || part.length == 3) && part.all Char.isLower
  let country (part : List Char) := part.length == 2 && part.all Char.isUpper
  let area (part : List Char) := part.length == 3 && part.all Char.isDigit
  match chars with
  | [] => return true
  | separator :: rest =>
      if chars.contains '#' || chars.length < 2 then return false
      if country chars then
        throw s!"locale {spelling} parses only if the JDK lists it as a country, outside the represented profile"
      if separator == '_' || separator == '-' then
        return match rest with
          | first :: second :: tail =>
              first.isUpper && second.isUpper && match tail with
                | [] => true
                | next :: variant => next == separator && !variant.isEmpty
          | _ => false
      if language chars then return true
      let separator := if chars.contains '_' then '_' else '-'
      let (head, afterHead) := chars.span (· != separator)
      return match afterHead with
        | [] => false
        | _ :: tail =>
            let (middle, afterMiddle) := tail.span (· != separator)
            match afterMiddle with
            | [] => (language head && country middle) || area middle
            | _ :: variant =>
                language head && (middle.isEmpty || country middle || area middle) && !variant.isEmpty

private def localizedTextEntry (entry : Json) : Except String (String × String) := do
  let .ok (.str locale) := entry.getObjVal? "locale"
    | throw s!"localized text {entry.compress} has no string locale"
  let .ok (.str text) := entry.getObjVal? "text"
    | throw s!"localized text {entry.compress} has no string text"
  unless ← localeSpellingParses locale do throw s!"locale {locale} does not parse"
  pure (locale, text)

/-- The entries of a localized-text member's value, as `(locale, text)` pairs. -/
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

end A12Kernel.Dm
