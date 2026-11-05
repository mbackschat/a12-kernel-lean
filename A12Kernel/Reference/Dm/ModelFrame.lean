import Lean.Data.Json
import A12Kernel.Elaboration.ModelConsistency
import A12Kernel.Reference.Dm.LocaleSpelling

/-! # How the Kernel binds a DM-JSON model's frame

The Kernel reads a model's frame, the `header` and `content` objects and the members under them, into
Java objects before any check, member by member (peer KF650, a12-dmkits `413880f4b`, Kernel gate, kernel
30.8.1, 2026-10-29; the [model frame members](../../../docs/sources/model-structure-and-declaration-probes.md#src-model-frame-members)
checkpoint). A member it cannot bind leaves no model, a read failure here:

* A text member binds any scalar, a number or boolean as its text, and its absence; an object or an
  array leaves no model, as `null` does where the Kernel marks the member non-null.
* A list member binds an array and its absence; any other kind leaves no model, as `null` does where
  the member is non-null.
* An object member binds an object, and its absence where the member is optional.

Three shapes cost only the entry's consistency check: no `modelInfo`, a `null` supported character, and
a condition language naming a parsed locale other than the two supported, measured for the codes
`supportedConditionLanguages` lists. The model builds and its check fails without a class, so they are a
`FrameCheckFailure`, never a read failure.

Kernel 31.1.1 reads a header whose `id`, `modelVersion` or `locales` is absent or `null` into a model it then
cannot build, on the dmtool and the probe route alike (derived-row capture of 2026-11-04, `header-slots.json`;
peer KF654, a12-dmkits `1124b523f`, `ModelHeaderSlotLawsTest` and `WorkspaceBlankTextDiffTest`). Each leaves no
model here as a read failure, as every member KF654 lists does in these readers, so they do not separate a model
the Kernel cannot read from one it reads and cannot build (SG9). Kernel 30.8.1 admitted the `id` absent or `null`
and built the other shapes to fail their check.

An integer number binds as its value's decimal text, measured for `5`; a token with a fraction or an
exponent is outside the represented profile, since the Kernel keeps the token as written and Lean's
parser does not. -/

namespace A12Kernel.Dm

open Lean A12Kernel

/-- The frame members the readers consume, each already bound. -/
structure ModelFrame where
  header : Json
  content : Json
  /-- The model info, empty when absent. -/
  info : Json
  /-- The model configuration, empty when absent. -/
  config : Json
  /-- The declared locale entries; an absent or `null` member leaves no model. -/
  locales : Array Json
  /-- The header's `modelReferences` entries, empty when absent or `null`: a model naming one is expanded
  before its check (peer Letter E §4, source-read). -/
  modelReferences : Array Json
  typeDefinitions : Array Json
  rootGroups : Array Json
  /-- The supported-character entries, a `null` entry as `none`. -/
  supportedCharacters : List (Option String)
  timeZone : Option String
  /-- The supported condition language's locale key, "en_US" or "de_DE"; `none` when the model declares
  none or an unsupported one, which `checkFailure?` then names. -/
  conditionLanguage : Option String
  checkFailure? : Option FrameCheckFailure

/-- Fuel for a walk over the content's nesting, which never exceeds the characters of the text holding it. -/
def ModelFrame.nestingFuel (frame : ModelFrame) : Nat :=
  frame.content.compress.length + 1

/-- A scalar as the text the Kernel binds it to; `none` for `null` and for a container. -/
def scalarText? : Json → Except String (Option String)
  | .str text => pure (some text)
  | .bool value => pure (some (toString value))
  | .num number =>
      if number.exponent == 0 then pure (some (toString number.mantissa))
      else throw s!"model member {number} is a non-integer number, outside the represented profile"
  | _ => pure none

/-- A text member: `none` when absent, or `null` on a nullable member. -/
def frameText (parent : Json) (key : String) (nonNull : Bool := false) : Except String (Option String) :=
  match parent.getObjVal? key with
  | .error _ => pure none
  | .ok .null => if nonNull then throw s!"model member {key} is null" else pure none
  | .ok value => do
      let some text ← scalarText? value | throw s!"model member {key} is no text"
      pure (some text)

/-- A member the Kernel never defaults: its absence leaves no model. -/
def requireMember (parent : Json) (key : String) : Except String Unit :=
  match parent.getObjVal? key with
  | .error _ => throw s!"model member {key} is absent"
  | .ok _ => pure ()

/-- A list member: `none` when absent, or `null` on a nullable member. -/
def frameList (parent : Json) (key : String) (nonNull : Bool := false) : Except String (Option (Array Json)) :=
  match parent.getObjVal? key with
  | .error _ => pure none
  | .ok .null => if nonNull then throw s!"model member {key} is null" else pure none
  | .ok (.arr entries) => pure (some entries)
  | .ok _ => throw s!"model member {key} is no list"

/-- An object member: `none` when absent; `null` and every other kind leave no model. -/
def frameObject (parent : Json) (key : String) : Except String (Option Json) :=
  match parent.getObjVal? key with
  | .error _ => pure none
  | .ok value@(.obj _) => pure (some value)
  | .ok _ => throw s!"model member {key} is no object"

/-- The condition language, as a text or an object whose `code` binds as a text member does: `null`,
another scalar, an array, and an object whose `code` is absent, `null` or a container leave no model.
The code is read as a locale, so one the locale parser refuses leaves no model too, while a parsed locale
is the language its key names, "de-DE" selecting German as "de_DE" does (peer letter of 2026-10-30a). -/
private def conditionLanguageLocale (config : Json) : Except String (Option ParsedLocale) :=
  match config.getObjVal? "conditionLanguage" with
  | .error _ => pure none
  | .ok (.str code) => parsed code
  | .ok language@(.obj _) => do
      let some code ← frameText language "code" (nonNull := true) | throw "condition language has no code"
      parsed code
  | .ok _ => throw "condition language is neither a text nor an object"
where
  parsed (code : String) : Except String (Option ParsedLocale) := do
    let some locale ← parseLocale? code | throw s!"condition language {code} does not parse as a locale"
    pure (some locale)

/-- The two locales whose condition languages the Kernel supports. A model declaring another parsed
locale is read and expanded, and its check then fails without a class, measured for "zz", the empty
code, "de", "en", "fr_FR" and "de_DE_x" (peer letter of 2026-10-30a; the
[model frame members](../../../docs/sources/model-structure-and-declaration-probes.md#src-model-frame-members)
checkpoint for "zz" and the empty code). -/
private def supportedConditionLanguages : List String := ["en_US", "de_DE"]

/-- Bind a model's frame, failing on the first member the Kernel cannot bind. -/
def bindModelFrame (json : Json) : Except String ModelFrame := do
  let some header ← frameObject json "header" | throw "model has no header"
  let some content ← frameObject json "content" | throw "model has no content"
  for key in ["modelType", "description"] do discard <| frameText header key
  discard <| frameText header "id" (nonNull := true)
  for key in ["id", "modelVersion", "locales"] do requireMember header key
  discard <| frameText header "modelVersion" (nonNull := true)
  let locales ← frameList header "locales" (nonNull := true)
  for key in ["labels", "annotations"] do discard <| frameList header key
  let modelReferences := (← frameList header "modelReferences").getD #[]
  let info? ← frameObject content "modelInfo"
  let info := info?.getD (Json.mkObj [])
  discard <| frameText info "name" (nonNull := true)
  for key in ["variant", "branch", "revision", "comment", "joinedModelsInfo"] do discard <| frameText info key
  let config := (← frameObject content "modelConfig").getD (Json.mkObj [])
  discard <| frameText config "decimalSeparator" (nonNull := true)
  let timeZone ← frameText config "timeZone" (nonNull := true)
  let language ← conditionLanguageLocale config
  let conditionLanguage := language.bind fun locale =>
    if supportedConditionLanguages.contains locale.key then some locale.key else none
  let supportedCharacters ← ((← frameList config "supportedCharacters" (nonNull := true)).getD #[]).toList.mapM
    fun entry => match entry with
      | .null => pure none
      | _ => do
          let some text ← scalarText? entry | throw "supported character entry is no text"
          pure (some text)
  let typeDefinitions := (← frameList content "typeDefinitions" (nonNull := true)).getD #[]
  let rootGroups ← match ← frameObject content "modelRoot" with
    | none => pure #[]
    | some root => do pure ((← frameList root "rootGroups" (nonNull := true)).getD #[])
  let failure :=
    if info?.isNone then some .modelInfoMissing
    else if supportedCharacters.contains none then some .supportedCharacterNull
    else if language.isSome && conditionLanguage.isNone then some .conditionLanguageUnsupported
    else none
  pure {
    header := header, content := content, info := info, config := config, locales := locales.getD #[]
    modelReferences
    typeDefinitions := typeDefinitions, rootGroups := rootGroups, supportedCharacters := supportedCharacters
    timeZone := timeZone, conditionLanguage := conditionLanguage, checkFailure? := failure }

end A12Kernel.Dm
