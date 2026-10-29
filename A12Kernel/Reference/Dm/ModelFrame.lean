import Lean.Data.Json
import A12Kernel.Elaboration.ModelConsistency

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

Four shapes cost only the entry's consistency check: no `modelVersion`, no `modelInfo`, `locales`
absent or `null`, and a `null` supported character. The model builds and its check fails without a
class, so they are a `FrameCheckFailure`, never a read failure.

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
  /-- The declared locale entries, empty when absent or `null`. -/
  locales : Array Json
  typeDefinitions : Array Json
  rootGroups : Array Json
  /-- The supported-character entries, a `null` entry as `none`. -/
  supportedCharacters : List (Option String)
  timeZone : Option String
  /-- The condition language's code, as a bare text or an object's `code`. -/
  conditionLanguage : Option String
  checkFailure? : Option FrameCheckFailure

private def scalarText? : Json → Except String (Option String)
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

/-- A condition language is a text, or an object whose `code` binds as a text member does; `null`, another
scalar, an array, and an object whose `code` is absent, `null` or a container leave no model. A `code`
written as a number binds as its text here, which no row measures. A bound code other than "en_US" and
"de_DE" leaves no model too, measured for "zz" and the empty code (model frame members checkpoint). -/
private def conditionLanguageCode (config : Json) : Except String (Option String) :=
  match config.getObjVal? "conditionLanguage" with
  | .error _ => pure none
  | .ok (.str code) => supported code
  | .ok language@(.obj _) => do
      let some code ← frameText language "code" (nonNull := true) | throw "condition language has no code"
      supported code
  | .ok _ => throw "condition language is neither a text nor an object"
where
  supported (code : String) : Except String (Option String) :=
    if code == "en_US" || code == "de_DE" then pure (some code)
    else throw s!"condition language {code} is not supported"

/-- Bind a model's frame, failing on the first member the Kernel cannot bind. -/
def bindModelFrame (json : Json) : Except String ModelFrame := do
  let some header ← frameObject json "header" | throw "model has no header"
  let some content ← frameObject json "content" | throw "model has no content"
  for key in ["id", "modelType", "description"] do discard <| frameText header key
  let version ← frameText header "modelVersion"
  let locales ← frameList header "locales"
  for key in ["labels", "annotations", "modelReferences"] do discard <| frameList header key
  let info? ← frameObject content "modelInfo"
  let info := info?.getD (Json.mkObj [])
  discard <| frameText info "name" (nonNull := true)
  for key in ["variant", "branch", "revision", "comment", "joinedModelsInfo"] do discard <| frameText info key
  let config := (← frameObject content "modelConfig").getD (Json.mkObj [])
  discard <| frameText config "decimalSeparator" (nonNull := true)
  let timeZone ← frameText config "timeZone" (nonNull := true)
  let conditionLanguage ← conditionLanguageCode config
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
    if version.isNone then some .versionMissing
    else if info?.isNone then some .modelInfoMissing
    else if locales.isNone then some .localesMissing
    else if supportedCharacters.contains none then some .supportedCharacterNull
    else none
  pure {
    header := header, content := content, info := info, config := config, locales := locales.getD #[]
    typeDefinitions := typeDefinitions, rootGroups := rootGroups, supportedCharacters := supportedCharacters
    timeZone := timeZone, conditionLanguage := conditionLanguage, checkFailure? := failure }

end A12Kernel.Dm
