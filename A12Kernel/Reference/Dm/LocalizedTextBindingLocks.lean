import A12Kernel.Reference.Dm.Model
import A12Kernel.Reference.Dm.LoneSurrogate
import A12Kernel.Reference.Dm.ModelConsistencyRead
import A12Kernel.Reference.Dm.FieldTypeDeclarationRead
import A12Kernel.Reference.Dm.EntryFrameFixture

/-! # How the DM-JSON readers bind a localized-text member

Each expectation is a Kernel row of peer KF646 (a12-dmkits `ceabf655`,
`CheckerLocalizedTextShapeAgreementTest`, BoundModel, kernel 30.8.1, 2026-10-29) or of the locale
spellings of peer KF290, read in the
[October 29 handback](../../../docs/sources/inbound-handbacks.md#src-inbound-2026-10-29). A model the
Kernel does not build is a read failure here, never a Kernel class; a built model may still draw a class
of its own, as two values labelled alike do. -/

namespace A12Kernel.Dm.LocalizedTextBindingLocks

open Lean A12Kernel

/-- The twelve carriers the letter measures, each placing one member value. -/
private inductive Carrier where
  | fieldLabel | helperText | groupLabel | externalDescription | internalDescription | valueLabel
  | enumerationMessage | definitionDescription | ruleMessage | variantMessage | stringMessage
  | requirednessMessage
  deriving DecidableEq

private def Carrier.all : List Carrier :=
  [.fieldLabel, .helperText, .groupLabel, .externalDescription, .internalDescription, .valueLabel,
    .enumerationMessage, .definitionDescription, .ruleMessage, .variantMessage, .stringMessage,
    .requirednessMessage]

private def only : Json := Json.mkObj [("filterType", "ONLY"), ("variants", Json.arr #["premium"])]

private def message : Json := Json.arr #[Json.mkObj [("locale", "en_US"), ("text", "m")]]

/-- The letter's model, a policy with a reference, a status, a group of items and a rule declaring
"en_US", with `value` on `carrier` and, when `filtered`, every element deleted by an `ONLY` filter. -/
private def model (carrier : Carrier) (value : Json) (filtered : Bool) : Json :=
  let on (target : Carrier) (key : String) : List (String × Json) := if carrier == target then [(key, value)] else []
  let filter : List (String × Json) := if filtered then [("variantFilter", only)] else []
  let stringBody := if carrier == .stringMessage then [("pattern", Json.str "[A-Z]+"), ("errorMessage", value)] else []
  let requiredness := if carrier == .requirednessMessage then
      [("requirednessConfig", Json.mkObj [("mode", "absoluteOrRelativeToNextRepAncestor"), ("errorMessage", value)])]
    else []
  let reference := Json.mkObj (([("type", "Field"), ("id", "/Policy/Ref"), ("name", "Ref")] : List (String × Json)) ++
    on .externalDescription "externalDescription" ++ on .internalDescription "internalDescription" ++
    [("Field", Json.mkObj (filter ++ on .fieldLabel "label" ++ on .helperText "helperText" ++ requiredness ++
      [("fieldType", Json.mkObj [("type", "StringType"), ("StringType", Json.mkObj stringBody)])]))])
  let enumValue (stored : String) := Json.mkObj ([("value", Json.str stored)] ++ on .valueLabel "label")
  let status := Json.mkObj [("type", "Field"), ("id", "/Policy/Status"), ("name", "Status"),
    ("Field", Json.mkObj (filter ++ [("fieldType", Json.mkObj [("type", "EnumerationType"),
      ("EnumerationType", Json.mkObj (on .enumerationMessage "errorMessage" ++
        [("values", Json.arr #[enumValue "OPEN", enumValue "CLOSED"])]))])]))]
  let items := Json.mkObj [("type", "Group"), ("id", "/Policy/Items"), ("name", "Items"),
    ("Group", Json.mkObj (filter ++ on .groupLabel "label" ++ [("repeatability", toJson (3 : Nat)),
      ("elements", Json.arr #[Json.mkObj [("type", "Field"), ("id", "/Policy/Items/Label"), ("name", "Label"),
        ("Field", Json.mkObj [("fieldType", Json.mkObj [("type", "StringType")])])]])]))]
  let rule := Json.mkObj [("type", "Rule"), ("id", "/Policy/RefCheck"), ("name", "RefCheck"),
    ("Rule", Json.mkObj (filter ++ ([("errorEntityRelPath", "../Ref"), ("errorCode", "REF"),
      ("errorCondition", "FieldFilled(Ref)"), ("severity", "ERROR"),
      ("errorMessage", if carrier == .ruleMessage then value else message)] : List (String × Json)) ++
      if carrier == .variantMessage then [("variantErrorMessages", Json.mkObj [("premium", value)])] else []))]
  let definitions := if carrier == .definitionDescription then
      #[Json.mkObj [("id", "RefType"), ("name", "RefType"), ("revision", "1"), ("internalDescription", value),
        ("fieldType", Json.mkObj [("type", "StringType"), ("StringType", Json.mkObj [])])]]
    else #[]
  checkedEntryFrame <| Json.mkObj [("header", Json.mkObj [("locales", Json.arr #[Json.mkObj [("code", "en_US")]])]),
    ("content", Json.mkObj [("modelInfo", Json.mkObj []), ("modelConfig", Json.mkObj []),
    ("typeDefinitions", Json.arr definitions),
    ("modelRoot", Json.mkObj [("rootGroups", Json.arr #[Json.mkObj [("type", "Group"), ("id", "/Policy"),
      ("name", "Policy"), ("Group", Json.mkObj [("elements", Json.arr #[reference, status, items, rule])])]])])])]

/-- Whether the reader builds the model; a refused declaration still counts as built. -/
private def builds (json : Json) : Bool :=
  match readModel json with
  | .ok _ => true
  | .error _ => false

private def entry (locale text : Option Json) : Json :=
  Json.mkObj (locale.toList.map ("locale", ·) ++ text.toList.map ("text", ·))

private def written (value : String) : Option Json := some (Json.str value)

/-- Whether model text parses and builds; `none` when the text itself is no JSON, so a malformed fixture
cannot pass as a model that does not build. -/
private def parsedBuilds (written : String) : Option Bool :=
  (parseModelJson written).toOption.map (builds ∘ checkedEntryFrame)

/-- Whether the consistency reader and the declaration reader read the model. Both fail on a member
that does not bind, as `readModel` does. -/
private def otherReadersRead (json : Json) : Bool × Bool :=
  ((readConsistencyModel json).isOk, (fieldTypeDeclarationNotifications json fun _ => .compiled fun _ => true).isOk)

/-- The declaration labels a model reports, empty when it does not read. -/
private def declarationLabels (json : Json) : List String :=
  ((fieldTypeDeclarationNotifications json fun _ => .compiled fun _ => true).toOption.getD []).map (·.1)

/-- The member values the letter writes, each with whether the Kernel builds the model. -/
private def shapes : List (Json × Bool) := [
  (Json.arr #[entry (written "en_US") (written "x")], true),
  (Json.arr #[entry (written "en_US") (written "")], true),
  (Json.arr #[entry (written "en_US") (some Json.null)], false),
  (Json.arr #[entry (written "en_US") (some (toJson (5 : Nat)))], false),
  (Json.arr #[entry (written "en_US") (some (Json.bool true))], false),
  (Json.arr #[entry (written "en_US") (some (Json.arr #[]))], false),
  (Json.arr #[entry (written "en_US") none], false),
  (Json.arr #[entry (some Json.null) (written "x")], false),
  (Json.arr #[entry (some (toJson (5 : Nat))) (written "x")], false),
  (Json.arr #[entry none (written "x")], false),
  (Json.arr #[entry (written "klingon") (written "x")], false),
  (Json.arr #[Json.str "x"], false),
  (Json.arr #[Json.null], false),
  (Json.arr #[], true),
  (Json.mkObj [("a", entry (written "en_US") (written "x"))], true),
  (Json.mkObj [("a", entry (written "en_US") (some Json.null))], false),
  (Json.str "x", true),
  (toJson (5 : Nat), true),
  (Json.null, false)]

/-- Every shape on every carrier, kept and with every element deleted by the filter: the reader builds
the model exactly where the Kernel does, since binding precedes the filter. -/
example :
    Carrier.all.all fun carrier => shapes.all fun (value, built) =>
      builds (model carrier value false) == built && builds (model carrier value true) == built := by
  native_decide

/-- The consistency and declaration readers bind every carrier before the filter too. -/
example :
    Carrier.all.all fun carrier => shapes.all fun (value, built) =>
      otherReadersRead (model carrier value false) == (built, built) &&
        otherReadersRead (model carrier value true) == (built, built) := by
  native_decide

/-- An object-valued member yields its values as entries: two Enumeration values labelled alike in that
form repeat a display value as the list form does, while values without labels do not (KF646). Under
`variantErrorMessages` a single entry written as an object, whose values are strings, leaves no model,
while an object of entries is read (KF646). -/
example :
    let alike := fun (label : Json) => declarationLabels (model .valueLabel label false)
    (alike (Json.mkObj [("a", entry (written "en_US") (written "same"))])).contains "MVK_DISPLAY_VALUES_DUPLICATE" ∧
    (alike (Json.arr #[entry (written "en_US") (written "same")])).contains "MVK_DISPLAY_VALUES_DUPLICATE" ∧
    !(alike (Json.arr #[])).contains "MVK_DISPLAY_VALUES_DUPLICATE" ∧
    builds (model .variantMessage (entry (written "en_US") (written "x")) false) = false ∧
    builds (model .variantMessage (Json.mkObj [("a", entry (written "en_US") (written "x"))]) false) = true := by
  native_decide

/-- The member parses from model text as it does from a constructed value: `null` is no model, `[]` and a
scalar are a model without text. -/
example :
    parsedBuilds "{\"content\":{\"modelRoot\":{\"rootGroups\":[{\"type\":\"Group\",\"name\":\"P\",\"Group\":{\"label\":null,\"elements\":[]}}]}}}" = some false ∧
    parsedBuilds "{\"content\":{\"modelRoot\":{\"rootGroups\":[{\"type\":\"Group\",\"name\":\"P\",\"Group\":{\"label\":[],\"elements\":[]}}]}}}" = some true := by
  native_decide

/-- The locale spellings peer KF290 measured on the Kernel, the entry rows of peer KF649's lock, which
the Kernel reads on all 2,410 retained spellings exactly where the jar parses, then the parser's quirks
the retained jar verdicts show: a three-digit area after any first segment of a two-segment spelling only, a variant
keeping its separators, and an opening separator before a country. A bare uppercase pair and a non-ASCII
character are outside the represented profile. -/
example :
    ["en_US", "en-US", "en", "eng", "fr_CA", "en_US_POSIX", "en_123", "", "XX_123", "1_123", "en_US_POSIX_x",
      "en__POSIX", "_US", "-US-x", "de", "deu", "de_CH", "de-CH", "es_419", "de_CH_1996", "de_CH_1996_x",
      "de_CH_POSIX-x", "de-CH-1996", "de__1996", "_CH", "-CH", "_CH_x", "DE_419", "1_419"].all (fun spelling => ((Dm.parseLocale? spelling).toOption.map Option.isSome) == some true) ∧
    ["en_us", "EN_US", "e", "en_U", "en_USA", "klingon", " ", "en_", "en_US_", "en_US-x", "_US-x", "en#US",
      "zh_Hans_CN", "XX_123_x", "1_123_x", "e_123_x", "-US-", "de_ch", "DE_CH", "d", "de_C", "de_CHE", "de_CH_",
      "de_CH-x", "de-CH_x", "de-CH-x_y", "_CH_", "DE_419_x", " de", "de "].all (fun spelling => ((Dm.parseLocale? spelling).toOption.map Option.isSome) == some false) ∧
    ["US", "EN", "CH", "QQ", "ée", "de_ÄÖ", "de_٣٣٣"].all (fun spelling => (Dm.parseLocale? spelling).toOption.isNone) := by
  native_decide

end A12Kernel.Dm.LocalizedTextBindingLocks
