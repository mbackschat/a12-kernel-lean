import Lean.Data.Json
import A12Kernel.Elaboration.FieldTypeDeclarationNotification
import A12Kernel.Elaboration.StringContext
import A12Kernel.Reference.Dm.Model

/-! # Reading a DM-JSON model for the field-type declaration notifications

The Kernel's consistency check judges every field the variant filter keeps, so this reader walks every
root group and nested group in document order and judges each such field's body after its type
definition is resolved per referencing field: a definition no field references draws nothing, and a
definition that two fields reference draws its notifications at both. It reads only the members the
field-type laws consume, keeps integer members raw so a refused one stays visible, and reads the two
String flags with the Kernel's coercion (`flagMember?`).

The result is a list of `(label, element path)` pairs. A model the Kernel cannot build yields the one
unbuilt-model label and no path. The report is a multiset, so the walk order is not an observation.

It is an input adapter, differentially tested by the field-declaration capture rather than proved. A
condition language other than the two whose message tokens are measured, a member of the wrong shape
and an unresolvable type definition are read errors, never an empty report.
-/

namespace A12Kernel.Dm

open Lean A12Kernel

private def optionalInt (json : Json) (key : String) : Except String (Option Int) :=
  match json.getObjVal? key with
  | .error _ | .ok .null => pure none
  | .ok value => some <$> fromJson? value

private def optionalString (json : Json) (key : String) : Except String (Option String) :=
  match json.getObjVal? key with
  | .error _ | .ok .null => pure none
  | .ok (.str value) => pure (some value)
  | .ok other => throw s!"{key} {other.compress}"

/-- The members of an array-valued key; an absent or `null` key is empty. -/
private def arrayMembers (json : Json) (key : String) : Except String (List Json) :=
  match json.getObjVal? key with
  | .error _ | .ok .null => pure []
  | .ok value => (value.getArr?).map Array.toList

/-- A flag read as a JSON boolean only, the reading every flag but the two coerced String ones keeps. -/
private def strictFlag (json : Json) (key : String) : Bool :=
  (json.getObjValAs? Bool key).toOption.getD false

/-- Locale-keyed entries, `[{locale, text}]`, as a field's messages and an Enumeration value's labels
write them. -/
private def localizedTexts (json : Json) (key : String) : Except String (List (String × String)) := do
  (← arrayMembers json key).mapM fun entry => do
    pure (← entry.getObjValAs? String "locale", ← entry.getObjValAs? String "text")

private def readMessages (json : Json) : Except String (List FieldMessageEntry) := do
  pure ((← localizedTexts json "errorMessage").map fun (locale, text) => { locale, text })

private def readString (body : Json) : Except String StringTypeDeclaration := do
  pure {
    minLength := ← optionalInt body "minLength"
    maxLength := ← optionalInt body "maxLength"
    noValueValidation := ← flagMember? body "noValueValidation"
    lineBreaksPermitted := ← flagMember? body "lineBreaksPermitted"
    pattern := ← optionalString body "pattern"
    hintList := ← (← arrayMembers body "hintList").mapM fun entry => do
      pure { locale := ← entry.getObjValAs? String "locale"
             values := ← (← arrayMembers entry "values").mapM Json.getStr? }
    messages := ← readMessages body }

private def readNumber (body : Json) : Except String NumberTypeDeclaration := do
  let amount ← match ← optionalString body "trait" with
    | none => pure false
    | some "amount" => pure true
    | some other => throw s!"NumberType trait {other}"
  pure {
    minLength := ← optionalInt body "minLength"
    maxLength := ← optionalInt body "maxLength"
    maxIntegerDigits := ← optionalInt body "maxIntegerDigits"
    minFractionalDigits := ← optionalInt body "minFractionalDigits"
    maxFractionalDigits := ← optionalInt body "maxFractionalDigits"
    positivesOnly := strictFlag body "positivesOnly"
    amount
    minValue := ← decimalMember? body "minValue"
    maxValue := ← decimalMember? body "maxValue" }

private def readEnumeration (body : Json) : Except String EnumerationTypeDeclaration := do
  let sValue ← match body.getObjVal? "sValue" with
    | .error _ | .ok .null => pure none
    | .ok (.str value) => pure (some value)
    | .ok _ => throw "EnumerationType sValue must be a string"
  pure {
    values := ← (← arrayMembers body "values").mapM fun entry => do
      pure { token := ← entry.getObjValAs? String "value"
             labels := (← localizedTexts entry "label").map fun (locale, text) => { locale, text } }
    categories := ← (← arrayMembers body "categories").mapM fun category => do
      pure { name := ← category.getObjValAs? String "name"
             tokens := ((category.getObjValAs? (Array String) "values").toOption.getD #[]).toList }
    sValue
    messages := ← readMessages body }

/-- The declaration of a field whose type definition is already resolved. A type none of the laws
concerns, or no type at all, is `other`: its refusal belongs to another reader. -/
private def readDeclaration (fieldJson : Json) : Except String FieldTypeDeclaration := do
  let some fieldType := (fieldJson.getObjVal? "fieldType").toOption | pure .other
  let some typeName := (fieldType.getObjValAs? String "type").toOption | pure .other
  let body := (fieldType.getObjVal? typeName).toOption.getD (Json.mkObj [])
  match typeName with
  | "StringType" => .string <$> readString body
  | "NumberType" => .number <$> readNumber body
  | "CustomFieldType" =>
      pure (.custom { name := ← optionalString body "name"
                      minLength := ← optionalInt body "minLength"
                      maxLength := ← optionalInt body "maxLength" })
  | "DateType" =>
      pure (.date { format := ← optionalString body "format"
                    partialMode := ← partialMode? (← optionalString body "datePrecision")
                    youngerThan1900Check := strictFlag body "youngerThan1900Check" })
  | "EnumerationType" => .enumeration <$> readEnumeration body
  | "UnspecifiedType" => pure .unspecified
  | _ => pure .other

/-- The field message tokens in the model's condition language. Only the two measured languages have
them. -/
private def messageTokens : String → Except String StringPatternMessageTokens
  | "en_US" => pure { field := "field", fieldValue := "field.value" }
  | "de_DE" => pure { field := "Feld", fieldValue := "Feld.Wert" }
  | other => throw s!"field message tokens of condition language {other} are not measured"

private structure WalkEnvironment where
  variant : Option String
  definitions : List (String × Json)
  compilePattern : StringPatternCompiler
  context : FieldTypeContext

/-- Judge each field in document order, a group's fields after its own position. -/
private partial def judgeElement (environment : WalkEnvironment) (parent : List String)
    (element : Json) : Except String (List (List String × FieldTypeJudgement)) := do
  let kind ← element.getObjValAs? String "type"
  let name := (element.getObjValAs? String "name").toOption.getD ""
  let body := (element.getObjVal? kind).toOption.getD (Json.mkObj [])
  match kind with
  | "Group" =>
      let children ← arrayMembers body "elements"
      pure (← children.mapM (judgeElement environment (parent ++ [name]))).flatten
  | "Field" =>
      if !(← acceptedByVariant environment.variant body) then pure []
      else
        let declaration ← readDeclaration (← resolveTypeDefinition environment.definitions body)
        pure [(parent ++ [name],
          declaration.judge environment.compilePattern environment.context)]
  | _ => pure []

/-- The notifications every kept field's type declaration raises, each as its capture label and the
element path, or the one unbuilt-model label with an empty path. The Java pattern compilation is the
host's and has no default: the closed ASCII profiles of `builtinStringPatternCompiler` refuse
Java-valid sources they cannot execute, which this check would report as invalid patterns. -/
def fieldTypeDeclarationNotifications (json : Json) (compilePattern : StringPatternCompiler)
    (variant : Option String := none)
    (charset : LegalCharset := .defaultBmp) : Except String (List (String × String)) := do
  let header := (json.getObjVal? "header").toOption.getD (Json.mkObj [])
  let content ← json.getObjVal? "content"
  let language := ((content.getObjVal? "modelConfig").toOption.bind fun config =>
    (config.getObjVal? "conditionLanguage").toOption.bind fun language =>
      (language.getObjValAs? String "code").toOption).getD "en_US"
  let environment : WalkEnvironment := {
    variant
    definitions := (← arrayMembers content "typeDefinitions").map fun definition =>
      ((definition.getObjValAs? String "id").toOption.getD "", definition)
    compilePattern
    context := {
      declaredLocales := (← arrayMembers header "locales").filterMap fun locale =>
        (locale.getObjValAs? String "code").toOption
      messageTokens := ← messageTokens language
      charset } }
  let roots ← match content.getObjVal? "modelRoot" with
    | .error _ | .ok .null => pure []
    | .ok root => arrayMembers root "rootGroups"
  let judgements := (← roots.mapM (judgeElement environment [])).flatten
  if judgements.any (·.2 == .modelNotBuilt) then
    pure [(modelNotBuiltLabel, "")]
  else
    pure (judgements.flatMap fun (path, judgement) =>
      match judgement with
      | .modelNotBuilt => []
      | .notifications raised => raised.map fun notification =>
          (notification.label, "/" ++ "/".intercalate path))

/-! ## Locks on the member coercions this reader depends on -/

private def member (value : Json) : Json := Json.mkObj [("k", value)]

/- A bound written as a plain decimal string reads as the number, and anything that is no plain decimal
   stays refused: an exponent, a plus sign, a digit separator and a bare or trailing point. -/
example :
    (decimalMember? (member (.str "1.5")) "k").toOption = some (some (3 / 2)) ∧
    (decimalMember? (member (.str "-2")) "k").toOption = some (some (-2)) ∧
    (decimalMember? (member (.str "007.50")) "k").toOption = some (some (15 / 2)) ∧
    ["", "-", "+1", "1e3", "1_0", ".5", "5.", "1.2.3", " 1"].all
      (fun text => (decimalMember? (member (.str text)) "k").toOption.isNone) = true := by
  native_decide

/- The two String flags coerce: a JSON number is true unless zero, the two strings read as their
   Boolean, `null` and absence are false, and any other shape is unreadable. -/
example :
    (flagMember? (member (.bool true)) "k").toOption = some true ∧
    (flagMember? (member (.num 1)) "k").toOption = some true ∧
    (flagMember? (member (.num 0)) "k").toOption = some false ∧
    (flagMember? (member (.str "true")) "k").toOption = some true ∧
    (flagMember? (member (.str "false")) "k").toOption = some false ∧
    (flagMember? (member .null) "k").toOption = some false ∧
    (flagMember? (Json.mkObj []) "k").toOption = some false ∧
    (flagMember? (member (.str "yes")) "k").toOption = none ∧
    (flagMember? (member (.arr #[])) "k").toOption = none := by
  native_decide

end A12Kernel.Dm
