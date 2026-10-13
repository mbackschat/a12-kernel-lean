import A12Kernel.Reference.Dm.ModelComputation
import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.Validate

/-! # Reader integration for model-supported characters

These locks exercise the spec/06 §A.2 charset boundary through model admission,
stored-document checking, and the reduced computed-target check.
-/

namespace A12Kernel.Dm.SupportedCharactersLocks

open Lean A12Kernel

private def field (name typeName : String) (body : List (String × Json) := []) : Json :=
  Json.mkObj [
    ("type", "Field"), ("id", .str ("/Form/" ++ name)), ("name", .str name),
    ("Field", Json.mkObj [("fieldType", Json.mkObj [
      ("type", .str typeName), (typeName, Json.mkObj body)])])]

private def source (definition : Option Json) : Json :=
  Json.mkObj [("content", Json.mkObj [
    ("modelConfig", Json.mkObj (definition.toList.map ("supportedCharacters", ·))),
    ("modelRoot", Json.mkObj [("rootGroups", Json.arr #[Json.mkObj [
      ("type", "Group"), ("name", "Form"),
      ("Group", Json.mkObj [("repeatability", toJson (1 : Nat)),
        ("elements", Json.arr #[field "S" "StringType", field "N" "NumberType",
          field "Out" "StringType"])])]])])])]

private def world : World := { now := { epochMillis := 0 } }

private def checkedInput (dm : DmModel) (name text : String) :
    Option (CheckedDocument dm.flat) := do
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler dm.flat).toOption
  let raw ← (readDocument dm (Json.mkObj [("Form", Json.mkObj [(name, .str text)])])).toOption
  if !raw.refusals.isEmpty then none
  (checkDocument prepared "en_US" raw.data).toOption

private def storedFindings (definition : Option Json) (name text : String)
    (graphemeClusters? : Option (String → List String) := none) :
    Option (List FormalCause) := do
  let dm ← (readModel (source definition) graphemeClusters?).toOption
  if !dm.refusals.isEmpty then none
  let checked ← checkedInput dm name text
  let declaration ← dm.flat.fields.find? (·.name == name)
  let cell ← (checked.read { field := declaration.id, path := [] }).toOption
  pure cell.findings

private def storedAndComputed (definition : Option Json) :
    Option (List FormalCause × List String) := do
  let dm ← (readModel (source definition)).toOption
  if !dm.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler dm.flat).toOption
  let checked ← checkedInput dm "S" "z"
  let declaration ← dm.flat.fields.find? (·.name == "S")
  let cell ← (checked.read { field := declaration.id, path := [] }).toOption
  let computation : DmComputation := {
    group := ["Form"], name := "C", targetRelPath := "../Out"
    alternatives := [{ operation := "\"z\"", precondition := none }], commonPrecondition := none
    errorCodesToSuppress := [] }
  let result ← (runModelComputations { dm with computations := [computation] }
    .english world prepared checked).toOption
  pure (cell.findings, result.map (·.outcome))

private def restricted : Option Json := some (toJson (["A-Z", "7"] : List String))

private def acute : String := "\u0301"
private def eAcute : String := "e\u0301"
private def qAcute : String := "q\u0301"
private def rGrave : String := "r\u0300"

private def clustersOf (value : String) : List String :=
  if value == eAcute then [eAcute]
  else if value == qAcute then [qAcute]
  else if value == rGrave then [rGrave]
  else if value == qAcute ++ "r" then [qAcute, "r"]
  else if value == eAcute ++ "x" then [eAcute, "x"]
  else value.toList.map (fun character => String.ofList [character])

private def inputFailure? (definition : Option Json)
    (graphemeClusters? : Option (String → List String) := none) : Option String :=
  match readModelWithAdmission (source definition) graphemeClusters? with
  | .error (.input reason) => some reason
  | _ => none

private def compatibilityFailure? (definition : Option Json)
    (graphemeClusters? : Option (String → List String) := none) : Option String :=
  match readModel (source definition) graphemeClusters? with
  | .error reason => some reason
  | .ok _ => none

example :
    [none, some .null, some (toJson ([] : List String))].all (fun definition =>
      storedFindings definition "S" "café" == some [] &&
      storedFindings definition "S" "x😀" == some [.unsupportedCharacter]) := by
  native_decide

example :
    [storedFindings restricted "S" "AZ7" == some [],
     storedFindings restricted "S" "a" == some [.unsupportedCharacter],
     storedFindings restricted "N" "7" == some [],
     storedFindings restricted "N" "9" == some [.unsupportedCharacter]].all id := by
  native_decide

example : storedAndComputed (some (toJson ([] : List String))) =
    some ([], ["value z"]) := by native_decide

example : storedAndComputed restricted =
    some ([.unsupportedCharacter], ["value z"]) := by native_decide

example :
    let definition := some (toJson [eAcute])
    [storedFindings definition "S" eAcute (some clustersOf) == some [],
     storedFindings definition "S" "e" (some clustersOf) == some [.unsupportedCharacter],
     storedFindings definition "S" acute (some clustersOf) == some [.unsupportedCharacter],
     (readModelWithAdmission (source definition) (some clustersOf)).isOk].all id := by
  native_decide

example :
    let definition := some (toJson [eAcute, eAcute ++ "x"])
    [storedFindings definition "S" (eAcute ++ "x" ++ eAcute) (some clustersOf) == some [],
     storedFindings definition "S" "x" (some clustersOf) == some [.unsupportedCharacter]].all id := by
  native_decide

example :
    inputFailure? (some (toJson [qAcute ++ "r", qAcute, rGrave])) (some clustersOf) =
      some (s!"supportedCharacters definition: {repr (SupportedCharactersDefinitionError.ambiguousOverlap 0)}") := by
  native_decide

example :
    [eAcute, "ab", eAcute ++ "x"].all (fun entry =>
      let definition := some (toJson [entry])
      inputFailure? definition == some "supportedCharacters requires Java-compatible grapheme preparation" &&
      compatibilityFailure? definition == inputFailure? definition) := by
  native_decide

example :
    [some (.str "A-Z"), some (toJson (7 : Nat)), some (Json.mkObj []),
     some (Json.arr #[.str "A", toJson (7 : Nat)]), some (Json.arr #[.null])].all
      (fun definition => (inputFailure? definition).isSome &&
        compatibilityFailure? definition == inputFailure? definition) := by
  native_decide

example :
    ["", "😀", "abcd", "Z-A"].all (fun entry =>
      let definition := some (toJson [entry])
      (inputFailure? definition).isSome &&
      compatibilityFailure? definition == inputFailure? definition) := by
  native_decide

example :
    inputFailure? (some (toJson ["ab"])) (some clustersOf) =
      some (s!"supportedCharacters definition: {repr (SupportedCharactersDefinitionError.plainMultiCharacterEntry 0)}") := by
  native_decide

example :
    [inputFailure? (some (toJson ([] : List String))) == none,
     inputFailure? (some (toJson [""])) ==
       some (s!"supportedCharacters definition: {repr (SupportedCharactersDefinitionError.emptyEntry 0)}")].all id := by
  native_decide

private def ingestionNames : List String := ["Raw", "Plain", "Pattern", "Custom", "Reported"]

private def ingestionSource : Json :=
  Json.mkObj [("content", Json.mkObj [
    ("modelConfig", Json.mkObj [("fieldRefByShortNameAllowed", .bool true),
      ("supportedCharacters", toJson (["A-Z", "0-9", "\r", "\n", " "] : List String))]),
    ("modelRoot", Json.mkObj [("rootGroups", Json.arr #[Json.mkObj [
      ("type", "Group"), ("name", "Form"),
      ("Group", Json.mkObj [("repeatability", toJson (1 : Nat)),
        ("elements", Json.arr #[
          field "Raw" "StringType" [("noValueValidation", .bool true), ("lineBreaksPermitted", .bool true)],
          field "Plain" "StringType" [("maxLength", toJson (2 : Nat))],
          field "Pattern" "StringType" [("pattern", "[A-Z]+")],
          field "Custom" "CustomFieldType" [("name", "Upper")],
          field "Reported" "CustomFieldType" [("name", "Report")],
          field "Witness" "StringType", field "Distinct" "NumberType",
          Json.mkObj [("type", "Group"), ("name", "Rows"),
            ("Group", Json.mkObj [("repeatability", toJson (2 : Nat)),
              ("elements", Json.arr #[
                field "Value" "CustomFieldType" [("name", "Loose")],
                field "Copy" "CustomFieldType" [("name", "Loose")],
                field "Size" "NumberType"])])]])])]])])])]

private def ingestionWorld : World := { world with
  customFieldValidator? := fun name =>
    if name == "Upper" then some fun value _ =>
      if matchesAsciiUppercasePattern value then none
      else some { projectCode := "UPPER" }
    else if name == "Report" then some fun _ _ => some { projectCode := "testIDNummer" }
    else if name == "Loose" then some fun _ _ => none
    else none }

private def ingestionRow (text : Option String) : Json :=
  Json.mkObj (text.toList.map (fun value => ("Value", Json.str value)) ++
    [("Copy", Json.str "OLD"), ("Size", toJson (7 : Nat))])

private def ingestion (text : Option String) :
    Option (List CheckedCell × List (String × String)) := do
  let dm ← (readModel ingestionSource).toOption
  if !dm.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext ingestionWorld builtinStringPatternCompiler dm.flat).toOption
  let fields : List (String × Json) :=
    ingestionNames.flatMap fun name => text.toList.map (fun value => (name, .str value))
  let document := Json.mkObj [("Form", Json.mkObj (fields ++ [
    ("Rows", Json.arr #[ingestionRow text, ingestionRow (some "AB")])]))]
  let raw ← (readDocument dm document).toOption
  if !raw.refusals.isEmpty then none
  let checked ← (checkDocument prepared "en_US" raw.data).toOption
  let cells ← ingestionNames.mapM fun name => do
    let declaration ← dm.flat.fields.find? (fun field => field.groupPath == ["Form"] && field.name == name)
    (checked.read { field := declaration.id, path := [] }).toOption
  let computation (name target operation : String) : DmComputation := {
    group := ["Form", "Rows"], name, targetRelPath := "../" ++ target
    commonPrecondition := none, alternatives := [{ precondition := none, operation }]
    errorCodesToSuppress := [] }
  let results ← (runModelComputations { dm with computations := [
    computation "CCopy" "Copy" "[Value]", computation "CSize" "Size" "Length(Value)" ] }
    .english ingestionWorld prepared checked).toOption
  pure (cells, results.map fun result => (result.pointer, result.outcome))

private def rowResults (copy size : String) : List (String × String) := [
  ("Form/Rows/Copy", copy), ("Form/Rows[2]/Copy", "value AB"),
  ("Form/Rows/Size", size), ("Form/Rows[2]/Size", "value 2")]

private def baselineFirst (text : String) (cause : FormalCause) : Bool :=
  match ingestion (some text) with
  | none => false
  | some (cells, results) =>
      cells.head? == some { rawPresent := true, parsed := some (.str text), findings := [] } &&
      cells.drop 1 == List.replicate 4 { rawPresent := true, parsed := none, findings := [cause] } &&
      results == rowResults "cleared" "cleared"

example :
    ["ab", " ab"].all (fun text => baselineFirst text .unsupportedCharacter) := by
  native_decide

example :
    [" AB", "AB "].all (fun text => baselineFirst text .leadingOrTrailingSpace) := by
  native_decide

example :
    (ingestion (some "AB")).map Prod.fst = some (
      List.replicate 4 { rawPresent := true, parsed := some (.str "AB"), findings := [] } ++
      [{ rawPresent := true, parsed := some (.str "AB"), findings := [], reports :=
           [.registeredCustomValidation { projectCode := "testIDNummer" }] }]) := by
  native_decide

example :
    (ingestion (some "77")).map (fun (cells, _) => cells.map (·.formalReports)) =
      some [[], [], [.declaredConstraint], [.registeredCustomValidation { projectCode := "UPPER" }],
        [.registeredCustomValidation { projectCode := "testIDNummer" }]] := by
  native_decide

example :
    [none, some ""].all (fun text =>
      (ingestion text).map Prod.fst == some (List.replicate 5 {
        rawPresent := text.isSome, parsed := none, findings := [] }) &&
      (ingestion text).map Prod.snd == some (rowResults "cleared" "value 0")) := by
  native_decide

example :
    [("A\r\nB", "value A\nB", "value 3"), ("A\r\r\nB", "value A\r\nB", "value 4")].all
      (fun (text, copy, size) => (ingestion (some text)).map Prod.snd == some (rowResults copy size)) := by
  native_decide

/- The technical cap counts the authored text in UTF-16 units before charset and blank checks, and
bypasses only the raw switch: each overlength row below would report charset, a blank or a declared
length under a scalar count, a normalized count or a later guard (pinned `FormalChecker`). -/
private def letters (count : Nat) : String := String.ofList (List.replicate count 'A')

example :
    let text := letters 99999
    (ingestion (some text)).map (fun (cells, results) => (cells.map (·.formalReports), results)) =
      some ([[], [.declaredConstraint], [], [],
        [.registeredCustomValidation { projectCode := "testIDNummer" }]],
        rowResults s!"value {text}" "value 99999") := by
  native_decide

example :
    [letters 100000, letters 99998 ++ "😀", letters 100000 ++ "😀",
     " " ++ letters 99999].all (fun text => baselineFirst text .valueTooLong) := by
  native_decide

/- A CRLF pair counts twice although the stored text later normalizes it to one unit. Only the four
checked cells are compared; the raw cell bypasses this guard. -/
example :
    (ingestion (some (letters 99998 ++ "\r\n"))).map (fun pair => (pair.1.drop 1, pair.2)) =
      some (List.replicate 4 { rawPresent := true, parsed := none, findings := [.valueTooLong] },
        rowResults "cleared" "cleared") := by
  native_decide

example : baselineFirst (letters 99997 ++ "😀") .unsupportedCharacter := by
  native_decide

example : FormalCause.valueTooLong.fixedFormalErrorCode? = some "wertZuLang" := by
  native_decide

/- The reduced computed-target check has no technical cap, but a String target without a declared
maximum still carries its runtime format's 99,999 units: an overlength concatenation of two admitted
values is ERRORED with its attempt kept (peer KF547 `CheckedInputOrderDiffTest`, a12-dmkits
`4b5e73812`). -/
example :
    (do
      let dm ← (readModel ingestionSource).toOption
      let prepared ← (prepareFlatStringContext ingestionWorld builtinStringPatternCompiler dm.flat).toOption
      let raw ← (readDocument dm (Json.mkObj [("Form", Json.mkObj [("Pattern", .str (letters 50000))])])).toOption
      let checked ← (checkDocument prepared "en_US" raw.data).toOption
      let concatenation : DmComputation := {
        group := ["Form"], name := "CTwice", targetRelPath := "../Witness"
        commonPrecondition := none
        alternatives := [{ precondition := none, operation := "[Pattern] + [Pattern]" }]
        errorCodesToSuppress := [] }
      let results ← (runModelComputations { dm with computations := [concatenation] }
        .english ingestionWorld prepared checked).toOption
      pure (results.map (·.outcome))) = some [s!"errored {letters 100000}"] := by
  native_decide

private inductive Domain where
  | rows | mixed
  deriving BEq

private def domainResults (domain : Domain) (first second : String) :
    Option (List String × List (String × String)) := do
  let dm ← (readModel ingestionSource).toOption
  if !dm.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext ingestionWorld builtinStringPatternCompiler dm.flat).toOption
  let rowValues := if domain == .rows then [first, second] else ["AB", "AB"]
  let mixedValues := if domain == .mixed then [("Custom", Json.str first), ("Plain", Json.str second)] else []
  let document := Json.mkObj [("Form", Json.mkObj (mixedValues ++ [
    ("Witness", Json.str "AB"), ("Distinct", toJson (9 : Nat)),
    ("Rows", Json.arr (rowValues.map (ingestionRow ∘ some)).toArray)]))]
  let raw ← (readDocument dm document).toOption
  if !raw.refusals.isEmpty then none
  let checked ← (checkDocument prepared "en_US" raw.data).toOption
  let operands := match domain with
    | .rows => "Rows*/Value"
    | .mixed => "Custom, Plain"
  let count : DmComputation := {
    group := ["Form"], name := "Count", targetRelPath := "../Distinct"
    commonPrecondition := none
    alternatives := [{ precondition := none, operation := s!"NumberOfDifferentValues({operands})" }]
    errorCodesToSuppress := [] }
  let counts ← (runModelComputations { dm with computations := [count] }
    .english ingestionWorld prepared checked).toOption
  let definition : DmRule := {
    group := ["Form"], name := "Unique", errorEntityRelPath := "../Witness"
    errorCode := "UNIQUE", condition := s!"FieldFilled(Witness) And FieldValuesNotUnique({operands})"
    severity := "ERROR" }
  let rule ← (checkRule dm .english definition ingestionWorld).toOption
  let messages ← (runRule ingestionWorld checked rule).toOption
  pure (counts.map (·.outcome), messages.map fun message =>
    let result := observe dm.flat message
    (result.pointer, result.messageType))

private def domainExpected (count : String) (duplicate : Bool) :
    Option (List String × List (String × String)) :=
  some ([count], if duplicate then [("Form/Witness", "VALUE_ERROR")] else [])

example :
    [("AB", "AB", "value 1", true),
     ("A\r\nB", "A\nB", "value 1", true),
     ("A\r\r\nB", "A\nB", "value 2", false),
     ("ab", "AB", "cleared", false),
     ("", "AB", "value 1", false)].all (fun (first, second, count, duplicate) =>
      domainResults .rows first second == domainExpected count duplicate) := by
  native_decide

example :
    [("AB", "AB", "value 1", true), ("12", "12", "cleared", false),
     ("", "", "value 0", false)].all (fun (first, second, count, duplicate) =>
      domainResults .mixed first second == domainExpected count duplicate) := by
  native_decide

end A12Kernel.Dm.SupportedCharactersLocks
