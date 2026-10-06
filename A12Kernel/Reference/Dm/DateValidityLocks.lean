import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.Replay

namespace A12Kernel.Dm.DateValidityLocks

private def model : FlatModel :=
  let number (id : FieldId) (name : String) (width : Nat) : FlatFieldDecl := {
    id, name, groupPath := ["Form", "Rows"], repeatableScope := [10]
    policy := { kind := .number { scale := 0, signed := false } }
    numericTargetConstraints := { maxStoredLength := some width } }
  let text (id : FieldId) (name : String) (width : Nat) : FlatFieldDecl := {
    id, name, groupPath := ["Form", "Rows"], repeatableScope := [10]
    policy := { kind := .string }, stringPolicy := { maxLength := some width }
    stringPatternSource := some "[0-9]+" }
  let date (id : FieldId) (name : String) (format : String) (components : TemporalComponents)
      (partialMode : TemporalPartialMode := .full) : FlatFieldDecl := {
    id, name, groupPath := ["Form", "Rows"], repeatableScope := [10]
    policy := { kind := .temporal .date components }, temporalTargetPolicy := some { format, partialMode } }
  { fields := [
      { id := 0, name := "Out", groupPath := ["Form"], policy := { kind := .temporal .date .fullDate }
        temporalTargetPolicy := some { format := "yyyy-MM-dd" } },
      { id := 1, name := "Key", groupPath := ["Form"], policy := { kind := .string } },
      { id := 2, name := "Code", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .string } },
      { id := 3, name := "After", groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := false } } },
      number 4 "Day" 2, number 5 "Month" 2, number 6 "Year" 4, number 7 "Century" 2, number 8 "ShortYear" 2,
      text 9 "DayText" 2, text 11 "MonthText" 2, text 12 "YearText" 4,
      date 13 "YearDate" "yyyy" { year := true, month := false, day := false, hour := false, minute := false, second := false },
      date 14 "Full" "yyyy-MM-dd" .fullDate,
      date 15 "Partial" "yyyy-MM-dd" .fullDate .yearOptional,
      { id := 16, name := "D", groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := false } }, numericTargetConstraints := { maxStoredLength := some 2 } },
      { id := 17, name := "M", groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := false } }, numericTargetConstraints := { maxStoredLength := some 2 } },
      { id := 18, name := "Y", groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := false } }, numericTargetConstraints := { maxStoredLength := some 4 } },
      { id := 19, name := "NumberOut", groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := false } } } ]
    repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 3, indexField := some 2 }]
    baseYear := some 2024, timeZoneId := "UTC" }

private structure Scenario where
  key : String := "B"
  duplicate : Bool := false
  selected : List (String × String) := []
  keyProducer : Bool := false
  sourceProducer : Bool := false
  omitted : List String := []

private def input (scenario : Scenario) : Lean.Json :=
  let row (code day month year full partialText : String) (overrides : List (String × String)) :=
    Lean.Json.mkObj (([("Code", code), ("Day", day), ("Month", month), ("Year", year),
      ("Century", "20"), ("ShortYear", "24"), ("DayText", day), ("MonthText", month),
      ("YearText", year), ("YearDate", year), ("Full", full), ("Partial", partialText)].map fun (name, value) =>
        (name, Lean.Json.str ((overrides.lookup name).getD value))).filter fun entry => !scenario.omitted.contains entry.1)
  Lean.Json.mkObj [("Form", Lean.Json.mkObj [
    ("Out", .str "2001-12-25"), ("NumberOut", .str "9"), ("D", .str "29"), ("M", .str "2"), ("Y", .str "2024"), ("After", .str "9"), ("Key", .str scenario.key),
    ("Rows", .arr #[row (if scenario.duplicate then "B" else "A") "01" "01" "2023" "2023-01-01" "2023-01-00" [],
      row "B" "29" "02" "2024" "2024-02-29" "2024-02-00" scenario.selected])])]

private def checked (scenario : Scenario) (fixture : FlatModel := model) : Option (CheckedDocument fixture) := do
  let model := fixture
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } } builtinStringPatternCompiler model).toOption
  let raw ← (readDocument { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
    (input scenario)).toOption
  (checkDocument prepared "en_US" raw.data).toOption

private def forms := [
  "Date(Rows/Day For Key,Rows/Month For Key,Rows/Year For Key)",
  "Date(Rows/DayText For Key,Rows/MonthText For Key,Rows/YearText For Key)",
  "Date(\"1\",\"2\",Rows/YearDate For Key)",
  "Date(DayFromDate(AddDays(Rows/Full For Key,1)),Rows/Month For Key,YearFromDate(AddDays(Rows/Full For Key,1)))",
  "Date(\"1\",Rows/Month For Key,YearFromDate(AddDays(ValueAsDate(Rows/Partial For Key,FirstDay),1)))",
  "Date(DayFromDate(AddDays(ValueAsDate(Rows/Partial For Key,FirstDay),1)),Rows/Month For Key,Rows/Year For Key)",
  "Date(Rows/Day For Key,Rows/Month For Key)",
  "Date(Rows/Day For Key,Rows/Month For Key,Rows/Century For Key,Rows/ShortYear For Key)"]

private def predicate (operation source : String) := operation ++ "(" ++ source ++ ")"

private def validate (expression : String) (scenario : Scenario := {}) (fixture : FlatModel := model) : Option Verdict := do
  let model := fixture
  let document ← checked scenario model
  let parsed ← (parseText .english expression).toOption
  let condition ← (lowerCondition model ["Form"] false parsed.body).toOption
  (condition.core.evalAddressed {
    scalar := { fields := document.flatContext, groups := GroupPresenceContext.unavailable },
    outer := [], input := .checked document }).toOption

private def run (guard : String) (scenario : Scenario := {})
    (common temporal : Bool := false) (fixture : FlatModel := model) : Option (List String) := do
  let model := fixture
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let document ← checked scenario model
  let target := if temporal then "Out" else "NumberOut"
  let definitions : List DmComputation := ([{
    name := "After", group := ["Form"], targetRelPath := "../After",
    commonPrecondition := some ("FieldNotFilled(" ++ target ++ ")"),
    alternatives := [{ precondition := none, operation := "1" }], errorCodesToSuppress := [] }, {
    name := "Guard", group := ["Form"], targetRelPath := "../" ++ target,
    commonPrecondition := (if common then some guard else none),
    alternatives := [{ precondition := (if common then none else some guard), operation := (if temporal then "AddDays(\"01.03.2024\",0)" else "1") }] ++
        (if common then [] else [{ precondition := some "FieldFilled(D)", operation := (if temporal then "AddDays(\"02.03.2024\",0)" else "2") }]), errorCodesToSuppress := [] }] ++
      (if scenario.keyProducer then [{ name := "Key", group := ["Form"], targetRelPath := "../Key", commonPrecondition := none, alternatives := [{ precondition := none, operation := "\"B\"" }], errorCodesToSuppress := [] }] else []) ++
      (if scenario.sourceProducer then [{ name := "Day", group := ["Form"], targetRelPath := "../Rows/Day", commonPrecondition := none, alternatives := [{ precondition := none, operation := "31" }], errorCodesToSuppress := [] }] else []))
  let steps ← definitions.mapM fun definition =>
          (lowerComputation model .english definition).toOption.map (·.2)
  let results ← (runComputations world prepared document steps).toOption
  pure ((results.filter (fun result => !result.pointer.endsWith "/Key" && !result.pointer.endsWith "/Day")).map
    (fun result => result.pointer ++ ":" ++ result.outcome)).mergeSort

example : forms.all (fun source =>
    validate (predicate "Valid" source) == some (.fired .value) &&
    validate (predicate "Invalid" source) == some .notFired &&
    run (predicate "Valid" source) == some ["Form/After:cleared", "Form/NumberOut:value 1"] &&
    run (predicate "Invalid" source) == some ["Form/After:cleared", "Form/NumberOut:value 2"]) = true := by native_decide

private def noEntity := ["Date(\"1\",\"2\",\"2024\")",
  "Date(DayFromDate(Out),MonthFromDate(Out),YearFromDate(Out))",
  "Date(DayFromDate(AddDays(Rows/Full For Key,1)),MonthFromDate(AddDays(Rows/Full For Key,1)),YearFromDate(AddDays(Rows/Full For Key,1)))"]

example : ["Valid", "Invalid"].all (fun operation =>
    noEntity.all (fun source => (validate (predicate operation source)).isNone &&
      (run (predicate operation source)).isNone) &&
    validate (predicate operation "Date(D,M,Y)") ==
      some (if operation == "Valid" then .fired .value else .notFired)) = true := by native_decide

private inductive Expected where
  | real | empty | unreal | poison | nonRelevant
  deriving BEq

private def expectedVerdict (operation : String) : Expected → Verdict
  | .real => if operation == "Valid" then .fired .value else .notFired
  | .empty => if operation == "Invalid" then .fired .omission else .notFired
  | .unreal => if operation == "Invalid" then .fired .value else .notFired
  | .poison | .nonRelevant => .unknown

private def expectedRun (operation : String) (expected : Expected) (common temporal : Bool) : List String :=
  let target := if temporal then "Form/Out:" else "Form/NumberOut:"
  if expected == .poison then ["Form/After:cleared", target ++ "cleared"]
  else if (match expectedVerdict operation expected with | .fired _ => true | _ => false) then
    ["Form/After:cleared", target ++ (if temporal then "value 2024-03-01" else "value 1")]
  else if common then ["Form/After:value 1", target ++ "cleared"]
  else ["Form/After:cleared", target ++ (if temporal then "value 2024-03-02" else "value 2")]

private def states : List (Scenario × List Expected) :=
  let filled := ["Day", "Month", "Year", "Century", "ShortYear", "DayText", "MonthText", "YearText", "YearDate", "Full", "Partial"]
  [({}, List.replicate 8 .real),
    ({ selected := filled.map (·, "") }, List.replicate 8 .empty),
    ({ key := "missing" }, List.replicate 8 .empty),
    ({ duplicate := true }, List.replicate 8 .poison),
    ({ selected := filled.map (·, "bad") }, List.replicate 8 .poison),
    ({ selected := [("Partial", "0000-00-00")] }, [.real, .real, .real, .real, .nonRelevant, .nonRelevant, .real, .real]),
    ({ selected := [("Day", "31"), ("DayText", "31")] }, [.unreal, .unreal, .real, .real, .real, .real, .unreal, .unreal]),
    ({ selected := [("Partial", "0000-00-00"), ("Month", "bad")] }, [.poison, .real, .real, .poison, .poison, .poison, .poison, .poison])]

example : states.all (fun (scenario, expected) =>
    (forms.zip expected).all fun (source, expected) =>
      ["Valid", "Invalid"].all fun operation =>
        validate (predicate operation source) scenario == some (expectedVerdict operation expected) &&
        [false, true].all fun common => [false, true].all fun temporal =>
          run (predicate operation source) scenario common temporal == some (expectedRun operation expected common temporal)) = true := by native_decide

private def ruleMessages (expression : String) (scenario : Scenario := {}) : Option (List String) := do
  let document ← checked scenario
  let rule ← (checkRule { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
    .english { name := "Rule", group := ["Form"], errorCode := "PROBE", errorEntityRelPath := "../Key", condition := expression, severity := "ERROR" }).toOption
  let messages ← (runRule { now := { epochMillis := 0 } } document rule).toOption
  pure (messages.map fun message => (observe model message).messageType)

example : states.all (fun (scenario, expected) =>
    (forms.zip expected).all fun (source, expected) =>
      ["Valid", "Invalid"].all fun operation =>
        ruleMessages (predicate operation source) scenario == some (match expectedVerdict operation expected with
          | .fired .value => ["VALUE_ERROR"]
          | .fired .omission => ["OMISSION_ERROR"]
          | _ => [])) = true := by native_decide

example : ["Valid", "Invalid"].all (fun operation =>
    validate (predicate operation forms[0]!) { omitted := ["Day"] } ==
      some (expectedVerdict operation .empty) &&
    validate (predicate operation forms[0]!) { key := "" } ==
      some (expectedVerdict operation .empty) &&
    run (predicate operation forms[0]!) { key := "missing", keyProducer := true } ==
      some (expectedRun operation .real false false)) = true := by native_decide

example : ["Date(Rows/Full For Key,\"2\",\"2024\")",
    "Date(MonthFromDate(Rows/Full For Key),Rows/Month For Key,\"2024\")",
    "Date(Rows/Day For Key,Rows/Month For Key,YearFromDate(Rows/Full For Key),\"24\")"].all (fun source =>
      ["Valid", "Invalid"].all fun operation => (validate (predicate operation source)).isNone &&
        (run (predicate operation source)).isNone) = true := by native_decide

private def partialAndPointerBoundary (source : String) : Option Bool := do
  let document ← checked {}
  let parsed ← (parseText .english (predicate "Valid" source)).toOption
  let condition ← (lowerCondition model ["Form"] false parsed.body).toOption
  let .leaf leaf := condition.core | none
  pure (leaf.supportsAddressedPartial &&
    (leaf.evalAddressedPartial? { scalar := { fields := document.flatContext, groups := GroupPresenceContext.unavailable }, outer := [], input := .checked document } .full (fun _ => true)
      (fun _ _ => .error (.checkedDocumentRequired [])) none).bind Except.toOption == some (.fired .value) &&
    match condition.core.referencePointers [] with
    | .error .unclassifiedOperand => true
    | _ => false)

example : forms.all (fun source => partialAndPointerBoundary source == some true) = true := by native_decide

private def staticCodes (source : String) : Option (Option String × Option String) := do
  let parsed ← (parseText .english source).toOption
  let .call "Date" arguments none none := parsed.body | none
  let components ← (lowerScalarDateComponents model ["Form"] arguments).toOption
  let validation := match CheckedValidationCondition.fromConstructedDateValidity model ["Form"] .valid components with
    | .error error => error.groupListDiagnostic?.map (·.kernelCode)
    | .ok _ => none
  let computation := match model.elaborateComputationPredicate ["Form"] ["Form"] (.dateValidity .invalid components) with
    | .error error => error.dateValidityDiagnostic?.map (·.kernelCode)
    | .ok _ => none
  pure (validation, computation)

example : noEntity.all (fun source => staticCodes source ==
    some (some "MVK_ONLY_CONSTANTS_USED", some "MVK_ONLY_CONSTANTS_USED")) = true := by native_decide

private def extensibleModel : FlatModel := { model with fields := model.fields.map fun field =>
  if field.id == 9 then { field with stringExtensibleEnum := true, stringPatternSource := none } else field }

private def genericFault : Option Bool := do
  let document ← checked { selected := [("DayText", "x")] } extensibleModel
  let parsed ← (parseText .english (predicate "Valid" forms[1]!)).toOption
  let condition ← (lowerCondition extensibleModel ["Form"] false parsed.body).toOption
  pure (match condition.core.evalAddressed {
    scalar := { fields := document.flatContext, groups := GroupPresenceContext.unavailable },
    outer := [], input := .checked document } with
    | .error .temporalUnavailable => true
    | _ => false)

private def genericComputationFault : Option Bool := do
  let document ← checked { selected := [("DayText", "x")] } extensibleModel
  let parsed ← (parseText .english forms[1]!).toOption
  let .call "Date" arguments none none := parsed.body | none
  let surface ← (lowerScalarDateComponents extensibleModel ["Form"] arguments).toOption
  let predicate ← (extensibleModel.elaborateComputationPredicate ["Form"] ["Form"] (.dateValidity .valid surface)).toOption
  pure (match predicate.evalChecked (document.indexedComputationContextAt []) with
    | .error .valueFailure => true
    | _ => false)

example : genericFault = some true ∧ genericComputationFault = some true ∧
    run (predicate "Valid" forms[1]!) { selected := [("DayText", "x")] } true false extensibleModel =
      some ["Form/After:cleared", "Form/NumberOut:cleared"] := by native_decide

private def metadata : Option Bool := do
  let parsed ← (parseText .english (predicate "Valid" forms[0]!)).toOption
  let condition ← (lowerCondition model ["Form"] false parsed.body).toOption
  let .leaf (.constructedDateValidity _ components) := condition.core | none
  pure (components.scalarFieldIds.contains 1 && components.scalarFieldIds.contains 2 &&
    [4,5,6].all components.scalarFieldIds.contains && components.scalarBoundFieldIds == [1,1,1] &&
    components.scalarBindingScopes.all List.isEmpty &&
    (match condition.core.ordinaryIterationScope with | .ok none => true | _ => false))

example : metadata = some true := by native_decide

private def currentRead (source : String) (cellOverride : Bool) : Option Verdict := do
  let document ← checked {}
  let parsed ← (parseText .english source).toOption
  let .call "Date" arguments none none := parsed.body | none
  let surface ← (lowerScalarDateComponents model ["Form"] arguments).toOption
  let components ← (elaborateScalarDateValidityComponents model ["Form"] surface).toOption
  let context := document.indexedComputationContextAt []
  let some addressed := context.addressed | none
  let current := { addressed with
    read := fun row field => if cellOverride && row == [(10,2)] && field == 4 then
      checkAdmittedRawCell (.parsed (.num 31)) else addressed.read row field
    storedText := fun row field => if !cellOverride && row == [(10,2)] && field == 15 then
      some "0000-00-00" else addressed.storedText row field }
  let observation ← (components.evaluateScalarValidity .computation { context with addressed := some current }).toOption
  (observation.validityVerdict .valid).toOption

example : currentRead forms[0]! true = some .notFired ∧
    currentRead forms[4]! false = some .unknown := by native_decide

example : ["Valid", "Invalid"].all (fun operation =>
    run (predicate operation forms[0]!) { sourceProducer := true } true false ==
      some (expectedRun operation .unreal true false) &&
    validate (predicate operation (forms[0]!.replace " For Key" " For \"B\"")) { key := "missing" } ==
      some (expectedVerdict operation .real)) = true := by native_decide

private def directRecursive := "Date(D,MonthFromDate(AddDays(Out,1)),YearFromDate(AddDays(Out,1)))"

example : validate (predicate "Valid" directRecursive) = some (.fired .value) ∧
    partialAndPointerBoundary directRecursive = some true := by native_decide

example : ValidationConditionAssemblyError.emptyGroupList.groupListDiagnostic? = none := by decide

end A12Kernel.Dm.DateValidityLocks
