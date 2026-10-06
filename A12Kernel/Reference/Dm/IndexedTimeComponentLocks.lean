import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.Replay

namespace A12Kernel.Dm.IndexedTimeComponentLocks

private def model : FlatModel :=
  let number (id : FieldId) (name : String) (path : GroupPath := ["Form", "Rows"])
      (scope : List RepeatableLevel := [10]) : FlatFieldDecl := {
    id, name, groupPath := path, repeatableScope := scope
    policy := { kind := .number { scale := 0, signed := false } }
    numericTargetConstraints := { maxStoredLength := some 2 } }
  let text (id : FieldId) (name : String) : FlatFieldDecl := {
    id, name, groupPath := ["Form", "Rows"], repeatableScope := [10]
    policy := { kind := .string }, stringPolicy := { maxLength := some 2 }
    stringPatternSource := some "[0-9]+" }
  let temporal (id : FieldId) (name : String) (kind : TemporalKind) (components : TemporalComponents)
      (format : String) : FlatFieldDecl := {
    id, name, groupPath := ["Form"], policy := { kind := .temporal kind components }
    temporalTargetPolicy := some { format } }
  { fields := [temporal 0 "Out" .time .time "HH:mm:ss",
      { id := 1, name := "Key", groupPath := ["Form"], policy := { kind := .string } },
      { id := 2, name := "Code", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .string } },
      { id := 3, name := "After", groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := false } } },
      number 4 "Hour", number 5 "Minute", number 6 "Second", text 7 "HText", text 8 "MText", text 9 "SText",
      { temporal 10 "Clock" .time .time "HH:mm:ss" with groupPath := ["Form", "Rows"], repeatableScope := [10] },
      { id := 11, name := "NumberOut", groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := true } } },
      temporal 12 "StampOut" .dateTime .now "yyyy-MM-dd'T'HH:mm:ss",
      number 13 "H" ["Form"] [], number 14 "M" ["Form"] [], number 15 "S" ["Form"] [],
      { text 16 "T" with groupPath := ["Form"], repeatableScope := [] }]
    repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 3, indexField := some 2 }]
    timeZoneId := "UTC" }

private structure Scenario where
  key : String := "B"
  duplicate : Bool := false
  selected : List (String × String) := []
  unselected : List (String × String) := []
  omitted : List String := []
  keyProducer : Bool := false
  sourceProducer : Option (String × String) := none

private def input (scenario : Scenario) : Lean.Json :=
  let row (code hour minute second : String) (overrides : List (String × String)) (omitted : List String) :=
    let padded (value : String) := "0" ++ value
    Lean.Json.mkObj (([("Code", code), ("Hour", hour), ("Minute", minute), ("Second", second),
      ("HText", padded hour), ("MText", padded minute), ("SText", padded second), ("Clock", "03:04:05")].map
        fun (name, value) => (name, Lean.Json.str ((overrides.lookup name).getD value))).filter
          fun entry => !omitted.contains entry.1)
  Lean.Json.mkObj [("Form", Lean.Json.mkObj [
    ("Out", .str "01:02:03"), ("NumberOut", .str "9"), ("StampOut", .str "2001-12-25T01:02:03"),
    ("After", .str "9"), ("Key", .str scenario.key), ("H", .str "3"), ("M", .str "4"), ("S", .str "5"), ("T", .str "03"),
    ("Rows", .arr #[row (if scenario.duplicate then "B" else "A") "1" "2" "3" scenario.unselected [],
      row "B" "3" "4" "5" scenario.selected scenario.omitted])])]

private def checked (scenario : Scenario) (fixture : FlatModel := model) : Option (CheckedDocument fixture) := do
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } } builtinStringPatternCompiler fixture).toOption
  let raw ← (readDocument { flat := fixture, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
    (input scenario)).toOption
  (checkDocument prepared "en_US" raw.data).toOption

private def run (source : String) (scenario : Scenario := {}) (target : String := "Out") : Option (List String) := do
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let document ← checked scenario
  let definitions : List (String × String × Option String) := [("After", "1", some ("FieldNotFilled(" ++ target ++ ")")), (target, source, none)] ++
    (if scenario.keyProducer then [("Key", "\"B\"", none)] else []) ++
    scenario.sourceProducer.toList.map (fun (field, value) => ("Rows/" ++ field, value, none))
  let steps ← definitions.mapM fun (target, operation, guard) =>
      (lowerComputation model .english {
        name := target ++ "Comp", group := ["Form"], targetRelPath := "../" ++ target
        commonPrecondition := guard, alternatives := [{ precondition := none, operation }], errorCodesToSuppress := [] }).toOption
  let results ← (runComputations world prepared document (steps.map (·.2))).toOption
  pure ((results.filter (fun result => result.pointer == "Form/After" || result.pointer == "Form/" ++ target)).map
    (fun result => result.pointer ++ ":" ++ result.outcome)).mergeSort

private inductive Role where
  | ordinary | extractors | nested | minimum | stamp | numeric
  deriving BEq

private structure Case where
  source : String
  expected : String
  target : String := "Out"
  role : Role := .ordinary
  deriving Inhabited

private def numberThree := "Time(Rows/Hour For Key,Rows/Minute For Key,Rows/Second For Key)"

private def cases : List Case := [
  { source := "Time(Rows/Hour For Key)", expected := "03:00:00" },
  { source := "Time(Rows/Hour For Key,Rows/Minute For Key)", expected := "03:04:00" },
  { source := numberThree, expected := "03:04:05" },
  { source := "Time(Rows/HText For Key)", expected := "03:00:00" },
  { source := "Time(Rows/HText For Key,Rows/MText For Key)", expected := "03:04:00" },
  { source := "Time(Rows/HText For Key,Rows/MText For Key,Rows/SText For Key)", expected := "03:04:05" },
  { source := "Time(Rows/HText For Key,\"4\",Rows/Second For Key)", expected := "03:04:05" },
  { source := "Time(HoursFromTime(Rows/Clock For Key),MinutesFromTime(Rows/Clock For Key),SecondsFromTime(Rows/Clock For Key))", expected := "03:04:05", role := .extractors },
  { source := "Time(HoursFromTime(" ++ numberThree ++ "),Rows/Minute For Key,Rows/Second For Key)", expected := "03:04:05", role := .nested },
  { source := "Min(" ++ numberThree ++ ",\"09:00:00\")", expected := "03:04:05", role := .minimum },
  { source := "DateTime(\"01.02.2024\"," ++ numberThree ++ ")", expected := "2024-02-01T03:04:05", target := "StampOut", role := .stamp },
  { source := "HoursFromTime(" ++ numberThree ++ ")", expected := "3", target := "NumberOut", role := .numeric }]

private def comparison (case : Case) : String :=
  case.source ++ " == " ++ (if case.target == "NumberOut" then case.expected
    else if case.target == "StampOut" then "\"01.02.2024T03:04:05\"" else "\"" ++ case.expected ++ "\"")

private def validate (case : Case) (scenario : Scenario := {}) : Option Verdict := do
  let document ← checked scenario
  let parsed ← (parseText .english (comparison case)).toOption
  let condition ← (lowerCondition model ["Form"] false parsed.body).toOption
  (condition.core.evalAddressed {
    scalar := { fields := document.flatContext, groups := GroupPresenceContext.unavailable }
    outer := [], input := .checked document }).toOption

example : cases.all (fun case =>
    run case.source {} case.target == some ["Form/After:cleared", "Form/" ++ case.target ++ ":value " ++ case.expected] &&
    validate case == some (.fired .value)) = true := by native_decide

example : [("Time()", "00:00:00"), ("Time(H)", "03:00:00"), ("Time(T,M,S)", "03:04:05"),
    ("Time(H,M,S)", "03:04:05")].all (fun (source, expected) =>
      run source == some ["Form/After:cleared", "Form/Out:value " ++ expected]) = true := by native_decide

private inductive State where
  | known | empty | missing | duplicate | malformed | unreal | unselectedMalformed | omitted | emptyKey
  deriving BEq

private def states : List State := [.known, .empty, .missing, .duplicate, .malformed, .unreal, .unselectedMalformed, .omitted, .emptyKey]

private def scenarioFor : State → Scenario
  | .known => {}
  | .empty => { selected := ["Hour", "Minute", "Second", "HText", "MText", "SText", "Clock"].map (·, "") }
  | .missing => { key := "Z" }
  | .duplicate => { duplicate := true }
  | .malformed => { selected := ["Hour", "Minute", "Second", "HText", "MText", "SText", "Clock"].map (·, "bad") }
  | .unreal => { selected := [("Hour", "24"), ("HText", "24")] }
  | .unselectedMalformed => { unselected := [("Hour", "bad"), ("HText", "bad")] }
  | .omitted => { omitted := ["Hour", "HText"] }
  | .emptyKey => { key := "" }

private def isPoison (state : State) := state == .duplicate || state == .malformed

private def expectedValue (state : State) (entry : Case) : Option String :=
  if isPoison state then none
  else if state == .known || state == .unselectedMalformed then some entry.expected
  else match entry.role with
    | .numeric => some "0"
    | .minimum => some "09:00:00"
    | .extractors => if state == .unreal || state == .omitted then some entry.expected else none
    | .nested => if state == .unreal then some "00:04:05" else none
    | .ordinary | .stamp => none

private def expectedRun (state : State) (entry : Case) : List String :=
  match expectedValue state entry with
  | some value => ["Form/After:cleared", "Form/" ++ entry.target ++ ":value " ++ value]
  | none => ["Form/After:" ++ (if isPoison state then "cleared" else "value 1"), "Form/" ++ entry.target ++ ":cleared"]

private def expectedVerdict (state : State) (entry : Case) : Verdict :=
  if isPoison state then .unknown
  else if expectedValue state entry == some entry.expected then .fired .value else .notFired

private def ruleMessages (entry : Case) (scenario : Scenario) : Option (List String) := do
  let document ← checked scenario
  let rule ← (checkRule { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
    .english { name := "Rule", group := ["Form"], errorCode := "PROBE", errorEntityRelPath := "../Key", condition := "FieldFilled(Key) And " ++ comparison entry, severity := "ERROR" }).toOption
  let messages ← (runRule { now := { epochMillis := 0 } } document rule).toOption
  pure (messages.map fun message => (observe model message).messageType)

example : states.all (fun state => cases.all fun entry =>
    run entry.source (scenarioFor state) entry.target == some (expectedRun state entry) &&
    validate entry (scenarioFor state) == some (expectedVerdict state entry) &&
    ruleMessages entry (scenarioFor state) == some (if expectedVerdict state entry == .fired .value then ["VALUE_ERROR"] else [])) = true := by native_decide

example : ["Time(MinutesFromTime(Rows/Clock For Key))", "Time(Rows/Clock For Key)",
    "Time([Rows/Hour For Key]+1)"].all (fun source => (run source).isNone) = true := by native_decide

private def admitted (source : String) (fixture : FlatModel) : Bool :=
  ((parseText .english source).toOption.bind fun parsed =>
    (lowerScalarTemporalExpression fixture ["Form"] parsed.body).toOption.bind fun surface =>
      (elaborateScalarTemporalExpression fixture ["Form"] surface).toOption).isSome

private def changedField (field : FieldId) (change : FlatFieldDecl → FlatFieldDecl) : FlatModel :=
  { model with fields := model.fields.map fun declaration => if declaration.id == field then change declaration else declaration }

example : [4,5,6].all (fun field =>
    !admitted numberThree (changedField field fun declaration =>
      { declaration with numericTargetConstraints := {} }) &&
    !admitted numberThree (changedField field fun declaration =>
      { declaration with policy := { kind := .number { scale := 1, signed := false } } })) ∧
    [7,8,9].all (fun field =>
      !admitted cases[5]!.source (changedField field fun declaration =>
        { declaration with stringPatternSource := some ".*" }) &&
      !admitted cases[5]!.source (changedField field fun declaration =>
        { declaration with stringPolicy := { maxLength := some 3 } })) := by native_decide

example : [4,5,6].all (fun field =>
    admitted numberThree (changedField field fun declaration =>
      { declaration with numericTargetConstraints := { maximum := some (if field == 4 then 23 else 59) } })) ∧
    admitted cases[5]!.source (changedField 7 fun declaration =>
      { declaration with stringExtensibleEnum := true, stringPatternSource := none }) := by native_decide

example : [cases[2]!, cases[5]!].all (fun entry =>
    run entry.source { key := "Z", keyProducer := true } == some (expectedRun .known entry) &&
    run (entry.source.replace " For Key" " For \"B\"") { key := "Z" } == some (expectedRun .known entry)) = true := by native_decide

example : run numberThree { sourceProducer := some ("Hour", "6") } =
    some ["Form/After:cleared", "Form/Out:value 06:04:05"] ∧
    run cases[5]!.source { sourceProducer := some ("HText", "\"06\"") } =
    some ["Form/After:cleared", "Form/Out:value 06:04:05"] := by native_decide

private def currentSelected (entry : Case) (field : FieldId) (cell : CheckedCell) : Option (TimeOfDay × Bool) := do
  let document ← checked {}
  let parsed ← (parseText .english entry.source).toOption
  let surface ← (lowerScalarTemporalExpression model ["Form"] parsed.body).toOption
  let expression ← (elaborateScalarTemporalExpression model ["Form"] surface).toOption
  if !(expression.referencesField 1 && expression.referencesField 2 && expression.referencesField field &&
      expression.requiresAddressed && expression.bindingScopes.all List.isEmpty &&
      expression.boundFieldIds == [1,1,1] && expression.storedTextFields == [1,1,1]) then none else pure ()
  let context := document.indexedComputationContextAt []
  let some addressed := context.addressed | none
  let current := { addressed with
    read := fun row source => if row == [(10,2)] && source == field then cell else addressed.read row source
    storedText := fun _ source => if source == field then some "bad" else none }
  let .value (.time value) true ← (expression.evalResult .computation
    { read := context.read, storedText := context.storedText } (some current)).toOption | none
  let comparisonText ← (parseText .english (comparison entry)).toOption
  let condition ← (lowerCondition model ["Form"] false comparisonText.body).toOption
  let hasNoOuterRows := match condition.core.ordinaryIterationScope with
    | .ok none => true
    | _ => false
  pure (value, hasNoOuterRows)

example : currentSelected cases[2]! 4 (checkAdmittedRawCell (.parsed (.num 6))) =
    some ({ hour := 6, minute := 4, second := 5, valid := by decide }, true) ∧
    currentSelected cases[5]! 7 (checkAdmittedRawCell (.parsed (.str "06"))) =
    some ({ hour := 6, minute := 4, second := 5, valid := by decide }, true) := by native_decide

private def excludedViews : Option Bool := do
  let parsed ← (parseText .english (comparison cases[2]!)).toOption
  let condition ← (lowerCondition model ["Form"] false parsed.body).toOption
  let document ← checked {}
  let .leaf leaf := condition.core | none
  pure (!condition.core.allLeaves ValidationConditionLeaf.supportsAddressedPartial &&
    (leaf.evalAddressedPartial? { scalar := { fields := document.flatContext, groups := GroupPresenceContext.unavailable }, outer := [], input := .checked document } .full (fun _ => true)
      (fun _ _ => .error (.checkedDocumentRequired [])) none).isNone &&
    match condition.core.referencePointers [] with
    | .error .unclassifiedOperand => true
    | _ => false)

example : excludedViews = some true := by native_decide

private def missingAddressed : Option Bool := do
  let document ← checked {}
  let parsed ← (parseText .english numberThree).toOption
  let surface ← (lowerScalarTemporalExpression model ["Form"] parsed.body).toOption
  let expression ← (elaborateScalarTemporalExpression model ["Form"] surface).toOption
  pure (match expression.evalResult .computation document.flatContext with
    | .error .calendarUnavailable => true
    | _ => false)

example : missingAddressed = some true := by native_decide

end A12Kernel.Dm.IndexedTimeComponentLocks
