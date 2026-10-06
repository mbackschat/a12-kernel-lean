import A12Kernel.Reference.Dm.Replay
import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.Compute
import A12Kernel.Elaboration.GeneratedComputationValidation

namespace A12Kernel.Dm.ConstructedDateValidityLocks

open A12Kernel A12Kernel.Dm Lean

private def number (id : FieldId) (name : String) (maximum : Rat) : FlatFieldDecl := {
  id, name, groupPath := ["Form"]
  policy := { kind := .number { scale := 0, signed := false } }
  numericTargetConstraints := { maximum := some maximum } }

private def model : FlatModel := {
  timeZoneId := "UTC", baseYear := some 2024
  fields := [number 1 "D" 31, number 2 "M" 12, number 3 "Y" 9999,
    number 4 "C" 99, number 5 "S" 99,
    { id := 6, name := "E", groupPath := ["Form", "Rows"], repeatableScope := [10]
      policy := { kind := .string } },
    { id := 7, name := "TextDay", groupPath := ["Form"], policy := { kind := .string }
      stringPolicy := { maxLength := some 2 }, stringPatternSource := some "[0-9]+" },
    { id := 8, name := "Year", groupPath := ["Form"]
      policy := { kind := .temporal .date (TemporalComponents.ofFormat "yyyy") }
      temporalTargetPolicy := some { format := "yyyy" } },
    { id := 9, name := "Stamp", groupPath := ["Form"]
      policy := { kind := .temporal .date TemporalComponents.fullDate }
      temporalTargetPolicy := some { format := "yyyy-MM-dd" } }]
  repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 2 }] }

private def admitted (text : String) : Bool :=
  ((parseText .english text).toOption.bind fun parsed =>
    (lowerCondition model ["Form"] false parsed.body).toOption).isSome

example : ["Valid(Date(D, M, Y))", "Invalid(Date(D, M))",
    "Valid(Date(D, M, C, S))", "Invalid(Date(D, \"02\", \"2024\"))",
    "Valid(Date(D, MonthFromDate(Today), YearFromDate(Now)))",
    "Valid(Date(TextDay, M, Year))",
    "Valid(Date(D, MonthFromDate(BaseYear), YearFromDate(EndOfDateRange(BaseYear))))"].all admitted := by native_decide

example : ["Valid(Date(D))", "Valid(Date(D, M, Y, C, S))",
    "Valid(Date(D, M, 2024))", "Valid(Date(D, M, \"24\"))",
    "Valid(Date(D, M, MonthFromDate(Today)))", "Valid(Date(Rows*/E, M, Y))"].all
    (fun text => !admitted text) := by native_decide

private def dm : DmModel := {
  flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }

private def checkedDocument (values : List (String × String)) (rows : Bool := false)
    (fixture : FlatModel := model) : Option (CheckedDocument fixture) := do
  let model := fixture
  let dm := { dm with flat := model }
  let row := Json.mkObj [("E", "present")]
  let members := (values.map fun (key, value) => (key, Json.str value)) ++
    (if rows then [("Rows", Json.arr #[row, row])] else [])
  let input ← (readDocument dm (Json.mkObj [("Form", Json.mkObj members)])).toOption
  if !input.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption
  (checkDocument prepared "en_US" input.data).toOption

private def runWorlds (text : String) (values : List (String × String))
    (errorPath : String) (times : List Int) (rows : Bool := false)
    (fixture : FlatModel := model) : Option (List (List (String × String))) := do
  let model := fixture
  let dm := { dm with flat := model }
  let rule : DmRule := {
    group := ["Form"], name := "Rule", errorCode := "R"
    errorEntityRelPath := errorPath, condition := text, severity := "ERROR" }
  let document ← checkedDocument values rows fixture
  let checked ← (checkRule dm .english rule { now := { epochMillis := 0 } }).toOption
  times.mapM fun now => do
    let messages ← (runRule { now := { epochMillis := now } } document checked).toOption
    pure (messages.map fun message =>
      let observed := observe model message
      (observed.pointer, observed.messageType))

private def run (text : String) (values : List (String × String))
    (errorPath : String := "../D") : Option (List (String × String)) :=
  (runWorlds text values errorPath [0]).bind List.head?

example : run "Valid(Date(D, M, Y))" [("D", "29"), ("M", "2"), ("Y", "2024")] =
    some [("Form/D", "VALUE_ERROR")] ∧
    run "Invalid(Date(D, M, Y))" [("D", "29"), ("M", "2"), ("Y", "2023")] =
      some [("Form/D", "VALUE_ERROR")] ∧
    run "Invalid(Date(D, M, Y))" [] = some [("Form/D", "OMISSION_ERROR")] ∧
    run "Valid(Date(D, M, Y))" [] = some [] ∧
    run "Invalid(Date(D, M, Y))" [("Y", "bad")] = some [] := by native_decide

example : run "Invalid(Date(D, M)) Or FieldFilled(Y)" [("D", "29"), ("M", "2")] = some [] ∧
    run "Valid(Date(D, M, C, S)) And FieldFilled(Y)"
      [("D", "29"), ("M", "2"), ("C", "20"), ("S", "0"), ("Y", "2000")] =
      some [("Form/D", "VALUE_ERROR")] := by native_decide

-- One checked rule is reused: January versus February makes day 30 distinguish runtime clocks.
example : runWorlds "Valid(Date(D, MonthFromDate(Now), YearFromDate(Now)))"
    [("D", "30")] "../D" [0, 951782400000] = some [[("Form/D", "VALUE_ERROR")], []] ∧
    runWorlds "Valid(Date(D, MonthFromDate(Now), YearFromDate(Now))) And AtLeastOneFieldFilled(Rows*)"
      [("D", "30")] "../Rows/E" [0, 951782400000] true =
      some [[("Form/Rows/E", "VALUE_ERROR")], []] ∧
    runWorlds "FieldFilled(Rows/E) And Valid(Date(D, MonthFromDate(Now), YearFromDate(Now)))"
      [("D", "30")] "../Rows/E" [0, 951782400000] true =
      some [[("Form/Rows/E", "VALUE_ERROR"), ("Form/Rows[2]/E", "VALUE_ERROR")], []] := by native_decide

example : run "Valid(Date(TextDay, M, Year))"
    [("TextDay", "29"), ("M", "2"), ("Year", "2024")] "../TextDay" =
      some [("Form/TextDay", "VALUE_ERROR")] ∧
    run "Valid(Date(D, MonthFromDate(Stamp), YearFromDate(Stamp)))"
      [("D", "29"), ("Stamp", "2024-02-29")] "../Stamp" = some [("Form/Stamp", "VALUE_ERROR")] := by native_decide

private def references : Option (List FieldId × Bool) := do
  let expression ← (parseText .english "Invalid(Date(D, M, C, S))").toOption
  let condition ← (lowerCondition model ["Form"] false expression.body).toOption
  let pointers ← (condition.core.referencePointers []).toOption
  pure (pointers.map (·.field), condition.core.allLeaves ValidationConditionLeaf.supportsAddressedPartial)

example : references = some ([1, 2, 4, 5], true) := by native_decide

private def leafResult (text : String) (values : List (String × String)) :
    Option (Except CheckedAddressingError Verdict) := do
  let document ← checkedDocument values
  let expression ← (parseText .english text).toOption
  let condition ← (lowerCondition model ["Form"] false expression.body).toOption
  let .leaf leaf := condition.core | none
  pure (leaf.evalAddressed {
    scalar := { fields := document.flatContext, groups := GroupPresenceContext.unavailable }
    outer := [], input := .checked document })

example : [leafResult "Valid(Date(D, M, Y))" [("D", "29"), ("M", "2"), ("Y", "bad")],
    leafResult "Invalid(Date(D, M, Y))" [("D", "29"), ("M", "2"), ("Y", "bad")]].all
      (fun | some (.ok .unknown) => true | _ => false) = true ∧
    (match leafResult "Valid(Date(D, MonthFromDate(Now), YearFromDate(Now)))" [("D", "30")] with
      | some (.error (.constructedDate .nowWorldRequired)) => true | _ => false) = true := by native_decide

private def computationModel (repeated : Bool) : FlatModel :=
  let target (id : FieldId) (name : String) := {
    (number id name 9999) with
    policy := { kind := .number { scale := 0, signed := true } }
    numericTargetConstraints := { minimum := some 0, maximum := some 9999 } }
  { model with fields := (model.fields ++ [target 10 "Out", target 11 "After"]).map fun field =>
      if repeated && field.id != 6 then
        { field with groupPath := ["Form", "Rows"], repeatableScope := [10] }
      else field }

private def compute (guard : String) (rows : List (List (String × String)))
    (repeated fresh : Bool := false) (now : Int := 0) (stringTarget : Bool := false)
    (extensible : Bool := false) : Option (List String) := do
  let model := computationModel repeated
  let model := if extensible then { model with fields := model.fields.map fun field =>
    if field.id == 7 then { field with stringExtensibleEnum := true, stringPatternSource := none } else field } else model
  let model := if stringTarget then { model with fields := model.fields.map fun field =>
    if field.id == 10 then { field with policy := { kind := .string }, numericTargetConstraints := {} } else field } else model
  let raw := fun values => Json.mkObj ((values ++ [("Out", "9"), ("After", "9")]).map
    fun (key, value) => (key, Json.str value))
  let data := if repeated then Json.mkObj [("Rows", .arr (rows.map raw).toArray)]
    else raw (rows.headD [])
  let input ← (readDocument {
    flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
    (Json.mkObj [("Form", data)])).toOption
  if !input.refusals.isEmpty then none
  let world : World := { now := { epochMillis := now } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let path := if repeated then "Rows/" else ""
  let definition (name target operation : String) (guard : Option String := none) : DmComputation := {
    group := ["Form"], name, targetRelPath := "../" ++ path ++ target
    commonPrecondition := guard, alternatives := [{ precondition := none, operation }]
    errorCodesToSuppress := [] }
  let definitions := [definition "Guard" "Out" (if stringTarget then "\"yes\"" else "1") (some guard),
    definition "Dependent" "After" (if stringTarget then s!"Length({path}Out)" else s!"[{path}Out] + 1")] ++
      if fresh then [definition "Producer" "D" "29"] else []
  let steps ← definitions.mapM fun definition =>
    (lowerComputation model .english definition).toOption.map (·.2)
  pure ((← (runComputations world prepared checked steps).toOption).map (·.outcome))

example : [false, true].all (fun repeated =>
    let path := if repeated then "Rows/" else ""
    ["Valid", "Invalid"].all fun operation =>
      let guard := s!"{operation}(Date({path}D, {path}M, {path}Y))"
      let valid := operation == "Valid"
      compute guard [[("D", "29"), ("M", "2"), ("Y", "2024")]] repeated ==
        some (if valid then ["value 1", "value 2"] else ["cleared", "value 1"]) &&
      compute guard [[("D", "29"), ("M", "2"), ("Y", "2023")]] repeated ==
        some (if valid then ["cleared", "value 1"] else ["value 1", "value 2"]) &&
      compute guard [[]] repeated ==
        some (if valid then ["cleared", "value 1"] else ["value 1", "value 2"]) &&
      compute guard [[("D", "29"), ("M", "2"), ("Y", "bad")]] repeated ==
        some ["cleared", "cleared"] &&
      compute guard [[("D", "bad"), ("M", "2"), ("Y", "2024")]] repeated true ==
        some (if valid then ["value 29", "value 1", "value 2"] else
          ["value 29", "cleared", "value 1"])) := by native_decide

example : compute "Valid(Date(Rows/D, Rows/M, Rows/Y))"
    [[("D", "29"), ("M", "2"), ("Y", "2024")], [("D", "29"), ("M", "2"), ("Y", "2023")]] true =
      some ["value 1", "cleared", "value 2", "value 1"] ∧
    compute "Valid(Date(TextDay, M, Year))" [[("TextDay", "29"), ("M", "2"), ("Year", "2024")]] =
      some ["value 1", "value 2"] ∧
    compute "Invalid(Date(D, M))" [[("D", "29"), ("M", "2")]] = some ["cleared", "value 1"] ∧
    compute "Valid(Date(D, M, C, S))" [[("D", "29"), ("M", "2"), ("C", "20"), ("S", "0")]] =
      some ["value 1", "value 2"] := by native_decide

example : compute "Valid(Date(D, MonthFromDate(Now), YearFromDate(Now)))" [[("D", "30")]] =
    some ["value 1", "value 2"] ∧
    compute "Valid(Date(D, MonthFromDate(Now), YearFromDate(Now)))" [[("D", "30")]] false false 951782400000 =
      some ["cleared", "value 1"] ∧
    compute "FieldNotFilled(D) Or Invalid(Date(D, M, Y))" [[("Y", "bad")]] =
      some ["value 1", "value 2"] ∧
    compute "FieldFilled(D) And Valid(Date(D, M, Y))" [[("Y", "bad")]] =
      some ["cleared", "value 1"] := by native_decide

example : compute "Valid(Date(D, M, Y))" [[("D", "29"), ("M", "2"), ("Y", "1500")]] =
    some ["value 1", "value 2"] ∧
    compute "Invalid(Date(D, M, Y))" [[("D", "10"), ("M", "10"), ("Y", "1582")]] =
      some ["value 1", "value 2"] := by native_decide

example : [false, true].all (fun repeated =>
    let path := if repeated then "Rows/" else ""
    let guard := s!"Valid(Date({path}D, {path}M, {path}Y))"
    compute guard [[("D", "29"), ("M", "2"), ("Y", "2024")]] repeated false 0 true ==
      some ["value yes", "value 3"] &&
    compute guard [[("D", "29"), ("M", "2"), ("Y", "bad")]] repeated false 0 true ==
      some ["cleared", "cleared"]) := by native_decide

example : compute "Valid(Date(D, MonthFromDate(Stamp), YearFromDate(Stamp)))"
    [[("D", "29"), ("Stamp", "2024-02-29")]] = some ["value 1", "value 2"] ∧
    compute "Valid(Date(D, MonthFromDate(BaseYear), YearFromDate(EndOfDateRange(BaseYear))))"
      [[("D", "1")]] = some ["value 1", "value 2"] := by native_decide

private def guardAdmitted (guard : String) (repeated : Bool := false) : Bool :=
  let model := computationModel repeated
  let model := if repeated then { model with fields := model.fields ++ [number 12 "Out" 9999, number 13 "Root" 99] } else model
  (lowerComputation model .english {
    group := ["Form"], name := "Guarded", targetRelPath := "../Out"
    commonPrecondition := some guard, alternatives := [{ precondition := none, operation := "1" }]
    errorCodesToSuppress := [] }).isOk

example : ["Valid(Date(\"1\", \"2\", \"2024\"))", "Invalid(Date(D))",
    "Valid(Date(D, M, 2024))", "Valid(Date(D, M, \"24\"))", "Valid(Date(D, M, Out))"].all
      (fun guard => !guardAdmitted guard) ∧
    guardAdmitted "Valid(Date(D, M, After))" ∧
    guardAdmitted "FieldNotFilled(Root)" true ∧
    !guardAdmitted "Valid(Date(Rows/D, Rows/M, Rows/Y))" true := by native_decide

private def guardScopes : Option (List Bool) := do
  let model := computationModel true
  let parsed ← (parseText .english "Valid(Date(Rows/D, Rows/M, Rows/Y))").toOption
  let surface ← (lowerGuard model ["Form"] false parsed.body (some ["Form", "Rows"])).toOption
  let guard ← (model.elaborateCheckedComputationCondition ["Form"] ["Form", "Rows"] surface).toOption
  let .leaf (.predicate predicate) := guard | none
  pure ([[], [10], [10, 20], [20]].map predicate.rowBoundBool)

example : guardScopes = some [false, true, true, false] := by native_decide

private def generatedScope (repeated : Bool) (name : String) : Option (Bool × Bool) := do
  let model := computationModel repeated
  let model := { model with fields := model.fields ++ [number 12 "Fixed" 9999] }
  let path := if repeated then "Rows/" else ""
  let binding := if repeated then ["Form", "Rows"] else ["Form"]
  let parsed ← (parseText .english s!"{name}(Date({path}D, {path}M, {path}Y))").toOption
  let surface ← (lowerGuard model ["Form"] false parsed.body (some binding)).toOption
  let guard ← (model.elaborateCheckedComputationCondition ["Form"] binding surface).toOption
  let .leaf (.predicate predicate) := guard | none
  let operation ← (elaborateCompleteNumericComputationOperation model ["Form"] 12
    (.literal { value := 1, authoredScale := 0 }) false).toOption
  let table : GeneratedComputationTable (CheckedNumericComputationOperation model) (CheckedComputationCondition model) := {
    targetField := 12, name := "Computed", commonPrecondition := some guard
    alternatives := .singleton { operation }, messagePlan := { parts := [.text "date result"] } }
  pure (predicate.rowBoundBool [], (assembleGeneratedNumericOperationTableRule model table).isOk)

example : ["Valid", "Invalid"].all (fun name =>
    generatedScope false name == some (true, true) &&
    generatedScope true name == some (false, false)) := by native_decide

private def generatedPhases (operation : String) : Option (Bool × Bool) := do
  let model := computationModel false
  let path := ""
  let targetGroup := ["Form"]
  let parsed ← (parseText .english s!"{operation}(Date({path}D, {path}M, {path}Y)) Or FieldFilled({path}M)").toOption
  let surface ← (lowerGuard model ["Form"] false parsed.body (some targetGroup)).toOption
  let guard ← (model.elaborateCheckedComputationCondition ["Form"] targetGroup surface).toOption
  let operation ← (elaborateCompleteNumericComputationOperation model ["Form"] 10
    (.literal { value := 1, authoredScale := 0 }) false).toOption
  let table : GeneratedComputationTable (CheckedNumericComputationOperation model) (CheckedComputationCondition model) := {
    targetField := 10, name := "Computed", commonPrecondition := some guard
    alternatives := .singleton { operation }, messagePlan := { parts := [.text "date result"] } }
  let row := Json.mkObj [("D", "29"), ("M", "2"), ("Y", "bad"), ("Out", "9")]
  let data := row
  let input ← (readDocument {
      flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
    (Json.mkObj [("Form", data)])).toOption
  if !input.refusals.isEmpty then none
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  let row : Env := []
  let computed ← (guard.evalChecked ((document.computationContextAt row).withWorld world)).toOption
  let rule ← (assembleGeneratedNumericOperationTableRule model table).toOption
  let validated ← (rule.evalAddressedFull {
    scalar := { fields := document.flatContext.withWorld world, groups := GroupPresenceContext.unavailable }
    outer := row, input := .checked document } true).toOption
  pure (match computed with | .poison _ => true | _ => false,
    match validated with | .fired _ => true | _ => false)

example : ["Valid", "Invalid"].all (fun operation =>
    generatedPhases operation == some (true, true)) := by native_decide

private def extensibleFixture : FlatModel := { model with fields := model.fields.map fun field =>
  if field.id == 7 then { field with stringExtensibleEnum := true, stringPatternSource := none } else field }

example : runWorlds "Valid(Date(TextDay,M,Y)) And FieldFilled(D)"
    [("TextDay", "x"), ("M", "2"), ("Y", "2024")] "../TextDay" [0] false extensibleFixture =
      some [[("Form/TextDay", "VALUE_ERROR")]] := by native_decide

example : runWorlds "Invalid(Date(TextDay,M,Y)) Or FieldFilled(D)"
    [("TextDay", "?"), ("M", "2"), ("Y", "2024")] "../TextDay" [0] false extensibleFixture =
      some [[("Form/TextDay", "VALUE_ERROR")]] ∧
    runWorlds "FieldFilled(D) And Valid(Date(TextDay,M,Y))"
    [("TextDay", "x"), ("M", "2"), ("Y", "2024")] "../TextDay" [0] false extensibleFixture =
      some [[]] := by native_decide

example : [false, true].all (fun repeated =>
    let path := if repeated then "Rows/" else ""
    ["Valid", "Invalid"].all fun operation =>
      compute s!"{operation}(Date({path}TextDay,{path}M,{path}Y))"
        [[("TextDay", "x"), ("M", "2"), ("Y", "2024")]] repeated false 0 false true ==
        some ["cleared", "cleared"]) := by native_decide

private def rowValidityOutcomes (operation : String) (scope : Option ValidationRelevanceScope := none)
    (values : List (String × String) := [("29", "2024"), ("29", "2023")])
    (extensible : Bool := false) (condition : Option String := none)
    (world : Option World := none) (stringYear : Bool := false) :
    Option (List (Env × FlatRuleOutcome)) := do
  let model := computationModel true
  let model := { model with
    repeatableGroups := model.repeatableGroups.map fun group => { group with repeatability := some (max 1 values.length) }
    fields := model.fields.map fun field =>
      if stringYear && field.id == 3 then
        { field with
          policy := { kind := .string }, numericTargetConstraints := {}
          stringExtensibleEnum := true, stringPolicy := { maxLength := some 4 } }
      else if extensible && field.id == 7 then
        { field with stringExtensibleEnum := true, stringPatternSource := none } else field }
  let dm := { dm with flat := model }
  let day := if extensible then "TextDay" else "D"
  let raw (value : String × String) := Json.mkObj [(day, Json.str value.1), ("M", "2"), ("Y", Json.str value.2),
    ("Year", Json.str value.2), ("C", "20"), ("S", "24")]
  let input ← (readDocument dm (Json.mkObj [("Form", Json.mkObj [
    ("Rows", .arr (values.map raw).toArray)])])).toOption
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  let expression := s!"{operation}(Date(Rows/{day}, Rows/M, Rows/Y))"
  let expression := if operation == "Invalid" then s!"FieldFilled(Rows/{day}) And {expression}" else expression
  let rule ← (checkRule dm .english {
    group := ["Form"], name := "Rule", errorCode := "R", errorEntityRelPath := s!"../Rows/{day}"
    condition := condition.getD expression, severity := "ERROR" }).toOption
  match scope with
  | none => (rule.evalOrdinaryRepeatableFull document world).toOption
  | some scope =>
      match ← (rule.evalOrdinaryRepeatablePartial document scope world).toOption with
      | .skipped => none
      | .evaluated rows => rows.mapM fun (environment, outcome) => match outcome with
          | .skipped => none
          | .evaluated result => some (environment, result)

private def rowValidity (operation : String) (scope : Option ValidationRelevanceScope := none) :
    Option (List Verdict) := (rowValidityOutcomes operation scope).map fun rows => rows.map (·.2.verdict)

example : rowValidity "Valid" = some [.fired .value, .notFired] ∧
    rowValidity "Invalid" = some [.notFired, .fired .value] ∧
    rowValidity "Valid" (some .full) = some [.fired .value, .notFired] ∧
    rowValidity "Invalid" (some .full) = some [.notFired, .fired .value] := by native_decide

example : rowValidity "Valid" (some (.partialSet [
    { path := ["Form", "Rows", "D"], indices := [.all, .all, .all] }])) =
      some [.unknown, .unknown] := by native_decide

example : (rowValidityOutcomes "Valid" (some .full) [("2", "2024"), ("x", "2024")] true
    (some "Valid(Date(Rows/TextDay,Rows/M,Rows/Y)) And FieldNotFilled(Rows/M)")) =
    (rowValidityOutcomes "Valid" none [("2", "2024"), ("x", "2024")] true
    (some "Valid(Date(Rows/TextDay,Rows/M,Rows/Y)) And FieldNotFilled(Rows/M)")) := by native_decide

private def rowOutcomes (result : Option (List (Env × FlatRuleOutcome))) :
    Option (List (Env × Verdict × Option CellAddr)) := result.map fun rows => rows.map fun (row, outcome) =>
      (row, outcome.verdict, outcome.message?.bind (·.errorAddress.toCellAddr?))

example : [none, some ValidationRelevanceScope.full].all (fun scope =>
    rowOutcomes (rowValidityOutcomes "Valid" scope [("2", "2024"), ("x", "2024"), ("1", "2024")] true
      (some "Valid(Date(Rows/TextDay,Rows/M,Rows/Y)) And FieldNotFilled(Rows/M)")) == some [
        ([(10, 1)], .notFired, none),
        ([(10, 2)], .fired .value, some { field := 7, path := [1] })]) := by native_decide

example : [none, some ValidationRelevanceScope.full].all (fun scope =>
    rowOutcomes (rowValidityOutcomes "Valid" scope [("x", "2024"), ("x", "2024")] true
      (some "FieldNotFilled(Rows/M) And Valid(Date(Rows/TextDay,Rows/M,Rows/Y))")) == some [
        ([(10, 1)], .notFired, none), ([(10, 2)], .notFired, none)]) := by native_decide

example : ["Date(Rows/D,Rows/M)", "Date(Rows/D,Rows/M,Rows/C,Rows/S)"].all (fun constructor =>
    (rowValidityOutcomes "Valid" (some .full) [("29", "2024"), ("28", "2024")] false
      (some s!"Valid({constructor})")).map (fun rows => rows.map (·.2.verdict)) ==
        some [.fired .value, .fired .value]) ∧
    (rowValidityOutcomes "Valid" (some .full) [("29", "2024"), ("29", "2023")] false
      (some "Valid(Date(Rows/D,Rows/M,Rows/Year))")).map (fun rows => rows.map (·.2.verdict)) ==
        some [.fired .value, .notFired] := by native_decide

example : (rowValidityOutcomes "Valid" (some .full) [("", "2024"), ("bad", "2024")] false
    (some "FieldFilled(Rows/M) And Invalid(Date(Rows/D,Rows/M,Rows/Y))")).map
      (fun rows => rows.map (·.2.verdict)) = some [.fired .omission, .unknown] := by native_decide

example : [0, 951782400000].map (fun now =>
    (rowValidityOutcomes "Valid" (some .full) [("30", "2024")] false
      (some "FieldFilled(Rows/D) And Valid(Date(Rows/D,MonthFromDate(Now),YearFromDate(Now)))")
      (some { now := { epochMillis := now } })).map (fun rows => rows.map (·.2.verdict))) =
      [some [.fired .value], some [.notFired]] := by native_decide

example : rowOutcomes (rowValidityOutcomes "Valid" (some (.partialSet [
    { path := ["Form", "Rows", "D"], indices := [.all, .all, .all] },
    { path := ["Form", "Rows", "Y"], indices := [.all, .all, .all] }]))
    [("29", "x")] false none none true) = some [
      ([(10, 1)], .fired .value, some { field := 1, path := [1] })] ∧
    (rowValidityOutcomes "Valid" (some (.partialSet [
      { path := ["Form", "Rows", "D"], indices := [.all, .all, .all] }]))
      [("29", "x")] false none none true).map (fun rows => rows.map (·.2.verdict)) =
        some [.unknown] := by native_decide

example :
    let model := computationModel true
    let source : SurfaceConstructedDateComponents SurfaceScalarDateComponent := {
      day := .inl (.inl (.numberField 1)), month := .inl (.inl (.numberField 2)), year := .complete (.inl (.inl (.numberField 3))) }
    (CheckedValidationCondition.fromConstructedDateValidity model ["Form"] .valid source ["Form", "Rows"]).isOk = true ∧
    (CheckedValidationCondition.fromConstructedDateValidity model ["Form", "Side"] .valid source ["Form", "Rows"]).isOk = false := by native_decide

example : [none, some ValidationRelevanceScope.full].all (fun scope =>
    rowOutcomes (rowValidityOutcomes "Valid" scope [("x", "2024"), ("1", "2024")] true
      (some "FieldFilled(Rows/M) Or Valid(Date(Rows/TextDay,Rows/M,Rows/Y))")) == some [
        ([(10, 1)], .fired .value, some { field := 7, path := [1] })]) := by native_decide

private def fixedPartialValidity (once : Bool) (times : List Int)
    (scope : ValidationRelevanceScope := .full)
    (expression : String := "Valid(Date(D,MonthFromDate(Now),YearFromDate(Now)))") :
    Option (List (Verdict × Option CellAddr)) := do
  let document ← checkedDocument [("D", "30"), ("M", "2"), ("Y", "2024")] true
  let rule ← (checkRule dm .english {
    group := ["Form"], name := "Rule", errorCode := "R", severity := "ERROR"
    errorEntityRelPath := if once then "../Rows/E" else "../D"
    condition := if once then expression ++ " And AtLeastOneGroupFilled(Rows*)" else expression }).toOption
  times.mapM fun now => do
    let world := some { now := { epochMillis := now } }
    let outcome ← if once then do
      match ← (rule.evalOrdinaryOncePartial document scope world).toOption with
      | .skipped => none
      | .evaluated _ outcome => pure outcome
    else do
      match ← (rule.evalAddressedPartial document scope world).toOption with
      | .skipped => none
      | .evaluated outcome => pure outcome
    pure (outcome.verdict, outcome.message?.bind (·.errorAddress.toCellAddr?))

example : fixedPartialValidity false [0, 951782400000] = some [
    (.fired .value, some { field := 1, path := [] }), (.notFired, none)] ∧
    fixedPartialValidity true [0, 951782400000] = some [
    (.fired .value, some { field := 6, path := [1] }), (.notFired, none)] := by native_decide

example : fixedPartialValidity false [0]
    (.partialSet [{ path := ["Form", "D"], indices := [.all, .all] }])
    "Valid(Date(D,M,Y))" = some [(.unknown, none)] := by native_decide

end A12Kernel.Dm.ConstructedDateValidityLocks
