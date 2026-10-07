import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.Validate

namespace A12Kernel.Dm.NestedSemanticIndexLocks

private inductive Consumer where
  | scalar | groupSum | starSum | count | first
  deriving BEq

private inductive Placement where
  | root | parent | child
  deriving BEq

private def consumers : List Consumer := [.scalar, .groupSum, .starSum, .count, .first]
private def placements : List Placement := [.parent, .child]
private def keys : List String := ["\"a\"", "/Form/RootKey", "/Form/Parents/Key"]

private def model : FlatModel :=
  let number (id : FieldId) (name : String) (path : GroupPath) (scope : List RepeatableLevel) : FlatFieldDecl :=
    { id, name, groupPath := path, repeatableScope := scope, policy := { kind := .number { scale := 0, signed := true } } }
  let text (id : FieldId) (name : String) (path : GroupPath) (scope : List RepeatableLevel) : FlatFieldDecl :=
    { id, name, groupPath := path, repeatableScope := scope, policy := { kind := .string } }
  { fields := [text 1 "RootKey" ["Form"] [], text 2 "Key" ["Form", "Parents"] [10],
      text 3 "RequestedKey" ["Form", "Parents"] [10], number 4 "Out" ["Form", "Parents"] [10],
      text 5 "Id" ["Form", "Parents", "Rows"] [10,20], number 6 "N" ["Form", "Parents", "Rows"] [10,20],
      number 7 "Out" ["Form", "Parents", "Rows"] [10,20],
      number 8 "A" ["Form", "Parents", "Rows", "Body"] [10,20],
      number 9 "B" ["Form", "Parents", "Rows", "Body"] [10,20],
      number 10 "N" ["Form", "Parents", "Rows", "Items"] [10,20,30], number 11 "Out" ["Form"] []]
    repeatableGroups := [{ level := 10, path := ["Form", "Parents"], repeatability := some 2 },
      { level := 20, path := ["Form", "Parents", "Rows"], repeatability := some 3, indexField := some 5 },
      { level := 30, path := ["Form", "Parents", "Rows", "Items"], repeatability := some 3 }] }

private structure Scenario where
  firstKey : String := "a"
  secondKey : String := "a"
  rootKey : String := "a"
  firstRequested : String := "a"
  secondRequested : String := "a"
  duplicateFirst : Bool := false
  emptySecond : Bool := false
  malformedFirst : Bool := false

private def input (scenario : Scenario) (render : Nat → String := toString) (stored : String := "99") : Lean.Json :=
  let row (id : String) (n : Nat) (bad : Bool := false) := Lean.Json.mkObj [
    ("Id", .str id), ("N", .str (if bad then "bad" else render n)), ("Out", .str stored),
    ("Body", Lean.Json.mkObj [("A", .str (if bad then "bad" else render n)), ("B", .str (render (n + 1)))]),
    ("Items", .arr #[Lean.Json.mkObj [("N", .str (if bad then "bad" else render n))],
      Lean.Json.mkObj [("N", .str (render (n + 2)))]])]
  let parent (key requested : String) (rows : Array Lean.Json) := Lean.Json.mkObj [
    ("Key", .str key), ("RequestedKey", .str requested), ("Out", .str stored), ("Rows", .arr rows)]
  Lean.Json.mkObj [("Form", Lean.Json.mkObj [("RootKey", .str scenario.rootKey), ("Out", .str stored),
    ("Parents", .arr #[parent scenario.firstKey scenario.firstRequested
      #[row "a" 2 scenario.malformedFirst, row (if scenario.duplicateFirst then "a" else "b") 3],
      parent scenario.secondKey scenario.secondRequested
        (if scenario.emptySecond then #[] else #[row "a" 7, row "b" 11])])])]

private def world : World := { now := { epochMillis := 0 } }

private def checked (scenario : Scenario := {}) : Option (CheckedDocument model) := do
  let raw ← (readDocument { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
    (input scenario)).toOption
  if !raw.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  (checkDocument prepared "en_US" raw.data).toOption

private def operation (consumer : Consumer) (key : String := "/Form/Parents/Key")
    (sourcePath : String := "/Form/Parents/Rows") : String :=
  match consumer with
  | .scalar => "[" ++ sourcePath ++ "/N For " ++ key ++ "]"
  | .groupSum => "Sum(" ++ sourcePath ++ "/Body For " ++ key ++ ")"
  | .starSum => "Sum(" ++ sourcePath ++ "/Items*/N For " ++ key ++ ")"
  | .count => "NumberOfFilledFields(" ++ sourcePath ++ "/Body For " ++ key ++ ")"
  | .first => "FirstFilledValue(" ++ sourcePath ++ "/Body For " ++ key ++ ")"

private def group : Placement → GroupPath
  | .root => ["Form"] | .parent => ["Form", "Parents"] | .child => ["Form", "Parents", "Rows"]

private def definition (placement : Placement) (expression : String) (rootDeclared : Bool := false) : DmComputation := {
  name := "Consumer", group := if rootDeclared then group .root else group placement
  targetRelPath := if rootDeclared then match placement with
    | .parent => "../Parents/Out" | .child => "../Parents/Rows/Out" | .root => "../Out"
    else "../Out"
  commonPrecondition := none
  alternatives := [{ precondition := none, operation := expression }], errorCodesToSuppress := [] }

private def admitted (placement : Placement) (expression : String) : Bool :=
  (lowerComputation model .english (definition placement expression)).isOk

private def execute (placement : Placement) (expression : String) (scenario : Scenario := {})
    (produceKey : Bool := false) (rootDeclared : Bool := false) : Option (List ComputedOutcome) := do
  let document ← checked scenario
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let consumer ← (lowerComputation model .english (definition placement expression rootDeclared)).toOption
  let producers ← if produceKey then do
    let producer ← (lowerComputation model .english {
      definition .parent "[RequestedKey]" with name := "KeyProducer", targetRelPath := "../Key" }).toOption
    pure [producer.2]
    else pure []
  let outcomes ← (runComputations world prepared document (consumer.2 :: producers)).toOption
  pure (outcomes.filter (·.pointer.endsWith "/Out"))

private def run (placement : Placement) (consumer : Consumer) (scenario : Scenario := {})
    (key : String := "/Form/Parents/Key") (produceKey : Bool := false) : Option (List ComputedOutcome) :=
  execute placement (operation consumer key) scenario produceKey

private def amounts (consumer : Consumer) (b : Bool := false) : Nat × Nat :=
  match consumer with
  | .scalar | .first => if b then (3,11) else (2,7)
  | .groupSum => if b then (7,23) else (5,15)
  | .starSum => if b then (8,24) else (6,16)
  | .count => (2,2)

private def expected (placement : Placement) (first second : String) (emptySecond : Bool := false) : List ComputedOutcome :=
  let placed (parent : String) (outcome : String) :=
    (match placement with
      | .root => ["Form/Out"]
      | .parent => [parent ++ "/Out"]
      | .child => [parent ++ "/Rows/Out", parent ++ "/Rows[2]/Out"]).map fun pointer => { pointer, outcome }
  placed "Form/Parents" first ++
    (if emptySecond && placement == .child then [] else placed "Form/Parents[2]" second)

private def values (placement : Placement) (amounts : Nat × Nat) (emptySecond : Bool := false) : List ComputedOutcome :=
  expected placement ("value " ++ toString amounts.1) ("value " ++ toString amounts.2) emptySecond

example : (checked).isSome ∧ (checked { duplicateFirst := true }).isSome ∧
    (checked { malformedFirst := true }).isSome ∧
    placements.all (fun placement => admitted placement "2" &&
      execute placement "2" == some (values placement (2,2)) &&
      execute placement "2" { firstRequested := "b", secondRequested := "b" } true ==
        some (values placement (2,2))) := by native_decide

example : placements.all (fun placement => consumers.all fun consumer => keys.all fun key =>
    admitted placement (operation consumer key) && run placement consumer {} key ==
      some (values placement (amounts consumer))) = true := by native_decide

example : consumers.all (fun consumer => keys.all fun key => !admitted .root (operation consumer key)) ∧
    placements.all (fun placement => consumers.all fun consumer =>
      !admitted placement (operation consumer "/Form/Parents/Rows/Id")) := by native_decide

example : placements.all (fun placement => consumers.all fun consumer =>
    run placement consumer { firstKey := "b" } ==
      some (values placement ((amounts consumer true).1, (amounts consumer).2)) &&
    run placement consumer { rootKey := "b" } "/Form/RootKey" == some (values placement (amounts consumer true)) &&
    run placement consumer {} "\"b\"" == some (values placement (amounts consumer true))) = true := by native_decide

example : placements.all (fun placement => consumers.all fun consumer =>
    run placement consumer { secondKey := "missing" } ==
      some (values placement ((amounts consumer).1, 0)) &&
    run placement consumer { duplicateFirst := true } ==
      some (expected placement "cleared" ("value " ++ toString (amounts consumer).2)) &&
    run placement consumer { emptySecond := true } ==
      some (values placement ((amounts consumer).1, 0) true) &&
    run placement consumer { malformedFirst := true } ==
      some (expected placement "cleared" ("value " ++ toString (amounts consumer).2))) = true := by native_decide

example : placements.all (fun placement => consumers.all fun consumer =>
    run placement consumer { firstRequested := "b", secondRequested := "b" }
      "/Form/Parents/Key" true == some (values placement (amounts consumer true)) &&
    ["\"a\"", "/Form/RootKey"].all (fun key =>
      run placement consumer { firstRequested := "b", secondRequested := "b" } key true ==
        some (values placement (amounts consumer)))) = true := by native_decide

private def validation (consumer : Consumer) (key : String) (usePartial : Bool) : Option (List Verdict) := do
  let document ← checked
  let rule ← (checkRule { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
    .english {
      name := "Nested", group := group .parent, errorEntityRelPath := "../Out", errorCode := "PROBE"
      condition := "FieldFilled(Out) And (" ++ operation consumer key ++ " == " ++ toString (amounts consumer).1 ++ ")"
      severity := "ERROR" } world).toOption
  if usePartial then
    match ← (rule.evalOrdinaryRepeatablePartial document .full (some world)).toOption with
    | .skipped => none
    | .evaluated rows => rows.mapM fun (_, result) => match result with
      | .skipped => none | .evaluated outcome => some outcome.verdict
  else
    pure ((← (rule.evalOrdinaryRepeatableFull document (some world)).toOption).map (fun (_, outcome) => outcome.verdict))

example : consumers.all (fun consumer => keys.all fun key => [false,true].all fun usePartial =>
    validation consumer key usePartial == some [.fired (if consumer == .starSum then .omission else .value), if consumer == .count then .fired .value else .notFired]) = true := by native_decide

private def twoAncestorAdmission (consumer : Consumer) : Bool :=
  let nested := { model with
    fields := model.fields.map fun field => if field.repeatableScope.isEmpty then field else
      { field with groupPath := "Form" :: "Outer" :: field.groupPath.drop 1, repeatableScope := 5 :: field.repeatableScope }
    repeatableGroups := { level := 5, path := ["Form", "Outer"], repeatability := some 2 } ::
      model.repeatableGroups.map fun group => { group with path := "Form" :: "Outer" :: group.path.drop 1 } }
  (lowerComputation nested .english {
    definition .parent (operation consumer "\"a\"" "/Form/Outer/Parents/Rows") with group := ["Form", "Outer", "Parents"] }).isOk

example : consumers.all twoAncestorAdmission = true := by native_decide

private def multipleIndexesRefused : Bool :=
  let nested := { model with repeatableGroups := model.repeatableGroups.map fun group =>
    if group.level == 10 then { group with indexField := some 2 } else group }
  match elaborateSemanticIndexSource nested (group .parent) {
      target := { base := .absolute, groups := ["Form", "Parents", "Rows"], field := "N" }
      key := .literal (.text "a") } with
  | .error .multipleIndexGroups => true | _ => false

example : multipleIndexesRefused = true := by native_decide

example : placements.all (fun placement => consumers.all fun consumer => keys.all fun key =>
    execute placement (operation consumer key) {} false true == some (values placement (amounts consumer))) = true := by native_decide

private def countSource (operands : String) : Option (CheckedFieldFillList model) := do
  let parsed ← (parseText .english ("NumberOfFilledFields(" ++ operands ++ ")")).toOption
  let .call _ arguments none none := parsed.body | none
  let surface ← (lowerEntitySource model (group .parent) arguments).toOption
  (elaborateFieldFillList model (group .parent) surface).toOption

private def partialCount (operands : String) (scope : ValidationRelevanceScope := .full)
    (scenario : Scenario := {}) (parent : Nat := 1) (unavailable : Option CellAddr := none) (faultSuffix : Bool := false) :
    Option (Except CheckedAddressingError (Option PartialValidationFilledFieldCountResult)) := do
  let source ← countSource operands
  let document ← checked scenario
  pure (source.evaluatePartialCount document [(10,parent)] scope fun environment field => do
    let address ← document.cellAddress environment field
    if unavailable == some address then return none
    if faultSuffix && field == 4 then throw (.checkedDocumentRequired ["suffix"])
    some <$> (document.fullValidationAddressedCell environment field).map (·.cell))

private def coverage (paths : List (List String)) : ValidationRelevanceScope :=
  .partialSet (paths.map fun path => { path, indices := path.map fun _ => .all })

private def countCoverage : List (List String) :=
  [["Form", "Parents", "Key"], ["Form", "Parents", "Rows", "Id"],
    ["Form", "Parents", "Rows", "Body", "A"], ["Form", "Parents", "Rows", "Body", "B"],
    ["Form", "Parents", "Out"]]

private def concreteIndexRows (withWildcardIndex : Bool) : ValidationRelevanceScope :=
  .partialSet (countCoverage.filterMap (fun path =>
    if path == ["Form", "Parents", "Rows", "Id"] && !withWildcardIndex then none
    else some { path, indices := path.map fun _ => .all }) ++
    (if withWildcardIndex then [] else [1,2].map fun row =>
      { path := ["Form", "Parents", "Rows", "Id"], indices := [.all, .concrete 1, .concrete row, .all] }))

private def countMatches
    (actual : Option (Except CheckedAddressingError (Option PartialValidationFilledFieldCountResult)))
    (expected : PartialValidationFilledFieldCountResult) : Bool :=
  match actual with
  | some (.ok (some observed)) => decide (observed = expected)
  | _ => false

private def suffixFaultMatches : Bool :=
  match partialCount "Rows/Body For Key,Out" .full {} 1 none true with
  | some (.error (.checkedDocumentRequired path)) => path == ["suffix"]
  | _ => false

example : countMatches (partialCount "Rows/Body For Key,Out") (.evaluated (.value 3)) ∧
    countMatches (partialCount "Rows/N For Key,Out") (.evaluated (.value 2)) ∧
    countMatches (partialCount "Rows/Body For Key,Out" (coverage countCoverage)) (.evaluated (.value 3)) ∧
    countMatches (partialCount "Rows/Body For Key,Out"
      (coverage (countCoverage.filter (· != ["Form", "Parents", "Rows", "Body", "B"]))) {} 1 none true) .nonRelevant ∧
    countMatches (partialCount "Rows/Body For Key,Out" (concreteIndexRows false) { firstKey := "missing" }) .nonRelevant ∧
    countMatches (partialCount "Rows/Body For Key,Out" (concreteIndexRows true) { firstKey := "missing" })
      (.evaluated (.value 1)) := by native_decide

example : [8,9].all (fun field => countMatches
    (partialCount "Rows/Body For Key,Out" .full {} 1 (some { field, path := [1,1] }) true) .silentlyUnavailable) ∧
    countMatches (partialCount "Rows/Body For Key,Out" .full {} 1 (some { field := 2, path := [1] }) true) .nonRelevant ∧
    countMatches (partialCount "Rows/Body For Key,Out" .full {} 2 (some { field := 8, path := [1,1] }))
      (.evaluated (.value 3)) ∧ suffixFaultMatches := by native_decide

private def partialAddresses (scope : ValidationRelevanceScope) : Option (Option (List CellAddr)) := do
  let source ← (elaborateKeyedEntityExtent model (group .parent) {
    target := .group { base := .absolute, groups := ["Form", "Parents", "Rows", "Body"] }
    key := .field { base := .absolute, groups := ["Form", "Parents"], field := "Key" } }).toOption
  let document ← checked
  let result ← (resolvePartialSelectedAddresses (.inr source) document scope [(10,2)]
    (fun environment field => some <$> (document.fullValidationAddressedCell environment field).map (·.cell))
    (fun field bound reopened environment => scope.coversAggregateExtent model field.path bound reopened environment)).toOption
  match result with
  | none => some none
  | some (.value (addresses, _)) => some <$> addresses.mapM (fun (field, environment) =>
      (document.cellAddress environment field.id).toOption)
  | _ => none

example : partialAddresses (coverage countCoverage) = some (some [{ field := 8, path := [2,1] }, { field := 9, path := [2,1] }]) ∧
    partialAddresses (coverage (countCoverage.filter (· != ["Form", "Parents", "Rows", "Body", "B"]))) = some none := by native_decide

private inductive Profile where
  | boolean | string | enumeration | date | time | stamp | range | fragment | custom
  deriving BEq

private def profiles : List Profile := [.boolean, .string, .enumeration, .date, .time, .stamp, .range, .fragment, .custom]

private def prototype (profile : Profile) : FlatFieldDecl :=
  let temporal (kind : TemporalKind) (components : TemporalComponents) (format : String) : FlatFieldDecl := {
    id := 0, name := "Value", groupPath := ["Form"], policy := { kind := .temporal kind components }
    temporalTargetPolicy := some { format } }
  match profile with
  | .boolean => { id := 0, name := "Value", groupPath := ["Form"], policy := { kind := .boolean } }
  | .string | .custom => {
      id := 0, name := "Value", groupPath := ["Form"], policy := { kind := .string }
      customType := if profile == .custom then some { name := "Code" } else none }
  | .enumeration => {
      id := 0, name := "Value", groupPath := ["Form"], policy := { kind := .enumeration }
      enumeration := some { storedTokens := ["alpha", "beta", "gamma", "delta", "seed"] } }
  | .date => temporal .date .fullDate "yyyy-MM-dd"
  | .time => temporal .time .time "HH:mm:ss"
  | .stamp => temporal .dateTime .now "yyyy-MM-dd'T'HH:mm:ss"
  | .fragment => temporal .date (TemporalComponents.ofFormat "MM") "MM"
  | .range => {
      id := 0, name := "Value", groupPath := ["Form"], policy := { kind := .dateRange }
      dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" } }

private def profileValues : Profile → Array String
  | .boolean => #["false", "true", "true", "false", "true"]
  | .string | .enumeration | .custom => #["alpha", "beta", "gamma", "delta", "seed"]
  | .date => #["2024-02-01", "2024-03-01", "2024-04-01", "2024-05-01", "2000-01-01"]
  | .time => #["03:04:05", "06:07:08", "09:10:11", "12:13:14", "01:01:01"]
  | .stamp => #["2024-02-01T03:04:05", "2024-03-01T06:07:08", "2024-04-01T09:10:11", "2024-05-01T12:13:14", "2000-01-01T01:01:01"]
  | .fragment => #["02", "03", "04", "05", "01"]
  | .range => #["2024-02-01/2024-02-02", "2024-03-01/2024-03-02", "2024-04-01/2024-04-02", "2024-05-01/2024-05-02", "2000-01-01/2000-01-02"]

private def profileValue (profile : Profile) (n : Nat) : String :=
  (profileValues profile)[if n == 2 then 0 else if n == 3 then 1 else if n == 7 then 2 else if n == 11 then 3 else 1]!

private def profileModel (profile : Profile) : FlatModel :=
  { model with fields := model.fields.map fun field =>
      if [4,6,7,8,9,10,11].contains field.id then
        { prototype profile with id := field.id, name := field.name, groupPath := field.groupPath, repeatableScope := field.repeatableScope }
      else field }

private def profileWorld : World := { world with
  customFieldValidator? := fun name => if name == "Code" then some (fun _ _ => none) else none }

private def profileDocument (profile : Profile) (scenario : Scenario) : Option (CheckedDocument (profileModel profile)) := do
  let m := profileModel profile
  let prepared ← (prepareFlatStringContext profileWorld builtinStringPatternCompiler m).toOption
  let raw ← (readDocument { flat := m, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
    (input scenario (profileValue profile) (profileValues profile)[4]!)).toOption
  if !raw.refusals.isEmpty then none
  (checkDocument prepared "en_US" raw.data).toOption

private def typedRun (profile : Profile) (placement : Placement) (source : String)
    (scenario : Scenario) (key : String := "/Form/Parents/Key") (produceKey : Bool := false)
    (operator : String := "FirstFilledValue") (rootDeclared : Bool := false) : Option (List ComputedOutcome) := do
  let m := profileModel profile
  let document ← profileDocument profile scenario
  let prepared ← (prepareFlatStringContext profileWorld builtinStringPatternCompiler m).toOption
  let selected := "/Form/Parents/Rows/" ++ source ++ " For " ++ key
  let expression := if operator.isEmpty then "[" ++ selected ++ "]" else operator ++ "(" ++ selected ++
    (if source == "N" && operator == "FirstFilledValue" then ",/Form/Out)" else ")")
  let step ← (lowerComputation m .english (definition placement expression rootDeclared)).toOption
  let producers ← if produceKey then do
    let producer ← (lowerComputation m .english {
      definition .parent "[RequestedKey]" with name := "KeyProducer", targetRelPath := "../Key" }).toOption
    pure [producer.2]
    else pure []
  pure ((← (runComputations profileWorld prepared document (step.2 :: producers)).toOption).filter (·.pointer.endsWith "/Out"))

private def typedExpected (profile : Profile) (placement : Placement) (numbers : Nat × Nat) : List ComputedOutcome :=
  (expected placement ("value " ++ profileValue profile numbers.1) ("value " ++ profileValue profile numbers.2)).filter
    (·.outcome != "value " ++ (profileValues profile)[4]!)

example : profiles.all (fun profile => placements.all fun placement => ["N", "Body", "Items*/N"].all fun source =>
    typedRun profile placement source { secondKey := "b" } == some (typedExpected profile placement (2,11)) &&
    typedRun profile placement source { secondKey := "b", firstRequested := "b", secondRequested := "a" }
      "/Form/Parents/Key" true == some (typedExpected profile placement (3,7)) &&
    ["\"a\"", "/Form/RootKey"].all (fun key =>
      typedRun profile placement source { secondKey := "b" } key == some (typedExpected profile placement (2,7)))) = true := by native_decide

private def profileValidation (profile : Profile) (expression : String) (scenario : Scenario := { secondKey := "b" }) :
    Option (List Verdict) := do
  let m := profileModel profile
  let document ← profileDocument profile scenario
  let rule ← (checkRule { flat := m, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
    .english {
      name := "Token", group := group .parent, errorEntityRelPath := "../Out", errorCode := "PROBE"
      condition := "FieldFilled(Out) And (" ++ expression ++ ")"
      severity := "ERROR" } profileWorld).toOption
  pure ((← (rule.evalOrdinaryRepeatableFull document (some profileWorld)).toOption).map (fun (_, outcome) => outcome.verdict))

example : profileValidation .string
    "NumberOfValueInFields(\"alpha\" In /Form/Parents/Rows/Body For /Form/Parents/Key) == 1" =
    some [.fired .value, .notFired] := by native_decide

example : profileValidation .boolean
    "NumberOfValueInFields(True In /Form/Parents/Rows/Body For /Form/Parents/Key) == 1" =
    some [.fired .value, .fired .value] := by native_decide

example : [.date, .time, .stamp].all (fun profile =>
    profileValidation profile "NumberOfDifferentValues(/Form/Parents/Rows/Body For /Form/Parents/Key) == 2" ==
      some [.fired .value, .fired .value] &&
    profileValidation profile "FieldValuesNotUnique(/Form/Parents/Rows/Body For /Form/Parents/Key)"
      { firstKey := "b", secondKey := "b" } == some [.fired .value, .notFired]) = true := by native_decide

example : [.date, .time, .stamp].all (fun profile => placements.all fun placement =>
    typedRun profile placement "Body" { secondKey := "b" } "/Form/Parents/Key" false "MinValue" ==
      some (typedExpected profile placement (2,3)) &&
    typedRun profile placement "Body" { secondKey := "b" } "/Form/Parents/Key" false "MaxValue" ==
      some (typedExpected profile placement (3,11))) = true := by native_decide

example : [.string, .date, .time, .stamp].all (fun profile => placements.all fun placement => keys.all fun key =>
    typedRun profile placement "N" {} key false "" true ==
      some (typedExpected profile placement (2,7))) = true := by native_decide

private def selectedGuards (key : String) : List String :=
  let field := "/Form/Parents/Rows/N For " ++ key
  ["FieldFilled(" ++ field ++ ")", "GroupFilled(/Form/Parents/Rows/Body For " ++ key ++ ")",
    "[" ++ field ++ "] PatternViolated \"[0-9]+\"", "Valid(" ++ field ++ ",\"Code\")",
    "[" ++ field ++ "] + \"\" == [" ++ field ++ "]"]

private def guardScope (guard : String) : Option Bool := do
  let m := profileModel .string
  let parsed ← (parseText .english guard).toOption
  let surface ← (lowerGuard m (group .parent) false parsed.body (some (group .parent))).toOption
  let .predicate surface := surface | none
  let predicate ← (m.elaborateComputationPredicate (group .parent) (group .parent) surface).toOption
  let condition ← (lowerCondition m (group .parent) false parsed.body (world := profileWorld)).toOption
  let iteration := match condition.core.ordinaryIterationScope with
    | .ok (some [10]) => true | _ => false
  pure (predicate.rowBoundBool [10] && predicate.rowBoundBool [10,20] &&
    !predicate.rowBoundBool [] && !predicate.rowBoundBool [99] && iteration)

private def guardedRootDeclaration (placement : Placement) (guard : String) : Option (List ComputedOutcome) := do
  let m := profileModel .string
  let document ← profileDocument .string {}
  let prepared ← (prepareFlatStringContext profileWorld builtinStringPatternCompiler m).toOption
  let step ← (lowerComputation m .english {
    definition placement "\"done\"" true with commonPrecondition := some guard }).toOption
  pure ((← (runComputations profileWorld prepared document [step.2]).toOption).filter (·.pointer.endsWith "/Out"))

example : keys.all (fun key => (selectedGuards key).all fun guard => guardScope guard == some true) = true := by native_decide

example : placements.all (fun placement => keys.all fun key => (selectedGuards key).all fun guard =>
    guardedRootDeclaration placement guard == some (expected placement "value done" "value done")) = true := by native_decide

private def numericIterationScope (expression : String) : Option (List RepeatableLevel) := do
  let parsed ← (parseText .english expression).toOption
  let condition ← (lowerCondition model (group .parent) false parsed.body (world := world)).toOption
  (← condition.core.ordinaryIterationScope.toOption)

example : consumers.all (fun consumer => keys.all fun key =>
    numericIterationScope (operation consumer key ++ " == 2") == some [10]) = true := by native_decide

private def product (key : String) : String :=
  "SumOfProducts(/Form/Parents/Rows/Items*/N For " ++ key ++ ",/Form/Parents/Rows/Items*/N For \"b\")"

example : placements.all (fun placement =>
    execute placement (product "/Form/Parents/Key") == some (values placement (26,194)) &&
    execute placement (product "/Form/Parents/Key") { firstKey := "b", secondKey := "b" } ==
      some (values placement (34,290))) = true := by native_decide

example : keys.all (fun key => numericIterationScope (product key ++ " == 26") == some [10]) = true := by native_decide

example : placements.all (fun placement => execute placement (product "/Form/Parents/Key") {} false true ==
    some (values placement (26,194))) = true := by native_decide

private def boundRuleAdmission (booleanProfile rootDeclared : Bool) : Bool :=
  let m := if booleanProfile then profileModel .boolean else model
  let expression := if booleanProfile then
    "NumberOfValueInFields(True In /Form/Parents/Rows/Body For /Form/Parents/Key) == 1"
    else product "/Form/Parents/Key" ++ " == 26"
  (checkRule { flat := m, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
    .english {
      name := "Bound", group := group (if rootDeclared then .root else .parent)
      errorEntityRelPath := if rootDeclared then "../Parents/Out" else "../Out"
      errorCode := "PROBE", condition := "FieldFilled(/Form/Parents/Out) And (" ++ expression ++ ")"
      severity := "ERROR" } profileWorld).isOk

example : [false,true].all (fun booleanProfile => [false,true].all (boundRuleAdmission booleanProfile)) = true := by native_decide

private def stringAdmission : Option (Bool × Bool) := do
  let selected ← (elaborateIndexedStringNumericSource model (group .parent) {
    target := { base := .absolute, groups := ["Form", "Parents", "Rows"], field := "Id" }
    key := .literal (.text "a") } .length).toOption
  let atom : OrderedNumericValidationAtom model := .indexedString selected
  pure (atom.admitted (group .parent) .sameGroupAddressed, atom.admitted (group .root) .sameGroupAddressed)

private def temporalAdmission : Option (Bool × Bool) := do
  let selected ← (elaborateTemporalNumericExpression (profileModel .date) (group .parent)
    (.indexed {
      target := { base := .absolute, groups := ["Form", "Parents", "Rows"], field := "N" }
      key := .literal (.text "a") }) (.date .year)).toOption
  let atom : OrderedNumericValidationAtom (profileModel .date) := .temporalPart selected
  pure (atom.admitted (group .parent) .sameGroupAddressed, atom.admitted (group .root) .sameGroupAddressed)

private def numericReuse (expression : String) : Option (Bool × Bool) := do
  let parsed ← (parseText .english expression).toOption
  let condition ← (lowerCondition model (group .parent) false parsed.body (world := world)).toOption
  let .leaf leaf := condition.core | none
  pure (leaf.wellFormedBool (group .parent), leaf.wellFormedBool (group .root))

example : stringAdmission = some (true,false) ∧ temporalAdmission = some (true,false) ∧
    numericReuse (operation .groupSum "\"a\"" ++ " == 5") = some (true,false) ∧
    numericReuse (product "\"a\"" ++ " == 26") = some (true,false) := by native_decide

private def numericIndexModel : FlatModel :=
  { model with fields := model.fields.map fun field => if [1,2,3,5].contains field.id then
      { field with policy := { kind := .number { scale := 0, signed := true } } } else field }

private def oneLevelNumericModel : FlatModel :=
  { fields := numericIndexModel.fields.filterMap fun field =>
      if [1,2,5,6].contains field.id then some (if field.id == 5 || field.id == 6 then
        { field with groupPath := ["Form", "Rows"], repeatableScope := [20] } else field) else none
    repeatableGroups := [{ level := 10, path := ["Form", "Parents"], repeatability := some 2 },
      { level := 20, path := ["Form", "Rows"], repeatability := some 3, indexField := some 5 }] }

private def reducedSource (nested : Bool) (key : SurfaceSemanticIndexKey) : SurfaceSemanticIndex := {
  target := { base := .absolute, groups := if nested then ["Form", "Parents", "Rows"] else ["Form", "Rows"], field := "N" }, key }

private def reducedRefused (nested : Bool) (key : SurfaceSemanticIndexKey) : Bool :=
  match elaborateNumberSemanticIndexSource (if nested then numericIndexModel else oneLevelNumericModel)
      (group .parent) (reducedSource nested key) with
  | .error .reducedRouteNeedsSingleGroup => true | _ => false

private def reducedRead (fieldKey : Bool) : Option CellObservation := do
  let source ← (elaborateNumberSemanticIndexSource oneLevelNumericModel (group .root)
    (reducedSource false (if fieldKey then .field { base := .absolute, groups := ["Form"], field := "RootKey" }
      else .literal (.number 1)))).toOption
  (source.lookupValue { candidates := [1,2], read := fun row field =>
      if field == 5 then .parsed (.num row) else if field == 6 then .parsed (.num (row + 1)) else .empty }
    { read := fun field => if field == 1 then .parsed (.num 1) else .empty } .validation).toOption

example : reducedRefused true (.literal (.number 1)) ∧
    reducedRefused false (.field { base := .absolute, groups := ["Form", "Parents"], field := "Key" }) ∧
    reducedRead false = some (.value (.num 2)) ∧ reducedRead true = some (.value (.num 2)) := by native_decide

end A12Kernel.Dm.NestedSemanticIndexLocks
