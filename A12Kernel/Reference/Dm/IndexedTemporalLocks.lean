import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.LowerValidation
import A12Kernel.Elaboration.GeneratedComputationValidation.Assembly
import A12Kernel.Elaboration.ScalarComputationRun

namespace A12Kernel.Dm.IndexedTemporalLocks

private def model (kind : TemporalKind) (components : TemporalComponents) (format : String) : FlatModel :=
  let temporal (id : FieldId) (name : String) (path : GroupPath := ["Form"])
      (scope : List RepeatableLevel := []) : FlatFieldDecl := {
    id, name, groupPath := path, repeatableScope := scope
    policy := { kind := .temporal kind components }, temporalTargetPolicy := some { format } }
  { fields := [temporal 1 "Out", temporal 2 "Low", temporal 3 "High",
      { id := 4, name := "Key", groupPath := ["Form"], policy := { kind := .string } },
      { id := 5, name := "Code", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .string } },
      temporal 6 "A" ["Form", "Rows", "Body"] [10], temporal 7 "B" ["Form", "Rows", "Body"] [10],
      temporal 8 "Value" ["Form", "Rows", "Children"] [10,20],
      { id := 9, name := "Flag", groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := true } } }]
    repeatableGroups := [
      { level := 10, path := ["Form", "Rows"], repeatability := some 3, indexField := some 5 },
      { level := 20, path := ["Form", "Rows", "Children"], repeatability := some 3 }] }

private structure Scenario where
  key : String := "R1"
  firstA : Option String := none
  secondCode : String := "R2"
  children : Option (List String) := none
  producer : Option (String × String) := none
  baseYear : Option Int := none
  fullDateTarget : Bool := false
  temporalGuard : Bool := false
  scalarPlan : Bool := false
  secondFormat : Option String := none

private def input (low high : String) (scenario : Scenario) : Lean.Json :=
  let row (key a b : String) (children : List String) := Lean.Json.mkObj [
    ("Code", .str key), ("Body", Lean.Json.mkObj [("A", .str a), ("B", .str b)]),
    ("Children", .arr (children.map fun value => Lean.Json.mkObj [("Value", .str value)]).toArray)]
  Lean.Json.mkObj [("Form", Lean.Json.mkObj [
    ("Out", .str "bad"), ("Flag", .str "99"), ("Low", .str low), ("High", .str high), ("Key", .str scenario.key),
    ("Rows", .arr #[row "R1" (scenario.firstA.getD low) high (scenario.children.getD [high, low]), row scenario.secondCode "bad" "bad" ["bad"]])])]

private def evaluate (kind : TemporalKind) (components : TemporalComponents) (format low high expression : String)
    (computation : Bool) (guard : Option String := none) (scenario : Scenario := {}) : Option (Sum Verdict String) := do
  let model := { (model kind components format) with baseYear := scenario.baseYear }
  let model := if scenario.fullDateTarget then
    { model with fields := model.fields.map fun field =>
        if field.id == 1 then
          { field with
            policy := { kind := .temporal .date .fullDate }
            temporalTargetPolicy := some { format := "yyyy-MM-dd" } }
        else field }
    else model
  let model := match scenario.secondFormat with
    | none => model
    | some format => { model with fields := model.fields.map fun field =>
        if field.id == 7 then { field with temporalTargetPolicy := some { format } } else field }
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let document ← (readDocument {
    flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] } (input low high scenario)).toOption
  let document ← (checkDocument prepared "en_US" document.data).toOption
  if computation then
    let numberTarget := guard.isSome && !scenario.temporalGuard
    let step ← (lowerComputation model .english {
      name := "Result", group := ["Form"], targetRelPath := if numberTarget then "../Flag" else "../Out",
      commonPrecondition := guard, alternatives := [{ precondition := none, operation := expression }],
      errorCodesToSuppress := [] }).toOption
    let producers : List (FlatFieldDecl × LoweredComputation model) ← scenario.producer.toList.mapM fun (target, operation) =>
      (lowerComputation model .english {
        name := "Producer", group := ["Form"], targetRelPath := "../" ++ target,
        commonPrecondition := none, alternatives := [{ precondition := none, operation }], errorCodesToSuppress := [] }).toOption
    if scenario.scalarPlan then
      let .number table false := step.2 | none
      let plan ← (certifyScalarComputationPlan [.number table]).toOption
      let [.number 9 (.accepted value)] ← (plan.execute world prepared.patterns document).toOption | none
      return .inr ("value " ++ value.render)
    let results ← (runComputations world prepared document (step.2 :: producers.map (·.2))).toOption
    let target := if numberTarget then "/Flag" else "/Out"
    pure (.inr (String.intercalate "," ((results.filter (·.pointer.endsWith target)).map (·.outcome))))
  else
    let parsed ← (parseText .english expression).toOption
    let condition ← (lowerCondition model ["Form"] false parsed.body).toOption
    Sum.inl <$> (condition.core.evalAddressed {
      scalar := { fields := document.flatContext, groups := GroupPresenceContext.unavailable },
      outer := [], input := .checked document }).toOption

private def profiles : List (TemporalKind × TemporalComponents × String × String × String) := [
  (.date, .fullDate, "yyyy-MM-dd", "2024-01-01", "2024-01-03"),
  (.time, .time, "HH:mm:ss", "01:02:03", "03:02:01"),
  (.dateTime, .now, "yyyy-MM-dd'T'HH:mm:ss", "2024-01-01T01:02:03", "2024-01-03T03:02:01")]

example : profiles.all (fun (kind, components, format, low, high) =>
    [("Rows/Body For Key", Polarity.value), ("Rows/Children*/Value For Key", Polarity.omission),
      ("Rows/Body/A For Key,Rows/Body/B For Key", Polarity.value)].all fun (operands, polarity) =>
      [("MinValue", "Low", low), ("MaxValue", "High", high)].all fun (operator, field, expected) =>
        let expression := operator ++ "(" ++ operands ++ ")"
        let comparison := expression ++ " == [" ++ field ++ "]"
        evaluate kind components format low high comparison false == some (.inl (.fired polarity)) &&
        evaluate kind components format low high expression true == some (.inr ("value " ++ expected)) &&
        evaluate kind components format low high "1" true (some comparison) == some (.inr "value 1")) = true := by native_decide

example : profiles.all (fun (kind, components, format, low, high) =>
    ["MinValue", "MaxValue"].all fun operator =>
      let expression := operator ++ "(Rows/Body For Key)"
      let comparison := expression ++ " == [Low]"
      [(({ key := "missing" } : Scenario), Verdict.notFired),
        ({ firstA := some "bad" }, .unknown), ({ secondCode := "R1" }, .unknown)].all (fun (scenario, expected) =>
        evaluate kind components format low high comparison false none scenario == some (.inl expected) &&
        evaluate kind components format low high expression true none scenario == some (.inr "cleared")) &&
      evaluate kind components format low high (expression ++ " == [" ++ (if operator == "MinValue" then "Low" else "High") ++ "]")
        false none { secondCode := "" } == some (.inl (.fired .value)) &&
      evaluate kind components format low high expression true none { secondCode := "" } == some (.inr "cleared")) = true := by native_decide

example : profiles.all (fun (kind, components, format, low, high) =>
    evaluate kind components format low high "MinValue(Rows/Body For Key)" true none
      { key := "missing", producer := some ("Key", "\"R1\"") } == some (.inr ("value " ++ low)) &&
    evaluate kind components format low high "MinValue(Rows/Body For Key)" true none
      { firstA := some "bad", producer := some ("Rows/Body/A", "MinValue(Low,High)") } == some (.inr ("value " ++ low)) &&
    evaluate kind components format low high "1" true (some "MinValue(Rows/Body For Key) == [Low]")
      { firstA := some "bad", producer := some ("Rows/Body/A", "MinValue(Low,High)") } == some (.inr "value 1")) = true := by native_decide

example : profiles.all (fun (kind, components, format, low, high) =>
    ["MinValue(Rows For Key)", "MinValue(Rows/Body/A For Key)",
      "MinValue(Rows/Body/A For Key,Rows/Body/A For Key)"].all fun expression =>
        evaluate kind components format low high (expression ++ " == [Low]") false == none &&
        evaluate kind components format low high expression true == none) = true := by native_decide

example : evaluate .date .fullDate "yyyy-MM-dd" "2024-01-01" "2024-01-03" "1" true
    (some "MinValue(Rows/Children*/Value For Key) == [Low] Or FieldFilled(Key)")
    { children := some [] } = some (.inr "value 1") ∧
    evaluate .date .fullDate "yyyy-MM-dd" "2024-01-01" "2024-01-03" "1" true
    (some "MinValue(Rows/Children*/Value For Key) == [Low] Or FieldFilled(Key)")
    { children := some ["bad"] } = some (.inr "cleared") := by native_decide

example : ["MinValue(Rows/Body For Key)", "MinValue(Rows/Children*/Value For Key)",
    "MinValue(Rows/Body/A For Key,Rows/Body/B For Key)"].all (fun expression =>
      evaluate .date { TemporalComponents.fullDate with day := false } "yyyy-MM"
        "2024-01" "2024-03" expression true none { fullDateTarget := true } == some (.inr "value 2024-01-01") &&
      evaluate .date { TemporalComponents.fullDate with year := false } "MM-dd"
        "01-03" "03-02" expression true none { fullDateTarget := true, baseYear := some 2024 } ==
        some (.inr "value 2024-01-03")) = true := by native_decide

private def generatedGuard (key : String) (ordinary : Bool := false) : Option FlatRuleOutcome := do
  let model := model .date .fullDate "yyyy-MM-dd"
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let document ← (readDocument {
    flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
    (input "2024-01-01" "2024-01-03" { key })).toOption
  let document ← (checkDocument prepared "en_US" document.data).toOption
  let parsed ← (parseText .english "MinValue(Rows/Body For Key) == [Low]").toOption
  if ordinary then
    let condition ← (lowerCondition model ["Form"] false parsed.body).toOption
    let rule ← (assembleResolvedValidationRule model condition 2 "TEST" .error { parts := [] }).toOption
    if rule.ordinaryIterationPlan != .scalar then none else
      (rule.evalAddressedFull {
        scalar := { fields := document.flatContext, groups := GroupPresenceContext.unavailable }
        outer := [], input := .checked document } true).toOption
  else do
    let surface ← (lowerGuard model ["Form"] false parsed.body (some ["Form"])).toOption
    let guard ← (model.elaborateCheckedComputationCondition ["Form"] ["Form"] surface).toOption
    let operation ← (elaborateCompleteNumericComputationOperation model ["Form"] 9
      (.literal { value := 1, authoredScale := 0 }) false).toOption
    let table : GeneratedComputationTable (CheckedNumericComputationOperation model) (CheckedComputationCondition model) := {
      targetField := 9, name := "Computed", commonPrecondition := some guard
      alternatives := .singleton { operation }, messagePlan := { parts := [] } }
    let rule ← (assembleGeneratedNumericOperationTableRule model table).toOption
    (rule.evalAddressedFull {
      scalar := { fields := document.flatContext, groups := GroupPresenceContext.unavailable }
      outer := [], input := .checked document } true).toOption

example : (generatedGuard "R1").map (·.verdict) = some (.fired .value) ∧
    generatedGuard "missing" = some .notFired := by native_decide

example : profiles.all (fun (kind, components, format, low, high) =>
    evaluate kind components format low high "MinValue(Rows*/Body) == [Low]" false == some (.inl .unknown) &&
    evaluate kind components format low high "MinValue(Rows/Children* For Key) == [Low]" false ==
      some (.inl (.fired .omission)) &&
    evaluate kind components format low high "MinValue(Rows/Children* For Key)" true == some (.inr ("value " ++ low))) =
    true := by native_decide

example : (generatedGuard "R1" true).map (·.verdict) = some (.fired .value) ∧
    generatedGuard "missing" true = some .notFired := by native_decide

private def ordinaryFields (field : String) : Option (List FieldId) := do
  let model := model .date .fullDate "yyyy-MM-dd"
  let parsed ← (parseText .english ("MinValue(Rows/Body For Key) == [Rows/Body/" ++ field ++ "]")).toOption
  let condition ← (lowerCondition model ["Form"] false parsed.body (bindingGroup := ["Form", "Rows", "Body"])).toOption
  pure (condition.core.ordinaryRepeatableFields.map (·.id))

example : ordinaryFields "A" = some [6] ∧ ordinaryFields "B" = some [7] := by native_decide

example : profiles.all (fun (kind, components, format, low, high) =>
    ["MinValue(Rows/Body For Key) == [Low]", "[Low] == [Low]"].all fun guard =>
      evaluate kind components format low high "MinValue(Low,High)" true (some guard)
        { temporalGuard := true } == some (.inr ("value " ++ low)) &&
      evaluate kind components format low high "1" true (some guard)
        { scalarPlan := true } == some (.inr "value 1")) = true := by native_decide

example : profiles.all (fun (kind, components, format, low, high) =>
    [("Rows/Body For Key", Polarity.value), ("Rows/Children*/Value For Key", Polarity.omission), ("Rows/Children* For Key", Polarity.omission),
      ("Rows/Body/A For Key,Rows/Body/B For Key", Polarity.value)].all fun (operands, polarity) =>
      evaluate kind components format low high ("NumberOfDifferentValues(" ++ operands ++ ") == 2") false == some (.inl (.fired polarity)) &&
      evaluate kind components format low high ("NumberOfDifferentValues(" ++ operands ++ ")") true
        (some "FieldFilled(Key)") == some (.inr "value 2")) = true := by native_decide

example : profiles.all (fun (kind, components, format, low, high) =>
    ["Rows/Body For Key", "Rows/Children*/Value For Key", "Rows/Children* For Key", "Rows/Body/A For Key,Rows/Body/B For Key"].all fun operands =>
      evaluate kind components format low high ("FieldValuesNotUnique(" ++ operands ++ ")") false == some (.inl .notFired) &&
      evaluate kind components format low high ("FieldValuesNotUnique(" ++ operands ++ ")") false
        none { firstA := some high, children := some [low, low] } == some (.inl (.fired .value)) &&
      evaluate kind components format low high "1" true (some ("FieldValuesNotUnique(" ++ operands ++ ")"))
        { firstA := some high, children := some [low, low] } == some (.inr "value 1")) = true := by native_decide

private def staticSource (model : FlatModel) (operands : String) : Option SurfaceFieldEntitySource := do
  let parsed ← (parseText .english ("NumberOfDifferentValues(" ++ operands ++ ")")).toOption
  let .call _ arguments none none := parsed.body | none
  (lowerEntitySource model ["Form"] arguments).toOption

private def selectedStaticGates : Bool := Id.run do
  let base := model .date .fullDate "yyyy-MM-dd"
  let differentFormat := { base with fields := base.fields.map fun field =>
    if field.id == 7 then { field with temporalTargetPolicy := some { format := "dd.MM.yyyy" } } else field }
  let differentComponents := { base with fields := base.fields.map fun field =>
    if field.id == 7 then { field with
      policy := { kind := .temporal .date { TemporalComponents.fullDate with day := false } }
      temporalTargetPolicy := some { format := "yyyy-MM" } } else field }
  let partialModel := { base with fields := base.fields.map fun field =>
    if field.id == 7 then { field with temporalTargetPolicy := some { format := "yyyy-MM-dd", partialMode := .dayOptional } } else field }
  return ["Rows/Body For Key", "Rows/Body/A For Key,Rows/Body/B For Key"].all fun operands => Id.run do
    let some formatSource := staticSource differentFormat operands | return false
    let some componentSource := staticSource differentComponents operands | return false
    let some partialSource := staticSource partialModel operands | return false
    return (match elaborateTemporalValuesNotUniqueSource differentFormat ["Form"] formatSource with
      | .error (.mixedDeclaredFormats ["Form", "Rows", "Body", "B"] "dd.MM.yyyy" "yyyy-MM-dd") => true
      | _ => false) &&
      (elaborateTemporalDistinctCountSource differentFormat ["Form"] formatSource).isOk &&
      (match elaborateTemporalDistinctCountSource differentComponents ["Form"] componentSource with
      | .error (.mixedComponentSets ["Form", "Rows", "Body", "B"] "yyyy-MM" "yyyy-MM-dd") => true
      | _ => false) &&
      (match elaborateTemporalDistinctCountSource partialModel ["Form"] partialSource with
      | .error (.partialDate ["Form", "Rows", "Body", "B"] .dayOptional) => true
      | _ => false) &&
      (elaborateTemporalValuesNotUniqueSource partialModel ["Form"] partialSource).isOk

example : selectedStaticGates = true := by native_decide

example : ["Rows/Body For Key", "Rows/Body/A For Key,Rows/Body/B For Key"].all (fun operands =>
    let expression := "NumberOfDifferentValues(" ++ operands ++ ")"
    evaluate .date .fullDate "yyyy-MM-dd" "2024-01-01" "01.01.2024" (expression ++ " == 1") false
      none { secondFormat := some "dd.MM.yyyy" } == some (.inl (.fired .value)) &&
    evaluate .date .fullDate "yyyy-MM-dd" "2024-01-01" "01.01.2024" expression true
      (some "FieldFilled(Key)") { secondFormat := some "dd.MM.yyyy" } == some (.inr "value 1")) = true := by native_decide

example : profiles.all (fun (kind, components, format, low, high) =>
    ["Rows/Body For Key", "Rows/Children*/Value For Key", "Rows/Children* For Key", "Rows/Body/A For Key,Rows/Body/B For Key"].all fun operands =>
      let count := "NumberOfDifferentValues(" ++ operands ++ ")"
      let unique := "FieldValuesNotUnique(" ++ operands ++ ")"
      evaluate kind components format low high count true (some "FieldFilled(Key)")
        { key := "missing", producer := some ("Key", "\"R1\"") } == some (.inr "value 2") &&
      evaluate kind components format low high "1" true (some unique)
        { key := "missing", firstA := some high, children := some [low, low], producer := some ("Key", "\"R1\"") } == some (.inr "value 1") &&
      (if (operands == "Rows/Children*/Value For Key" || operands == "Rows/Children* For Key") then true else
        evaluate kind components format low high count true (some "FieldFilled(Key)")
          { firstA := some "bad", producer := some ("Rows/Body/A", "MaxValue(Low,High)") } == some (.inr "value 1") &&
        evaluate kind components format low high "1" true (some unique)
          { firstA := some "bad", producer := some ("Rows/Body/A", "MaxValue(Low,High)") } == some (.inr "value 1"))) = true := by native_decide

example : profiles.all (fun (kind, components, format, low, high) =>
    ["NumberOfDifferentValues", "FieldValuesNotUnique"].all fun operator =>
      ["Rows For Key", "Rows/Body/A For Key", "Rows/Body/A For Key,Rows/Body/A For Key"].all fun operands =>
        let expression := operator ++ "(" ++ operands ++ ")"
        let condition := if operator == "NumberOfDifferentValues" then expression ++ " == 1" else expression
        evaluate kind components format low high condition false == none &&
        evaluate kind components format low high "1" true (some condition) == none) = true := by native_decide

example : profiles.all (fun (kind, components, format, low, high) =>
    [(({ key := "missing" } : Scenario), Verdict.notFired),
      ({ firstA := some "bad" }, .unknown), ({ secondCode := "R1" }, .unknown)].all fun (scenario, expected) =>
      evaluate kind components format low high "NumberOfDifferentValues(Rows/Body For Key) == 2" false
        none scenario == some (.inl expected) &&
      evaluate kind components format low high "NumberOfDifferentValues(Rows/Body For Key)" true
        (some "FieldFilled(Key)") scenario == some (.inr (if scenario.key == "missing" then "value 0" else "cleared")) &&
      evaluate kind components format low high "FieldValuesNotUnique(Rows/Body For Key)" false
        none scenario == some (.inl .notFired) &&
      evaluate kind components format low high "1" true
        (some "FieldValuesNotUnique(Rows/Body For Key)") scenario == some (.inr "cleared")) = true := by native_decide

example : profiles.all (fun (kind, components, format, low, high) =>
    ["Rows/Children*/Value For Key", "Rows/Children* For Key"].all fun operands =>
      let count := "NumberOfDifferentValues(" ++ operands ++ ")"
      let unique := "FieldValuesNotUnique(" ++ operands ++ ")"
      evaluate kind components format low high (count ++ " == 0") false none
        { children := some [] } == some (.inl (.fired .omission)) &&
      evaluate kind components format low high count true (some "FieldFilled(Key)")
        { children := some [] } == some (.inr "value 0") &&
      evaluate kind components format low high (unique ++ " Or FieldFilled(Key)") false none
        { children := some ["bad"] } == some (.inl (.fired .value)) &&
      evaluate kind components format low high "1" true (some (unique ++ " Or FieldFilled(Key)"))
        { children := some [] } == some (.inr "value 1") &&
      evaluate kind components format low high "1" true (some (unique ++ " Or FieldFilled(Key)"))
        { children := some ["bad"] } == some (.inr "cleared")) = true := by native_decide

example : [none, some 2024].all (fun baseYear =>
    ["Rows/Body For Key", "Rows/Children*/Value For Key", "Rows/Children* For Key", "Rows/Body/A For Key,Rows/Body/B For Key"].all fun operands =>
      let count := "NumberOfDifferentValues(" ++ operands ++ ")"
      evaluate .date { TemporalComponents.fullDate with year := false } "MM-dd" "01-03" "03-02"
        (count ++ " == 2") false none { baseYear } ==
        some (.inl (.fired (if (operands == "Rows/Children*/Value For Key" || operands == "Rows/Children* For Key") then .omission else .value))) &&
      evaluate .date { TemporalComponents.fullDate with year := false } "MM-dd" "01-03" "03-02"
        count true (some "FieldFilled(Key)") { baseYear } == some (.inr "value 2")) = true := by native_decide

example : profiles.all (fun (kind, components, format, low, high) =>
    evaluate kind components format low high "NumberOfDifferentValues(Rows/Body For Key) == 2" false
      none { secondCode := "" } == some (.inl (.fired .value)) &&
    evaluate kind components format low high "NumberOfDifferentValues(Rows/Body For Key)" true
      (some "FieldFilled(Key)") { secondCode := "" } == some (.inr "cleared") &&
    evaluate kind components format low high "FieldValuesNotUnique(Rows/Body For Key)" false
      none { firstA := some high, secondCode := "" } == some (.inl (.fired .value)) &&
    evaluate kind components format low high "1" true (some "FieldValuesNotUnique(Rows/Body For Key)")
      { firstA := some high, secondCode := "" } == some (.inr "cleared")) = true := by native_decide

example : profiles.all (fun (kind, components, format, low, high) =>
    [("NumberOfDifferentValues(Rows/Body For Key) == 2", ({} : Scenario)),
      ("FieldValuesNotUnique(Rows/Body For Key)", { firstA := some high })].all fun (guard, scenario) =>
      evaluate kind components format low high "MinValue(Low,High)" true (some guard)
        { scenario with temporalGuard := true } == some (.inr ("value " ++ low)) &&
      evaluate kind components format low high "1" true (some guard)
        { scenario with scalarPlan := true } == some (.inr "value 1")) = true := by native_decide

end A12Kernel.Dm.IndexedTemporalLocks
