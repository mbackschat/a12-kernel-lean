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
      { id := 9, name := "Flag", groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := true } } },
      { id := 10, name := "Amount", groupPath := ["Form", "Rows"], repeatableScope := [10],
        policy := { kind := .number { scale := 0, signed := true } } }]
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
  partialCoverage : Option (List RelevantEntityPattern) := none
  partialMode : TemporalPartialMode := .full
  validSecond : Bool := false

private def input (low high : String) (scenario : Scenario) : Lean.Json :=
  let row (key a b : String) (children : List String) := Lean.Json.mkObj [
    ("Code", .str key), ("Amount", .str (if key == "R1" then "1" else "2")), ("Body", Lean.Json.mkObj [("A", .str a), ("B", .str b)]),
    ("Children", .arr (children.map fun value => Lean.Json.mkObj [("Value", .str value)]).toArray)]
  Lean.Json.mkObj [("Form", Lean.Json.mkObj [
    ("Out", .str "bad"), ("Flag", .str "99"), ("Low", .str low), ("High", .str high), ("Key", .str scenario.key),
    ("Rows", .arr #[row "R1" (scenario.firstA.getD low) high (scenario.children.getD [high, low]), row scenario.secondCode (if scenario.validSecond then low else "bad")
      (if scenario.validSecond then high else "bad") (if scenario.validSecond then [low] else ["bad"])])])]

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
  let model : FlatModel := match scenario.secondFormat with
    | none => model
    | some format => { model with fields := model.fields.map fun field =>
        if field.id == 7 then { field with temporalTargetPolicy := some { format } } else field }
  let model : FlatModel := { model with fields := model.fields.map fun field =>
    { field with temporalTargetPolicy := field.temporalTargetPolicy.map fun policy =>
        { policy with partialMode := scenario.partialMode } } }
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
    let parsed ← (parseText .english (if scenario.partialCoverage.isSome then
      "FieldFilled(Flag) And (" ++ expression ++ ")" else expression)).toOption
    let condition ← (lowerCondition model ["Form"] false parsed.body).toOption
    if let some coverage := scenario.partialCoverage then
      let rule ← (assembleResolvedValidationRule model condition 9 "PARTIAL_TEMPORAL" .error { parts := [] }).toOption
      let result ← (rule.evalAddressedPartial document (.partialSet (
        { path := ["Form", "Flag"], indices := [.all, .all] } :: coverage))).toOption
      match result with
      | .evaluated result => return .inl result.verdict
      | .skipped => some (.inr "skipped")
    else Sum.inl <$> (condition.core.evalAddressed {
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

private def relevant (path : List String) : RelevantEntityPattern :=
  { path := "Form" :: path, indices := (List.range (path.length + 1)).map fun _ => .all }

example : profiles.all (fun (kind, components, format, low, high) =>
    ["Rows/Body For Key", "Rows/Children*/Value For Key", "Rows/Children* For Key",
      "Rows/Body/A For Key,Rows/Body/B For Key"].all fun operands =>
      let expression := "FieldValuesNotUnique(" ++ operands ++ ")"
      evaluate kind components format low high expression false none
        { firstA := some high, children := some [low, low],
          partialCoverage := some [relevant ["Key"], relevant ["Rows"]] } == some (.inl (.fired .value)) &&
      evaluate kind components format low high expression false none
        { partialCoverage := some [relevant ["Key"], relevant ["Rows"]] } == some (.inl .notFired)) = true := by native_decide

example : profiles.all (fun (kind, components, format, low, high) =>
    evaluate kind components format low low "FieldValuesNotUnique(Low,High)" false none
      { partialCoverage := some [relevant ["Low"], relevant ["High"]] } == some (.inl (.fired .value)) &&
    evaluate kind components format low high "FieldValuesNotUnique(Rows*/Body)" false none
      { firstA := some high, partialCoverage := some [relevant ["Rows"]] } == some (.inl (.fired .value))) = true := by native_decide

private def concreteChild (child : Nat) : RelevantEntityPattern :=
  { path := ["Form", "Rows", "Children", "Value"], indices := [.all, .concrete 1, .concrete child, .all] }

example : profiles.all (fun (kind, components, format, low, high) =>
    ["Rows/Children*/Value For Key", "Rows/Children* For Key"].all fun operands =>
      let expression := "FieldValuesNotUnique(" ++ operands ++ ")"
      evaluate kind components format low high expression false none
        { children := some [low, low], partialCoverage := some [relevant ["Key"], relevant ["Rows", "Code"],
            concreteChild 1, concreteChild 2] } == some (.inl (.fired .value)) &&
      evaluate kind components format low high expression false none
        { children := some [low, low], partialCoverage := some [relevant ["Key"], relevant ["Rows", "Code"],
            concreteChild 1] } == some (.inl .notFired)) = true := by native_decide

example : profiles.all (fun (kind, components, format, low, high) =>
    let expression := "FieldValuesNotUnique(Rows/Body For Key)"
    evaluate kind components format low high expression false none
      { firstA := some high, partialCoverage := some [relevant ["Key"], relevant ["Rows", "Code"], relevant ["Rows", "Body", "A"]] } == some (.inl .notFired) &&
    evaluate kind components format low high expression false none
      { firstA := some high, secondCode := "R1", partialCoverage := some [relevant ["Key"], relevant ["Rows"]] } == some (.inl .notFired) &&
    evaluate kind components format low high expression false none
      { firstA := some high, secondCode := "R1", partialCoverage := some [relevant ["Key"],
          { path := ["Form", "Rows"], indices := [.all, .concrete 1] }] } == some (.inl (.fired .value)) &&
    evaluate kind components format low high expression false none
      { firstA := some high, secondCode := "", partialCoverage := some [relevant ["Key"], relevant ["Rows"]] } == some (.inl (.fired .value)) &&
    evaluate kind components format low high expression false none
      { firstA := some high, partialCoverage := some [relevant ["Rows"]] } == some (.inl .notFired)) = true := by native_decide

example : [TemporalPartialMode.dayOptional, .monthOptional, .yearOptional].all (fun partialMode =>
    evaluate .date .fullDate "yyyy-MM-dd" "2024-06-00" "2024-06-00" "FieldValuesNotUnique(Rows/Body For Key)" false none
      { partialMode, partialCoverage := some [relevant ["Key"], relevant ["Rows"]] } == some (.inl (.fired .value))) = true := by native_decide

example : evaluate .date .fullDate "yyyy-MM-dd" "2024-01-01" "2024-01-01"
    "FieldFilled(Flag) Or FieldValuesNotUnique(Rows*/Body/A Having (FieldFilled(Rows/Body/A)))" false none
    { partialCoverage := some [relevant ["Rows"]] } = some (.inr "skipped") := by native_decide

private inductive PartialReadChange where
  | unchanged | unavailable | unavailableError | malformed | copyLow
  | keyText (value : String)
  | structural

private def partialReadback (expression : String) (field : FieldId) (change : PartialReadChange)
    (partialMode : TemporalPartialMode := .full) (structuralField : Option FieldId := none) :
    Option (Sum Verdict (List String)) := do
  let sourceModel : FlatModel := { (model .date .fullDate "yyyy-MM-dd") with
    fields := (model .date .fullDate "yyyy-MM-dd").fields.map fun declaration =>
      { declaration with temporalTargetPolicy := declaration.temporalTargetPolicy.map fun policy => { policy with partialMode } } }
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } } builtinStringPatternCompiler sourceModel).toOption
  let low := if partialMode == .full then "2024-01-01" else "2024-01-00"
  let high := if partialMode == .full then "2024-01-03" else "2024-02-00"
  let input ← (readDocument {
    flat := sourceModel, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
    (input low high { firstA := some high })).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  let parsed ← (parseText .english expression).toOption
  let checked ← (lowerCondition sourceModel ["Form"] false parsed.body).toOption
  let .leaf leaf := checked.core | none
  let context : AddressedValidationEvaluationContext sourceModel := {
    scalar := { fields := document.flatContext, groups := GroupPresenceContext.unavailable }, outer := []
    input := .partialView document fun row current =>
      if structuralField == some current then .error (.checkedDocumentRequired ["injected"])
      else if current != field then (fun addressed => some addressed.cell) <$> document.addressedCell row current
      else match change with
      | .unchanged => (fun addressed => some addressed.cell) <$> document.addressedCell row current
      | .unavailable => pure none
      | .unavailableError => .error (.partialUnavailable row current)
      | .malformed => pure (some malformedCheckedCell)
      | .copyLow => pure (some (document.flatContext.read 2))
      | .structural => .error (.checkedDocumentRequired ["injected"])
      | .keyText text => pure (some (checkAdmittedRawCell (.parsed (.str text)))) }
  let result ← leaf.evalAddressedPartial? context .full (fun _ => true)
    (fun _ _ => .error (.checkedDocumentRequired [])) none
  pure (match result with
    | .ok verdict => .inl verdict
    | .error (.checkedDocumentRequired path) => .inr path
    | .error _ => .inr ["unexpected failure"])

example : partialReadback "FieldValuesNotUnique(Rows/Body For Key)" 6 .unchanged = some (.inl (.fired .value)) ∧
    [PartialReadChange.unavailable, .unavailableError, .malformed].all
      (fun change => partialReadback "FieldValuesNotUnique(Rows/Body For Key)" 6 change == some (.inl .notFired)) = true := by native_decide

example : partialReadback "FieldValuesNotUnique(Rows/Body For Key)" 6 .copyLow =
      some (.inr ["Form", "Rows", "Body", "A"]) ∧
    partialReadback "FieldValuesNotUnique(Low,High)" 3 .copyLow =
      some (.inr ["Form", "High"]) ∧
    partialReadback "FieldValuesNotUnique(Rows/Body For Key)" 6 .copyLow .dayOptional = some (.inl .notFired) ∧
    partialReadback "FieldValuesNotUnique(Low,High)" 3 .copyLow .dayOptional = some (.inl (.fired .value)) := by native_decide

example : profiles.all (fun (kind, components, format, low, high) =>
    [[low, "bad", low], [low, low, "bad"]].all fun children =>
      evaluate kind components format low high "FieldValuesNotUnique(Rows/Children*/Value For Key)" false none
        { children := some children, partialCoverage := some [relevant ["Key"], relevant ["Rows"]] } == some (.inl (.fired .value))) = true := by native_decide

example : profiles.all (fun (kind, components, format, low, high) =>
    evaluate kind components format low low "FieldValuesNotUnique(Low,High)" false none
      { partialCoverage := some [relevant ["Low"]] } == some (.inl .notFired) &&
    evaluate kind components format low high "FieldValuesNotUnique(Rows/Body For Key)" false none
      { key := "missing", partialCoverage := some [relevant ["Key"], relevant ["Rows"]] } == some (.inl .notFired) &&
    evaluate kind components format low high "FieldValuesNotUnique(Rows/Children*/Value For Key)" false none
      { children := some [], partialCoverage := some [relevant ["Key"], relevant ["Rows"]] } == some (.inl .notFired)) = true := by native_decide

example : partialReadback "[Rows/Amount For Key] == 2" 4 (.keyText "R2") = some (.inl (.fired .value)) ∧
    partialReadback "FieldValuesNotUnique(Rows/Body For Key)" 4 (.keyText "R2") = some (.inl .notFired) ∧
    partialReadback "FieldValuesNotUnique(Rows/Body/A For Key,Rows/Body/B For Key)" 4 (.keyText "R2") = some (.inl .notFired) ∧
    partialReadback "FieldValuesNotUnique(Rows/Code For Key,Key)" 4 (.keyText "R2") = some (.inl (.fired .value)) := by native_decide

example : ["FieldValuesNotUnique(Rows/Body For Key)", "FieldValuesNotUnique(Rows/Code For Key,Key)",
    "[Rows/Amount For Key] == 2"].all (fun expression =>
      (partialReadback expression 4 .unavailable).isSome &&
      partialReadback expression 4 .unavailableError == partialReadback expression 4 .unavailable) = true := by native_decide

example : ["FieldValuesNotUnique(Rows/Body For Key)", "FieldValuesNotUnique(Rows/Code For Key,Key)",
    "[Rows/Amount For Key] == 2"].all (fun expression =>
      partialReadback expression 4 .structural == some (.inr ["injected"])) = true := by native_decide

example : [PartialReadChange.unchanged, .keyText "R2", .unavailable, .unavailableError, .malformed, .structural].all
    (fun change => partialReadback "FieldValuesNotUnique(Rows/Body For \"R1\")" 4 change ==
      some (.inl (.fired .value))) = true := by native_decide

example : partialReadback "[Rows/Amount For Key] == 2" 4 .unchanged = some (.inl .notFired) ∧
    partialReadback "FieldValuesNotUnique(Rows/Body For Key)" 4 .unchanged = some (.inl (.fired .value)) ∧
    partialReadback "FieldValuesNotUnique(Rows/Body For Key)" 4 .malformed = some (.inl .notFired) := by native_decide

example : profiles.all (fun (kind, components, format, low, high) =>
    ["Low,High", "Rows*/Body", "Rows/Body For Key", "Rows/Children*/Value For Key",
      "Rows/Children* For Key", "Rows/Body/A For Key,Rows/Body/B For Key"].all fun operands =>
      let count := "NumberOfDifferentValues(" ++ operands ++ ")"
      evaluate kind components format low high (count ++ " == 2") false none
        { partialCoverage := some [relevant ["Low"], relevant ["High"], relevant ["Key"], relevant ["Rows"]],
          secondCode := "R2", children := some [low, high] } ==
        evaluate kind components format low high (count ++ " == 2") false none
          { secondCode := "R2", children := some [low, high] }) = true := by native_decide

example : evaluate .date .fullDate "yyyy-MM-dd" "2024-01-01" "2024-01-03"
    "NumberOfDifferentValues(Rows/Children*/Value For Key) == 2" false none
    { partialCoverage := some [relevant ["Key"], relevant ["Rows", "Code"], concreteChild 1, concreteChild 2] } =
      some (.inl .unknown) := by native_decide

example : partialReadback "NumberOfDifferentValues(Rows/Body For Key) == 2" 6 .copyLow =
    some (.inl (.fired .value)) := by native_decide

example : profiles.all (fun (kind, components, format, low, high) =>
    ["Low,High", "Rows*/Body", "Rows*/Children*/Value", "Rows*/Children*", "Rows/Body For Key",
      "Rows/Children*/Value For Key", "Rows/Children* For Key",
      "Rows/Body/A For Key,Rows/Body/B For Key"].all fun operands =>
      let expression := "NumberOfDifferentValues(" ++ operands ++ ") == 2"
      let scenario : Scenario := { validSecond := true }
      let full := evaluate kind components format low high expression false none scenario
      let expected := if operands == "Low,High" || operands == "Rows/Body For Key" ||
          operands == "Rows/Body/A For Key,Rows/Body/B For Key" then Polarity.value else .omission
      full == some (.inl (.fired expected)) &&
      evaluate kind components format low high expression false none
        { scenario with partialCoverage := some [relevant ["Low"], relevant ["High"], relevant ["Key"], relevant ["Rows"]] } == full) = true := by native_decide

example : profiles.all (fun (kind, components, format, low, high) =>
    ["Rows/Body For Key", "Rows/Children*/Value For Key", "Rows/Children* For Key",
      "Rows/Body/A For Key,Rows/Body/B For Key"].all fun operands =>
      let expression := "NumberOfDifferentValues(" ++ operands ++ ") == 0"
      let full := evaluate kind components format low high expression false none { key := "missing" }
      full == some (.inl (.fired (if operands == "Rows/Children*/Value For Key" ||
          operands == "Rows/Children* For Key" then .value else .omission))) &&
      evaluate kind components format low high expression false none
        { key := "missing", partialCoverage := some [relevant ["Key"], relevant ["Rows"]] } == full) = true := by native_decide

example : ["Rows/Body For Key", "Rows/Body/A For Key,Rows/Body/B For Key"].all (fun operands =>
    let expression := "NumberOfDifferentValues(" ++ operands ++ ") == 2"
    partialReadback expression 6 .malformed .full (some 7) == some (.inl .unknown) &&
    partialReadback expression 7 .malformed .full (some 6) == some (.inr ["injected"]) &&
    [PartialReadChange.unavailable, .unavailableError].all (fun change =>
      partialReadback expression 6 change == some (.inl .unknown))) = true := by native_decide

example : evaluate .date .fullDate "yyyy-MM-dd" "2024-01-01" "01.01.2024"
    "NumberOfDifferentValues(Rows/Body For Key) == 1" false none
    { secondFormat := some "dd.MM.yyyy", partialCoverage := some [relevant ["Key"], relevant ["Rows"]] } =
      some (.inl (.fired .value)) := by native_decide

example : [none, some 2024].all (fun baseYear =>
    evaluate .date { TemporalComponents.fullDate with year := false } "MM-dd" "01-03" "03-02"
      "NumberOfDifferentValues(Rows/Body For Key) == 2" false none
      { baseYear, partialCoverage := some [relevant ["Key"], relevant ["Rows"]] } ==
        some (.inl (.fired .value))) = true := by native_decide

example : evaluate .date .fullDate "yyyy-MM-dd" "2024-01-01" "2024-01-03"
    "FieldFilled(Flag) Or NumberOfDifferentValues(Rows*/Body/A Having (FieldFilled(Rows/Body/A))) == 2" false none
    { partialCoverage := some [relevant ["Rows"]] } = some (.inr "skipped") := by native_decide

example : ["Rows/Body For Key", "Rows/Children*/Value For Key", "Rows/Children* For Key"].all (fun operands =>
    let expression := "NumberOfDifferentValues(" ++ operands ++ ") == 2"
    evaluate .date .fullDate "yyyy-MM-dd" "2024-01-01" "2024-01-03" expression false none
      { partialCoverage := some [relevant ["Rows"]] } == some (.inl .unknown) &&
    evaluate .date .fullDate "yyyy-MM-dd" "2024-01-01" "2024-01-03" expression false none
      { secondCode := "R1", partialCoverage := some [relevant ["Key"], relevant ["Rows"]] } == some (.inl .unknown) &&
    evaluate .date .fullDate "yyyy-MM-dd" "2024-01-01" "2024-01-03" expression false none
      { secondCode := "", partialCoverage := some [relevant ["Key"], relevant ["Rows"]] } ==
        some (.inl (.fired (if operands == "Rows/Body For Key" then .value else .omission)))) = true := by native_decide

example : ["Rows/Children*/Value For Key", "Rows/Children* For Key"].all (fun operands =>
    let expression := "NumberOfDifferentValues(" ++ operands ++ ") == 0"
    evaluate .date .fullDate "yyyy-MM-dd" "2024-01-01" "2024-01-03" expression false none
      { children := some [], partialCoverage := some [relevant ["Key"], relevant ["Rows"]] } ==
        some (.inl (.fired .omission))) = true := by native_decide

example : ["Rows/Children*/Value For Key", "Rows/Children* For Key", "Rows*/Children*/Value"].all (fun operands =>
    let expression := "NumberOfDifferentValues(" ++ operands ++ ") == 2"
    let fieldWildcard : RelevantEntityPattern := {
      path := ["Form", "Rows", "Children", "Value"], indices := [.all, .all, .all, .concrete 1] }
    let concreteField : RelevantEntityPattern := {
      fieldWildcard with indices := [.all, .concrete 1, .concrete 1, .concrete 1] }
    let coverage := [relevant ["Key"], relevant ["Rows", "Code"], fieldWildcard]
    let concreteGroup : RelevantEntityPattern := {
      path := ["Form", "Rows", "Children"], indices := [.all, .concrete 1, .concrete 1] }
    evaluate .date .fullDate "yyyy-MM-dd" "2024-01-01" "2024-01-03" expression false none
      { validSecond := true, partialCoverage := some (concreteGroup :: coverage) } == some (.inl .unknown) &&
    evaluate .date .fullDate "yyyy-MM-dd" "2024-01-01" "2024-01-03" expression false none
      { validSecond := true, partialCoverage := some (concreteField :: coverage) } ==
        some (.inl (.fired .omission))) = true := by native_decide


example : profiles.all (fun (kind, components, format, low, high) =>
    ["Key", "\"R1\""].all fun key =>
      let expression := "[Rows/Body/A For " ++ key ++ "]"
      evaluate kind components format low high (expression ++ " == [Low]") false == some (.inl (.fired .value)) &&
      evaluate kind components format low high ("Max(" ++ expression ++ ",[High])") true == some (.inr ("value " ++ high)) &&
      evaluate kind components format low high "1" true (some (expression ++ " == [Low]")) == some (.inr "value 1")) = true := by native_decide

example : profiles.all (fun (kind, components, format, low, high) =>
    let expression := "Min([Rows/Body/A For Key],[Low])"
    [(({ key := "missing" } : Scenario), Verdict.notFired),
      ({ firstA := some "bad" }, .unknown), ({ secondCode := "R1" }, .unknown)].all (fun (scenario, expected) =>
        evaluate kind components format low high "[Rows/Body/A For Key] == [Low]" false none scenario == some (.inl expected) &&
        evaluate kind components format low high expression true none scenario ==
          some (.inr (if scenario.key == "missing" then "value " ++ low else "cleared"))) &&
    evaluate kind components format low high "Max([Rows/Body/A For Key],[Low])" true none
      { key := "missing", firstA := some high, producer := some ("Key", "\"R1\"") } == some (.inr ("value " ++ high)) &&
    evaluate kind components format low high "Max([Rows/Body/A For Key],[Low])" true none
      { firstA := some "bad", producer := some ("Rows/Body/A", "MaxValue(Low,High)") } == some (.inr ("value " ++ high))) = true := by native_decide

example : evaluate .date .fullDate "yyyy-MM-dd" "2024-01-01" "2024-01-03"
    "AddDays(Rows/Body/A For Key,2) == [High]" false == some (.inl (.fired .value)) ∧
    evaluate .date .fullDate "yyyy-MM-dd" "2024-01-01" "2024-01-03"
      "AddDays(Rows/Body/A For Key,2)" true == some (.inr "value 2024-01-03") := by native_decide

example : [("YearFromDate", "2024"), ("MonthFromDate", "1"), ("DayFromDate", "1"), ("QuarterFromDate", "1")].all (fun (operator, expected) =>
    let expression := operator ++ "(Rows/Body/A For Key)"
    evaluate .date .fullDate "yyyy-MM-dd" "2024-01-01" "2024-01-03"
      (expression ++ " == " ++ expected) false == some (.inl (.fired .value)) &&
    evaluate .date .fullDate "yyyy-MM-dd" "2024-01-01" "2024-01-03"
      expression true (some "FieldFilled(Key)") == some (.inr ("value " ++ expected))) = true := by native_decide

example : [(.time, TemporalComponents.time, "HH:mm:ss", "01:02:03", "03:02:01"),
    (.dateTime, .now, "yyyy-MM-dd'T'HH:mm:ss", "2024-01-01T01:02:03", "2024-01-03T03:02:01")].all
    (fun (kind, components, format, low, high) =>
      [("HoursFromTime", "1"), ("MinutesFromTime", "2"), ("SecondsFromTime", "3")].all fun (operator, expected) =>
        let expression := operator ++ "(Rows/Body/A For Key)"
        evaluate kind components format low high (expression ++ " == " ++ expected) false == some (.inl (.fired .value)) &&
        evaluate kind components format low high expression true (some "FieldFilled(Key)") == some (.inr ("value " ++ expected))) = true := by native_decide

example : evaluate .dateTime .now "yyyy-MM-dd'T'HH:mm:ss" "2024-01-01T01:02:03" "2024-01-03T03:02:01"
    "DateTime(DateFromDateTime(Rows/Body/A For Key),TimeFromDateTime(Rows/Body/A For Key)) == [Low]"
    false == some (.inl (.fired .value)) ∧
    evaluate .time .time "HH:mm:ss" "01:02:03" "03:02:01"
      "Time(HoursFromTime(Rows/Body/A For Key),MinutesFromTime(Rows/Body/A For Key),SecondsFromTime(Rows/Body/A For Key))"
      true == some (.inr "value 01:02:03") := by native_decide


example : evaluate .dateTime .now "yyyy-MM-dd'T'HH:mm:ss" "2024-01-01T01:02:03" "2024-01-03T03:02:01"
    "SecondsFromTime(AddSeconds(Rows/Body/A For Key,1)) == 4" false == some (.inl (.fired .value)) ∧
    evaluate .dateTime .now "yyyy-MM-dd'T'HH:mm:ss" "2024-01-01T01:02:03" "2024-01-03T03:02:01"
      "SecondsFromTime(AddSeconds(Rows/Body/A For Key,1))" true (some "FieldFilled(Key)") == some (.inr "value 4") ∧
    evaluate .time .time "HH:mm:ss" "01:02:03" "03:02:01"
      "HoursFromTime(Rows/Body/A For Key)" true (some "FieldFilled(Key)") { scalarPlan := true } == some (.inr "value 1") := by native_decide

example : evaluate .time .time "HH:mm:ss" "01:02:03" "03:02:01"
    "HoursFromTime(Rows/Body/A For Key)" true (some "FieldFilled(Key)")
    { firstA := some "03:02:01", key := "missing", producer := some ("Key", "\"R1\"") } == some (.inr "value 3") ∧
    evaluate .time .time "HH:mm:ss" "01:02:03" "03:02:01"
      "HoursFromTime(Rows/Body/A For Key)" true (some "FieldFilled(Key)")
      { firstA := some "bad", producer := some ("Rows/Body/A", "MaxValue(Low,High)") } == some (.inr "value 3") := by native_decide

example : [none, some 2024].all (fun baseYear =>
    evaluate .date { TemporalComponents.fullDate with year := false } "MM-dd" "01-01" "01-03"
      "AddDays(Rows/Body/A For Key,2) == [High]" false none { baseYear } == some (.inl (.fired .value))) = true := by native_decide

example : ["AddDays([Rows/Body/A For Key],2) == [High]",
    "Rows/Body/A For Key == [Low]", "AddDays(Rows/Amount For Key,2) == [High]",
    "[Rows/Body/A For 1] == [Low]", "DateTime(Rows/Body/A For Key,Rows/Body/B For Key) == [Low]"].all
    (fun expression => (evaluate .date .fullDate "yyyy-MM-dd" "2024-01-01" "2024-01-03" expression false).isNone) = true := by native_decide

private def indexedScalarDependencies : Option (List FieldId × List FieldId × List (List RepeatableLevel) × Bool × List FieldId) := do
  let model := model .date .fullDate "yyyy-MM-dd"
  let parsed ← (parseText .english "AddDays(Rows/Body/A For Key,2)").toOption
  let surface ← (lowerScalarTemporalExpression model ["Form"] parsed.body).toOption
  let checked ← (elaborateScalarTemporalExpression model ["Form"] surface).toOption
  pure (checked.fieldIds, checked.boundFieldIds, checked.bindingScopes, checked.requiresAddressed, checked.storedTextFields)

example : indexedScalarDependencies = some ([4,5,6], [4], [[]], true, [4]) := by native_decide

example : (evaluate .date .fullDate "yyyy-MM-dd" "2024-01-01" "2024-01-03"
    "[Rows/Body/A For Key] == [Low]" false none { partialCoverage := some [] }).isNone = true ∧
    (evaluate .date .fullDate "yyyy-MM-dd" "2024-01-01" "2024-01-03"
      "[Rows/Body/A For Key] == [Low]" false none { partialMode := .dayOptional }).isNone = true := by native_decide


private def numericMissingBinding (expression : String) : Option Bool := do
  let model := model .date .fullDate "yyyy-MM-dd"
  let parsed ← (parseText .english expression).toOption
  let surface ← (lowerScalarTemporalExpression model ["Form"] parsed.body).toOption
  let source ← (elaborateTemporalNumericExpression model ["Form"] surface (.date .day) (some ["Form", "Rows"])).toOption
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } } builtinStringPatternCompiler model).toOption
  let document ← (readDocument {
    flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
    (input "2024-01-01" "2024-01-03" {})).toOption
  let document ← (checkDocument prepared "en_US" document.data).toOption
  pure (!((OrderedNumericValidationAtom.temporalPart source).resolveAddressed {
    scalar := { fields := document.flatContext, groups := GroupPresenceContext.unavailable },
    outer := [], input := .checked document }).isOk)

example : numericMissingBinding "[Rows/Body/A]" = some true ∧
    numericMissingBinding "AddDays(Rows/Body/A,2)" = some true := by native_decide


private def indexedNumericContexts (expression : String) : Option (List (Option Rat)) := do
  let model := model .date .fullDate "yyyy-MM-dd"
  let parsed ← (parseText .english expression).toOption
  let surface ← (lowerScalarTemporalExpression model ["Form"] parsed.body).toOption
  let source ← (elaborateTemporalNumericExpression model ["Form"] surface (.date .day)).toOption
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let data ← (readDocument { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
    (input "2024-01-01" "2024-01-03" {})).toOption
  let checked ← (checkDocument prepared "en_US" data.data).toOption
  let scalar := checked.indexedScalarComputationContext world
  let context : NumericComputationEvaluationContext := {
    scalar, document := checked.computationFillContext.document, outer := [],
    filterRead := checked.computationFillContext.read, starRead := checked.computationFillContext.read }
  let atom := CheckedNumericComputationAtom.temporalPart source
  let explicit := { context with indexColumn? := some scalar.semanticIndexColumnReader }
  pure ([scalar.readCheckedNumericComputationAtom atom, context.readCheckedNumericComputationAtom atom,
    explicit.readCheckedNumericComputationAtom atom].map fun result =>
      result.toOption.bind fun | .value amount => some amount | _ => none)

example : indexedNumericContexts "[Rows/Body/A For Key]" = some [some 1, some 1, some 1] ∧
    indexedNumericContexts "AddDays(Rows/Body/A For Key,2)" = some [some 3, some 3, some 3] := by native_decide

end A12Kernel.Dm.IndexedTemporalLocks
