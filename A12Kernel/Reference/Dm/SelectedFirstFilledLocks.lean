import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document

namespace A12Kernel.Dm.SelectedFirstFilledLocks

private inductive Profile where
  | boolean | date | time | stamp | fragment | range | custom
  deriving BEq

private def profiles : List Profile := [.boolean, .date, .time, .stamp, .fragment, .range, .custom]

private def prototype (profile : Profile) : FlatFieldDecl :=
  let temporal (kind : TemporalKind) (components : TemporalComponents) (format : String) : FlatFieldDecl := {
    id := 0, name := "Value", groupPath := ["Form"], policy := { kind := .temporal kind components },
    temporalTargetPolicy := some { format } }
  match profile with
  | .boolean => { id := 0, name := "Value", groupPath := ["Form"], policy := { kind := .boolean } }
  | .date => temporal .date .fullDate "yyyy-MM-dd"
  | .time => temporal .time .time "HH:mm:ss"
  | .stamp => temporal .dateTime .now "yyyy-MM-dd'T'HH:mm:ss"
  | .fragment => temporal .date (TemporalComponents.ofFormat "MM") "MM"
  | .range => {
      id := 0, name := "Value", groupPath := ["Form"], policy := { kind := .dateRange }
      dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" } }
  | .custom => { id := 0, name := "Value", groupPath := ["Form"], policy := { kind := .string }, customType := some { name := "Code" } }

private def first : Profile → String
  | .boolean => "false" | .date => "2024-02-01" | .time => "03:04:05"
  | .stamp => "2024-02-01T03:04:05" | .fragment => "02" | .range => "2024-02-01/2024-02-02" | .custom => "alpha"
private def second : Profile → String
  | .boolean => "true" | .date => "2024-03-01" | .time => "06:07:08"
  | .stamp => "2024-03-01T06:07:08" | .fragment => "03" | .range => "2024-03-01/2024-03-02" | .custom => "beta"
private def fallback : Profile → String
  | .boolean => "true" | .date => "2024-04-01" | .time => "09:10:11"
  | .stamp => "2024-04-01T09:10:11" | .fragment => "04" | .range => "2024-04-01/2024-04-02" | .custom => "omega"
private def seed : Profile → String
  | .boolean => "true" | .date => "2000-01-01" | .time => "01:01:01"
  | .stamp => "2000-01-01T01:01:01" | .fragment => "01" | .range => "2000-01-01/2000-01-02" | .custom => "seed"

private def model (profile : Profile) : FlatModel :=
  let field (id : FieldId) (name : String) (path : GroupPath := ["Form"]) (scope : List RepeatableLevel := []) :=
    { prototype profile with id, name, groupPath := path, repeatableScope := scope }
  { fields := [field 1 "Out", field 2 "Fallback",
      { id := 3, name := "Key", groupPath := ["Form"], policy := { kind := .string } },
      { id := 4, name := "Id", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .string } },
      field 5 "Value" ["Form", "Rows"] [10], field 6 "Local" ["Form", "Rows"] [10],
      field 7 "Out" ["Form", "Rows"] [10], field 8 "Value" ["Form", "Rows", "Children"] [10,20],
      field 9 "Suffix", field 10 "Direct",
      field 11 "Zeta" ["Form", "Rows", "Body"] [10], field 12 "Alpha" ["Form", "Rows", "Body"] [10],
      field 13 "Zeta" ["Form", "Rows", "Body", "Slots"] [10,30],
      field 14 "Alpha" ["Form", "Rows", "Body", "Slots"] [10,30],
      field 15 "Zeta" ["Form", "Rows", "Mixed"] [10],
      { id := 16, name := "Alpha", groupPath := ["Form", "Rows", "Mixed"], repeatableScope := [10],
        policy := { kind := .number { scale := 0, signed := true } } }]
    repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 2, indexField := some 4 },
      { level := 20, path := ["Form", "Rows", "Children"], repeatability := some 3 },
      { level := 30, path := ["Form", "Rows", "Body", "Slots"], repeatability := some 3 }]
    timeZoneId := "UTC" }

private def world : World := {
  now := { epochMillis := 0 }
  customFieldValidator? := fun name => if name == "Code" then some (fun value _ =>
    if value == "bad" then some { projectCode := "BAD" } else none) else none }

private structure Scenario where
  key : String := "a"
  secondId : String := "b"
  selected : Option String := none
  suffix : Option String := none
  fallback : Option String := none
  outSeed : Option String := none
  children : Option (List String) := none
  localValue : Option String := none
  localEmpty : Bool := false
  omitted : Bool := false
  bodyZeta : Option String := none
  bodyAlpha : Option String := none
  secondBodyZeta : Option String := none
  slots : Option (List (String × String)) := none
  bodyOmitted : Bool := false
  rowsAbsent : Bool := false

private def input (profile : Profile) (scenario : Scenario) : Lean.Json :=
  let body (value : String) (selected : Bool) := Lean.Json.mkObj [
    ("Zeta", .str (if selected then scenario.bodyZeta.getD value else
      scenario.secondBodyZeta.getD (scenario.bodyZeta.getD value))),
    ("Alpha", .str (scenario.bodyAlpha.getD (second profile))),
    ("Slots", .arr ((scenario.slots.getD [(value, second profile)]).map fun pair =>
      Lean.Json.mkObj [("Zeta", .str pair.1), ("Alpha", .str pair.2)]).toArray)]
  let row (id value localText : String) (selected : Bool) := Lean.Json.mkObj
    ([("Id", .str id), ("Out", .str (scenario.outSeed.getD (seed profile))),
      ("Local", .str (if scenario.localEmpty then "" else scenario.localValue.getD localText)),
      ("Children", .arr ((scenario.children.getD [value]).map (fun child =>
        Lean.Json.mkObj [("Value", .str child)])).toArray)] ++
      (if scenario.bodyOmitted then [] else [("Body", body value selected)]) ++
      if selected && scenario.omitted then [] else [("Value", .str value)])
  Lean.Json.mkObj [("Form", Lean.Json.mkObj [
    ("Out", .str (scenario.outSeed.getD (seed profile))), ("Fallback", .str (scenario.fallback.getD (fallback profile))),
    ("Suffix", .str (scenario.suffix.getD (second profile))), ("Direct", .str (first profile)), ("Key", .str scenario.key),
    ("Rows", .arr (if scenario.rowsAbsent then #[] else
      #[row "a" (scenario.selected.getD (first profile)) (first profile) true,
        row scenario.secondId (second profile) (second profile) false]))])]

private def checked (profile : Profile) (scenario : Scenario := {}) : Option (CheckedDocument (model profile)) := do
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler (model profile)).toOption
  let raw ← (readDocument { flat := model profile, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
    (input profile scenario)).toOption
  (checkDocument prepared "en_US" raw.data).toOption

private def definition (operation : String) (repeated : Bool := false) (rowDeclared : Bool := false) : DmComputation := {
  name := "Selected", group := if rowDeclared then ["Form", "Rows"] else ["Form"]
  targetRelPath := if rowDeclared then "../Out" else if repeated then "../Rows/Out" else "../Out"
  commonPrecondition := none, alternatives := [{ precondition := none, operation }], errorCodesToSuppress := [] }

private def run (profile : Profile) (operation : String) (scenario : Scenario := {})
    (repeated : Bool := false) (produceKey : Bool := false) (rowDeclared : Bool := false) : Option (List ComputedOutcome) := do
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler (model profile)).toOption
  let document ← checked profile scenario
  let step ← (lowerComputation (model profile) .english (definition operation repeated rowDeclared)).toOption
  let producers ← if produceKey then do
    let producer ← (lowerComputation (model profile) .english
      { definition "\"b\"" with name := "KeyProducer", targetRelPath := "../Key" }).toOption
    pure [producer.2]
    else pure []
  let outcomes ← (runComputations world prepared document (step.2 :: producers)).toOption
  pure (outcomes.filter fun outcome => !outcome.pointer.endsWith "/Key")

private def expected (profile : Profile) (value : String) (repeated : Bool := false)
    (stored : Option String := none) : List ComputedOutcome :=
  if value == stored.getD (seed profile) then [] else
    (if repeated then ["Form/Rows/Out", "Form/Rows[2]/Out"] else ["Form/Out"]).map fun pointer =>
      { pointer, outcome := "value " ++ value }
private def cleared (repeated : Bool := false) : List ComputedOutcome :=
  (if repeated then ["Form/Rows/Out", "Form/Rows[2]/Out"] else ["Form/Out"]).map fun pointer => { pointer, outcome := "cleared" }

example : profiles.all (fun profile => [false,true].all fun repeated => ["Key", "\"a\""].all fun key =>
    ["Rows/Value For ", "Rows/Children*/Value For "].all fun source =>
      let operation := "FirstFilledValue(" ++ source ++ key ++ (if source == "Rows/Value For " then ",Fallback)" else ")")
      run profile operation {} repeated == some (expected profile (first profile) repeated)) = true := by native_decide

example : profiles.all (fun profile => [false,true].all fun repeated =>
    run profile "FirstFilledValue(Rows/Value For Key,Fallback)" { key := "b" } repeated ==
      some (expected profile (second profile) repeated) &&
    ["missing", ""].all (fun key =>
      run profile "FirstFilledValue(Rows/Value For Key,Fallback)" { key, outSeed := some (first profile) } repeated ==
        some (expected profile (fallback profile) repeated (some (first profile))) &&
      run profile "FirstFilledValue(Rows/Children*/Value For Key)" { key } repeated == some (cleared repeated))) = true := by native_decide

example : profiles.all (fun profile => [false,true].all fun repeated =>
    run profile "FirstFilledValue(Rows/Value For Key,Fallback)" { selected := some "", outSeed := some (first profile) } repeated ==
      some (expected profile (fallback profile) repeated (some (first profile))) &&
    run profile "FirstFilledValue(Rows/Value For Key,Fallback)" { omitted := true, outSeed := some (first profile) } repeated ==
      some (expected profile (fallback profile) repeated (some (first profile))) &&
    run profile "FirstFilledValue(Rows/Value For Key,Fallback)" { selected := some "bad" } repeated == some (cleared repeated) &&
    run profile "FirstFilledValue(Rows/Value For Key,Fallback)" { secondId := "a" } repeated == some (cleared repeated) &&
    run profile "FirstFilledValue(Rows/Children*/Value For Key)" { children := some [] } repeated == some (cleared repeated)) = true := by native_decide

example : profiles.all (fun profile => [false,true].all fun repeated =>
    run profile "FirstFilledValue(Rows/Value For Key,Fallback)" { selected := some "", fallback := some "" } repeated == some (cleared repeated) &&
    run profile "FirstFilledValue(Rows/Children*/Value For Key)" { children := some ["", first profile, "bad"] } repeated ==
      some (expected profile (first profile) repeated) &&
    run profile "FirstFilledValue(Rows/Children*/Value For Key)" { children := some ["bad", first profile] } repeated == some (cleared repeated) &&
    run profile "FirstFilledValue(Rows/Value For Key,Suffix)" { suffix := some "bad" } repeated ==
      some (expected profile (first profile) repeated)) = true := by native_decide

example : profiles.all (fun profile =>
    let localExpected := expected profile (first profile) true |>.filter (·.pointer == "Form/Rows/Out")
    let secondExpected := expected profile (second profile) true |>.filter (·.pointer == "Form/Rows[2]/Out")
    run profile "FirstFilledValue(Rows/Local,Rows/Value For Key)" { secondId := "a" } true == some (localExpected ++ secondExpected) &&
    run profile "FirstFilledValue(Rows/Local,Rows/Value For Key)" { secondId := "a", localEmpty := true } true == some (cleared true) &&
    run profile "FirstFilledValue(Direct,Fallback)" == some (expected profile (first profile))) = true := by native_decide

private def admitted (profile : Profile) (operation : String) (repeated : Bool := false) : Bool :=
  (lowerComputation (model profile) .english (definition operation repeated)).isOk

example : profiles.all (fun profile =>
    !admitted profile "FirstFilledValue(Rows/Value For Key)" &&
    !admitted profile "FirstFilledValue(Rows/Value For Key,Out)" &&
    !admitted profile "FirstFilledValue(Rows/Out For Key,Fallback)" true &&
    !admitted profile "FirstFilledValue(Rows For Key,Fallback)" &&
    !admitted profile "FirstFilledValue(Rows/Children*/Value For Key Having FieldFilled(Key))") = true := by native_decide

private def siteFor (profile : Profile) (operation : String) : Option (CheckedFirstFilledSite (model profile)) := do
  let parsed ← (parseText .english operation).toOption
  let .call "FirstFilledValue" arguments none none := parsed.body | none
  let source ← (lowerFirstFilledSource (model profile) ["Form"] arguments).toOption
  (checkFirstFilledSite (model profile) ["Form"] 1 source).toOption

private def dependencies (operation : String) : Option (List FieldId) := do
  let site ← siteFor .boolean operation
  pure ((model .boolean).fields.filterMap fun field => if site.referencesField field.id then some field.id else none)

example : dependencies "FirstFilledValue(Rows/Value For Key,Fallback)" = some [2,3,4,5] ∧
    dependencies "FirstFilledValue(Rows/Value For \"a\",Fallback)" = some [2,4,5] ∧
    dependencies "FirstFilledValue(Rows/Children*/Value For Key)" = some [3,4,8] := by native_decide

private def eagerSuffixFinding (profile : Profile) : Option Bool := do
  let site ← siteFor profile "FirstFilledValue(Rows/Value For Key,Suffix)"
  let document ← checked profile { suffix := some "bad" }
  let plan ← site.formalInputPlan.toOption
  let prepared ← (plan.prepare document).toOption
  pure (prepared.formalErrorsInOperands.any fun finding => finding.address == { field := 9, path := [] })

example : profiles.all (fun profile => eagerSuffixFinding profile == some true) = true := by native_decide

private def resolveWithFailure (operation : String) (field : FieldId)
    (scenario : Scenario := {}) (failurePath : Option (List Nat) := none) :
    Option (Except CheckedAddressingError (Except FormalCause ResolvedFirstFilledSource)) := do
  let site ← siteFor .boolean operation
  let document ← checked .boolean scenario
  pure (site.source.resolveAt document (fun address => if address.field == field && failurePath.all (· == address.path) then
    .error (.incoherentCell address) else document.read address) [])

private def resolutionTag (result : Option (Except CheckedAddressingError (Except FormalCause ResolvedFirstFilledSource))) : String :=
  match result with
  | some (.error _) => "fault"
  | some (.ok (.error .duplicateIndex)) => "duplicate"
  | some (.ok (.error _)) => "poison"
  | some (.ok (.ok source)) => if source.cells.isEmpty then "empty" else "value"
  | none => "refused"

example : resolutionTag (resolveWithFailure "FirstFilledValue(Rows/Value For Key,Suffix)" 9) = "value" ∧
    resolutionTag (resolveWithFailure "FirstFilledValue(Rows/Value For Key,Suffix)" 5) = "fault" ∧
    resolutionTag (resolveWithFailure "FirstFilledValue(Rows/Value For Key,Suffix)" 9 { key := "missing" }) = "fault" ∧
    resolutionTag (resolveWithFailure "FirstFilledValue(Rows/Value For Key,Suffix)" 9 { secondId := "a" }) = "duplicate" := by native_decide

example : resolutionTag (resolveWithFailure "FirstFilledValue(Rows/Value For Key,Suffix)" 3) = "fault" ∧
    resolutionTag (resolveWithFailure "FirstFilledValue(Rows/Children*/Value For Key)" 3) = "fault" := by native_decide

example : profiles.all (fun profile => [false,true].all fun repeated =>
    run profile "FirstFilledValue(Rows/Value For Key,Fallback)"
      { outSeed := some (first profile) } repeated true ==
      some (expected profile (second profile) repeated (some (first profile)))) = true := by native_decide

example : profiles.all (fun profile => [false,true].all fun repeated =>
    run profile "FirstFilledValue(Rows/Children*/Value For Key)"
      { children := some ["", "", "", first profile] } repeated == some (cleared repeated) &&
    run profile "FirstFilledValue(Rows/Children*/Value For Key)"
      { children := some ["", "", first profile, "bad"] } repeated ==
      some (expected profile (first profile) repeated)) = true := by native_decide

example : resolutionTag (resolveWithFailure "FirstFilledValue(Rows/Children*/Value For Key)" 8
    { children := some ["false", "true"] } (some [1,2])) = "value" ∧
    resolutionTag (resolveWithFailure "FirstFilledValue(Rows/Children*/Value For Key)" 8
      { children := some ["", "true"] } (some [1,2])) = "fault" := by native_decide

private def groupSources : List String := ["Rows/Body", "Rows/Body/Slots*"]

private def groupOperation (source : String) (key : String := "Key") (withFallback : Bool := true) : String :=
  "FirstFilledValue(" ++ source ++ " For " ++ key ++ (if withFallback then ",Fallback)" else ")")

example : profiles.all (fun profile => [false,true].all fun repeated => groupSources.all fun source =>
    ["Key", "\"a\""].all fun key => [false,true].all fun withFallback =>
      run profile (groupOperation source key withFallback) {} repeated ==
        some (expected profile (first profile) repeated)) = true := by native_decide

example : profiles.all (fun profile => [false,true].all fun repeated =>
    run profile (groupOperation "Rows/Body") { bodyZeta := some "", bodyAlpha := some (second profile), slots := some [] }
      repeated == some (expected profile (second profile) repeated) &&
    run profile (groupOperation "Rows/Body") { bodyZeta := some "", bodyAlpha := some "" }
      repeated == some (expected profile (first profile) repeated) &&
    groupSources.all (fun source => run profile (groupOperation source)
      { bodyZeta := some "", bodyAlpha := some "", slots := some [("", second profile), (first profile, "")] }
      repeated == some (expected profile (first profile) repeated))) = true := by native_decide

example : profiles.all (fun profile => [false,true].all fun repeated => groupSources.all fun source =>
    run profile (groupOperation source) { key := "b" } repeated ==
      some (expected profile (second profile) repeated) &&
    ["missing", ""].all (fun key =>
      run profile (groupOperation source) { key, outSeed := some (first profile) } repeated ==
        some (expected profile (fallback profile) repeated (some (first profile))) &&
      run profile (groupOperation source "Key" false) { key } repeated == some (cleared repeated)) &&
    run profile (groupOperation source) { bodyOmitted := true, outSeed := some (first profile) } repeated ==
      some (expected profile (fallback profile) repeated (some (first profile))) &&
    run profile (groupOperation source "Key" false) { bodyOmitted := true } repeated == some (cleared repeated) &&
    run profile (groupOperation source) { bodyZeta := some "", bodyAlpha := some "", slots := some [], fallback := some "" }
      repeated == some (cleared repeated) &&
    run profile (groupOperation source) { secondId := "a" } repeated == some (cleared repeated) &&
    run profile (groupOperation source) { bodyZeta := some "bad", slots := some [("bad", second profile)] }
      repeated == some (cleared repeated)) = true := by native_decide

example : profiles.all (fun profile => [false,true].all fun repeated =>
    run profile (groupOperation "Rows/Body") { bodyAlpha := some "bad" } repeated ==
      some (expected profile (first profile) repeated) &&
    groupSources.all (fun source =>
      run profile (groupOperation source) { rowsAbsent := true, outSeed := some (first profile) } repeated ==
        some (if repeated then [] else expected profile (fallback profile) false (some (first profile))))) = true := by native_decide

example : profiles.all (fun profile => groupSources.all fun source =>
    let localExpected := expected profile (first profile) true |>.filter (·.pointer == "Form/Rows/Out")
    let secondExpected := expected profile (second profile) true |>.filter (·.pointer == "Form/Rows[2]/Out")
    run profile ("FirstFilledValue(Rows/Local," ++ source ++ " For Key)") { secondId := "a" } true ==
      some (localExpected ++ secondExpected) &&
    run profile ("FirstFilledValue(Rows/Local," ++ source ++ " For Key)")
      { secondId := "a", localEmpty := true } true == some (cleared true)) = true := by native_decide

private def selfGroupRefused (profile : Profile) (operation : String := groupOperation "Rows/Body") : Bool :=
  let nested := { model profile with fields := (model profile).fields.map fun field =>
    if field.id == 7 then { field with groupPath := ["Form", "Rows", "Body"] } else field }
  !(lowerComputation nested .english
    { definition operation true with targetRelPath := "../Rows/Body/Out" }).isOk

example : profiles.all (fun profile => [false,true].all (fun repeated =>
    !admitted profile (groupOperation "Rows/Mixed") repeated) && selfGroupRefused profile) = true := by native_decide

example : dependencies (groupOperation "Rows/Body") = some [2,3,4,11,12,13,14] ∧
    dependencies (groupOperation "Rows/Body" "\"a\"") = some [2,4,11,12,13,14] ∧
    dependencies (groupOperation "Rows/Body/Slots*") = some [2,3,4,13,14] := by native_decide

private def eagerGroupFinding (profile : Profile) : Option Bool := do
  let site ← siteFor profile (groupOperation "Rows/Body")
  let document ← checked profile { bodyAlpha := some "bad" }
  let plan ← site.formalInputPlan.toOption
  let prepared ← (plan.prepare document).toOption
  pure (prepared.formalErrorsInOperands.any fun finding => finding.address == { field := 12, path := [1] })

example : profiles.all (fun profile => eagerGroupFinding profile == some true) = true := by native_decide

private def exactFailure (operation : String) (field : FieldId) (path : List Nat) (scenario : Scenario) : Bool :=
  match resolveWithFailure operation field scenario (some path) with
  | some (.error (.document (.incoherentCell address))) => address == { field, path }
  | _ => false

example : resolutionTag (resolveWithFailure (groupOperation "Rows/Body") 12 {} (some [1])) = "value" ∧
    exactFailure (groupOperation "Rows/Body") 12 [1] { bodyZeta := some "" } = true ∧
    resolutionTag (resolveWithFailure (groupOperation "Rows/Body/Slots*") 13
      { slots := some [("false", "true"), ("true", "false")] } (some [1,2])) = "value" ∧
    exactFailure (groupOperation "Rows/Body/Slots*") 13 [1,2]
      { slots := some [("", "true"), ("false", "")] } = true ∧
    resolutionTag (resolveWithFailure (groupOperation "Rows/Body/Slots*") 14
      { slots := some [("", "true"), ("false", "")] } (some [1,1])) = "value" ∧
    exactFailure (groupOperation "Rows/Body/Slots*") 14 [1,1]
      { slots := some [("", "true"), ("", "false")] } = true := by native_decide

example : profiles.all (fun profile => [false,true].all fun repeated =>
    run profile (groupOperation "Rows/Body/Slots*" "Key" false)
      { slots := some [("", ""), ("", ""), ("", ""), (first profile, "")] } repeated == some (cleared repeated) &&
    run profile (groupOperation "Rows/Body/Slots*" "Key" false)
      { slots := some [("", ""), ("", ""), (first profile, ""), ("bad", "bad")] } repeated ==
        some (expected profile (first profile) repeated)) = true := by native_decide

example : profiles.all (fun profile => ["Body", "Body/Slots*"].all fun source =>
    run profile ("FirstFilledValue(" ++ source ++ " For ../Key,../Fallback)") {} true false true ==
      some (expected profile (first profile) true)) = true := by native_decide

example : profiles.all (fun profile => [false,true].all fun repeated =>
    run profile "FirstFilledValue(Rows/Value For Key,Rows*/Local)" {} repeated ==
      some (expected profile (first profile) repeated) &&
    run profile "FirstFilledValue(Rows/Value For Key,Rows*/Local)" { key := "missing" } repeated ==
      some (expected profile (first profile) repeated)) = true := by native_decide

example : profiles.all (fun profile =>
    run profile "FirstFilledValue(Rows/Value For Key,Rows*/Body)" { key := "missing" } ==
      some (expected profile (first profile))) = true := by native_decide

private def ordinarySources : List String := ["Rows*/Local", "Rows*/Body", "Rows*/Body/Slots*"]

private def mixedOperation (ordinary : String) (ordinaryFirst : Bool := false) : String :=
  "FirstFilledValue(" ++ (if ordinaryFirst then ordinary ++ ",Rows/Value For Key" else
    "Rows/Value For Key," ++ ordinary) ++ ")"

private def emptyOrdinary (selected : Option String := none) : Scenario := {
  selected, localEmpty := true, bodyZeta := some "", bodyAlpha := some "", slots := some [("", "")] }

example : profiles.all (fun profile => [false,true].all fun repeated => ordinarySources.all fun source =>
    run profile (mixedOperation source) { key := "b" } repeated ==
      some (expected profile (second profile) repeated) &&
    run profile (mixedOperation source true) { key := "b" } repeated ==
      some (expected profile (first profile) repeated) &&
    run profile (mixedOperation source) { key := "missing" } repeated ==
      some (expected profile (first profile) repeated) &&
    run profile (mixedOperation source true) (emptyOrdinary) repeated ==
      some (expected profile (first profile) repeated) &&
    [false,true].all (fun ordinaryFirst =>
      run profile (mixedOperation source ordinaryFirst) (emptyOrdinary (some "")) repeated ==
        some (cleared repeated))) = true := by native_decide

example : profiles.all (fun profile => [false,true].all fun repeated =>
    run profile (mixedOperation "Rows*/Local") { localValue := some "bad" } repeated ==
      some (expected profile (first profile) repeated) &&
    run profile (mixedOperation "Rows*/Local" true) { localValue := some "bad" } repeated == some (cleared repeated) &&
    run profile (mixedOperation "Rows*/Local") { selected := some "", localValue := some "bad" } repeated == some (cleared repeated) &&
    ordinarySources.all (fun source =>
      run profile (mixedOperation source true) { secondId := "a" } repeated ==
        some (expected profile (first profile) repeated) &&
      run profile (mixedOperation source) { secondId := "a" } repeated == some (cleared repeated)) &&
    ["Rows*/Body", "Rows*/Body/Slots*"].all (fun source =>
      let poisoned := { bodyZeta := some "bad", slots := some [("bad", second profile)] : Scenario }
      run profile (mixedOperation source) poisoned repeated == some (expected profile (first profile) repeated) &&
      run profile (mixedOperation source true) poisoned repeated == some (cleared repeated))) = true := by native_decide

example : profiles.all (fun profile => [false,true].all fun repeated =>
    run profile (mixedOperation "Rows*/Body" true)
      { bodyZeta := some "", secondBodyZeta := some (first profile), bodyAlpha := some (second profile), slots := some [] }
      repeated == some (expected profile (first profile) repeated) &&
    ["Rows*/Body", "Rows*/Body/Slots*"].all (fun source =>
      run profile (mixedOperation source true)
        { bodyZeta := some "", bodyAlpha := some "", slots := some [("", second profile), (first profile, "")] }
        repeated == some (expected profile (first profile) repeated) &&
      run profile (mixedOperation source true) { bodyOmitted := true } repeated ==
        some (expected profile (first profile) repeated) &&
      run profile (mixedOperation source true)
        { bodyZeta := some "", bodyAlpha := some "", slots := some [("", ""), ("", ""), ("", ""), ("bad", "bad")] }
        repeated == some (expected profile (first profile) repeated) &&
      run profile (mixedOperation source true)
        { key := "missing", bodyZeta := some "", bodyAlpha := some "",
          slots := some [("", ""), ("", ""), ("", ""), (first profile, "")] }
        repeated == some (cleared repeated))) = true := by native_decide

example : profiles.all (fun profile => ["Body", "Body/Slots*"].all fun source =>
    let ordinaryExpected := (expected profile (first profile) true).filter (·.pointer == "Form/Rows/Out") ++
      (expected profile (second profile) true).filter (·.pointer == "Form/Rows[2]/Out")
    run profile ("FirstFilledValue(" ++ source ++ " For ../Key," ++ source ++ ")") { key := "b" }
      true false true == some (expected profile (second profile) true) &&
    run profile ("FirstFilledValue(" ++ source ++ "," ++ source ++ " For ../Key)") { key := "b" }
      true false true == some ordinaryExpected &&
    run profile ("FirstFilledValue(" ++ source ++ " For ../Key," ++ source ++ ")") { key := "missing" }
      true false true == some ordinaryExpected &&
    run profile ("FirstFilledValue(" ++ source ++ ",Value For ../Key)") { bodyOmitted := true }
      true false true == some (expected profile (first profile) true)) = true := by native_decide

example : exactFailure (mixedOperation "Rows*/Local" true) 6 [1] {} = true ∧
    resolutionTag (resolveWithFailure (mixedOperation "Rows*/Local") 6 {} (some [1])) = "value" ∧
    exactFailure (mixedOperation "Rows*/Local") 6 [1] { key := "missing" } = true ∧
    resolutionTag (resolveWithFailure (mixedOperation "Rows*/Local" true) 3) = "value" ∧
    exactFailure (mixedOperation "Rows*/Local") 3 [] {} = true ∧
    resolutionTag (resolveWithFailure (mixedOperation "Rows*/Local" true) 4 {} (some [1])) = "value" ∧
    exactFailure (mixedOperation "Rows*/Local" true) 3 [] { localEmpty := true } = true := by native_decide

-- Index fields cannot be computation targets (spec/09 §1); selection uses their prepared
-- immutable column rather than the dependency overlay, unlike reached key and payload reads.
example : resolutionTag (resolveWithFailure (mixedOperation "Rows*/Local") 4 {} (some [1])) =
    "value" := by native_decide

example : exactFailure (mixedOperation "Rows*/Body" true) 11 [1] {} = true ∧
    resolutionTag (resolveWithFailure (mixedOperation "Rows*/Body") 11 {} (some [1])) = "value" ∧
    resolutionTag (resolveWithFailure (mixedOperation "Rows*/Body" true) 12 {} (some [1])) = "value" ∧
    exactFailure (mixedOperation "Rows*/Body" true) 12 [1]
      { bodyZeta := some "", slots := some [] } = true ∧
    resolutionTag (resolveWithFailure (mixedOperation "Rows*/Body/Slots*" true) 13
      { slots := some [("false", "true"), ("true", "false")] } (some [1,2])) = "value" ∧
    exactFailure (mixedOperation "Rows*/Body/Slots*" true) 13 [1,2]
      { slots := some [("", "true"), ("false", "")] } = true ∧
    resolutionTag (resolveWithFailure (mixedOperation "Rows*/Body/Slots*" true) 14
      { slots := some [("", "true"), ("false", "")] } (some [1,1])) = "value" ∧
    exactFailure (mixedOperation "Rows*/Body/Slots*" true) 14 [1,1]
      { slots := some [("", "true"), ("", "false")] } = true := by native_decide

example : dependencies (mixedOperation "Rows*/Local") = some [3,4,5,6] ∧
    dependencies (mixedOperation "Rows*/Local" true) = some [3,4,5,6] ∧
    dependencies (mixedOperation "Rows*/Body") = some [3,4,5,11,12,13,14] ∧
    dependencies (mixedOperation "Rows*/Body/Slots*") = some [3,4,5,13,14] ∧
    dependencies "FirstFilledValue(Rows/Value For \"a\",Rows*/Body)" = some [4,5,11,12,13,14] := by native_decide

example : profiles.all (fun profile => [false,true].all (fun repeated =>
    !admitted profile (mixedOperation "Rows*/Mixed") repeated &&
    !admitted profile "FirstFilledValue(Rows/Value For Key,Rows*/Out)" true) &&
    selfGroupRefused profile (mixedOperation "Rows*/Body")) = true := by native_decide

end A12Kernel.Dm.SelectedFirstFilledLocks
