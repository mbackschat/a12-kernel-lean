import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.Validate

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
        policy := { kind := .number { scale := 0, signed := true } } },
      { id := 17, name := "Allow", groupPath := ["Form", "Rows"], repeatableScope := [10],
        policy := { kind := .number { scale := 0, signed := true } } },
      { id := 18, name := "Allow", groupPath := ["Form", "Rows", "Children"], repeatableScope := [10,20],
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
  allows : List String := ["1", "1"]
  childAllows : Option (List String) := none
  localValue : Option String := none
  secondLocalValue : Option String := none
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
      ("Local", .str (if scenario.localEmpty then "" else if selected then scenario.localValue.getD localText else
        scenario.secondLocalValue.getD (scenario.localValue.getD localText))),
      ("Allow", .str ((scenario.allows[if selected then 0 else 1]?).getD "1")),
      ("Children", .arr ((scenario.children.getD [value]).zipIdx.map (fun (child, index) =>
        Lean.Json.mkObj [("Value", .str child),
          ("Allow", .str (((scenario.childAllows.getD ["1"])[index]?).getD "1"))])).toArray)] ++
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
    (repeated : Bool := false) (produceKey : Bool := false) (rowDeclared : Bool := false)
    (evaluationWorld : World := world) (produceAllow : Bool := false) : Option (List ComputedOutcome) := do
  let prepared ← (prepareFlatStringContext evaluationWorld builtinStringPatternCompiler (model profile)).toOption
  let document ← checked profile scenario
  let step ← (lowerComputation (model profile) .english (definition operation repeated rowDeclared)).toOption
  let producers ← if produceKey then do
    let producer ← (lowerComputation (model profile) .english
      { definition "\"b\"" with name := "KeyProducer", targetRelPath := "../Key" }).toOption
    pure [producer.2]
    else pure []
  let allowProducers ← if produceAllow then do
    let producer ← (lowerComputation (model profile) .english
      { definition "1" true with name := "AllowProducer", targetRelPath := "../Rows/Allow" }).toOption
    pure [producer.2]
    else pure []
  let outcomes ← (runComputations evaluationWorld prepared document (step.2 :: (producers ++ allowProducers))).toOption
  pure (outcomes.filter fun outcome => !outcome.pointer.endsWith "/Key" && !outcome.pointer.endsWith "/Allow")

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

private def filteredLocal : String := "Rows*/Local Having [Rows/Allow] > 0"

private def filteredOperation (suffix : String := "") : String :=
  "FirstFilledValue(" ++ filteredLocal ++ (if suffix.isEmpty then ")" else "," ++ suffix ++ ")")

example : profiles.all (fun profile => [false,true].all fun repeated =>
    ["", "Fallback", "Rows*/Body", "Rows/Value For Key"].all (fun suffix =>
      run profile (filteredOperation suffix) {} repeated == some (expected profile (first profile) repeated)) &&
    run profile ("FirstFilledValue(Rows/Value For Key," ++ filteredLocal ++ ")") { key := "b" } repeated ==
      some (expected profile (second profile) repeated) &&
    run profile (filteredOperation "Rows/Value For Key") { key := "b" } repeated ==
      some (expected profile (first profile) repeated) &&
    run profile (filteredOperation "Fallback") { allows := ["0", "0"] } repeated ==
      some (expected profile (fallback profile) repeated) &&
    run profile (filteredOperation) { allows := ["0", "0"] } repeated == some (cleared repeated) &&
    run profile (filteredOperation "Rows/Value For Key") { allows := ["0", "0"], key := "b" } repeated ==
      some (expected profile (second profile) repeated) &&
    run profile (filteredOperation "Rows/Value For Key") { allows := ["0", "0"], key := "missing" } repeated ==
      some (cleared repeated) &&
    run profile (filteredOperation) { localValue := some "", secondLocalValue := some (second profile) } repeated ==
      some (expected profile (second profile) repeated)) = true := by native_decide

example : profiles.all (fun profile => [false,true].all fun repeated =>
    run profile (filteredOperation "Fallback") { allows := ["1", "bad"] } repeated == some (cleared repeated) &&
    run profile ("FirstFilledValue(Rows/Value For Key," ++ filteredLocal ++ ")") { allows := ["1", "bad"] } repeated ==
      some (expected profile (first profile) repeated) &&
    run profile ("FirstFilledValue(Rows*/Body," ++ filteredLocal ++ ")") { allows := ["1", "bad"] } repeated ==
      some (expected profile (first profile) repeated) &&
    run profile ("FirstFilledValue(Direct," ++ filteredLocal ++ ")") { allows := ["1", "bad"] } repeated ==
      some (expected profile (first profile) repeated) &&
    run profile (filteredOperation) { localValue := some "bad", secondLocalValue := some (second profile), allows := ["0", "1"] } repeated ==
      some (expected profile (second profile) repeated) &&
    run profile (filteredOperation) { localValue := some "bad" } repeated == some (cleared repeated) &&
    run profile (filteredOperation) { secondLocalValue := some "bad" } repeated ==
      some (expected profile (first profile) repeated)) = true := by native_decide

private def childFilteredOperation : String :=
  "FirstFilledValue(Rows/Children*/Value Having [Rows/Children/Allow] > 0)"

example : profiles.all (fun profile =>
    run profile childFilteredOperation
      { children := some [first profile, second profile, "bad"], childAllows := some ["1", "1", "bad"] } true ==
      some (expected profile (first profile) true) &&
    run profile childFilteredOperation
      { children := some [first profile, second profile, first profile], childAllows := some ["1", "bad", "1"] } true ==
      some (cleared true) &&
    run profile childFilteredOperation { children := some ["", second profile, first profile] } true ==
      some (expected profile (second profile) true) &&
    run profile childFilteredOperation
      { children := some ["", "", "", first profile], childAllows := some ["1", "1", "1", "1"] } true ==
      some (cleared true) &&
    run profile childFilteredOperation
      { children := some [first profile, second profile, first profile, "bad"], childAllows := some ["1", "1", "1", "bad"] }
      true == some (expected profile (first profile) true)) = true := by native_decide

example : profiles.all (fun profile =>
    let firstTarget := (expected profile (second profile) true).filter (·.pointer == "Form/Rows/Out")
    let secondTarget := (expected profile (first profile) true).filter (·.pointer == "Form/Rows[2]/Out")
    run profile "FirstFilledValue(Rows*/Local Having [Rows/Allow] > [$Rows/Allow],Fallback)"
      { allows := ["1", "2"], fallback := some (first profile) } true ==
      some (firstTarget ++ secondTarget)) = true := by native_decide

private def clockFilteredOperation : String :=
  "FirstFilledValue(Rows*/Local Having [Rows/Allow] > 0 And DifferenceInDays(Today, \"01.01.1970\") == 0)"

example : profiles.all (fun profile => [false,true].all fun repeated =>
    run profile clockFilteredOperation {} repeated == some (expected profile (first profile) repeated) &&
    run profile clockFilteredOperation {} repeated false false { world with now := { epochMillis := 86400000 } } ==
      some (cleared repeated) &&
    run profile (filteredOperation) { allows := ["0", "0"] } repeated false false world true ==
      some (expected profile (first profile) repeated)) = true := by native_decide

example : exactFailure (filteredOperation) 17 [2] {} = true ∧
    resolutionTag (resolveWithFailure ("FirstFilledValue(Rows/Value For Key," ++ filteredLocal ++ ")")
      17 {} (some [2])) = "value" ∧
    resolutionTag (resolveWithFailure (filteredOperation) 6 {} (some [2])) = "value" ∧
    exactFailure (filteredOperation) 6 [1] {} = true ∧
    resolutionTag (resolveWithFailure (filteredOperation) 6 { allows := ["0", "1"] } (some [1])) = "value" := by native_decide

example : dependencies (filteredOperation "Fallback") = some [2,6,17] ∧
    dependencies ("FirstFilledValue(Rows/Value For Key," ++ filteredLocal ++ ")") = some [3,4,5,6,17] ∧
    dependencies clockFilteredOperation = some [6,17] := by native_decide

example : profiles.all (fun profile =>
    !admitted profile "FirstFilledValue(Rows*/Local Having FieldFilled(Out),Fallback)" &&
    !admitted profile "FirstFilledValue(Rows*/Local Having FieldFilled(Rows/Out),Fallback)" true &&
    !admitted profile "FirstFilledValue(Rows/Value For Key Having [Rows/Allow] > 0,Fallback)") = true := by native_decide

example : profiles.all (fun profile =>
    run profile "FirstFilledValue(Rows*/Body,Fallback)" {} == some (expected profile (first profile)) &&
    run profile "FirstFilledValue(Rows*/Local,Fallback)" {} == some (expected profile (first profile))) = true := by native_decide

example : profiles.all (fun profile =>
    let parentValues := (expected profile (first profile) true).filter (·.pointer == "Form/Rows/Out") ++
      (expected profile (second profile) true).filter (·.pointer == "Form/Rows[2]/Out")
    run profile "FirstFilledValue(Children*/Value Having [Children/Allow] > 0)" {}
      true false true == some parentValues &&
    !admitted profile "FirstFilledValue(Rows*/Local Having [Rows/Allow] > [$Rows/Allow],Fallback)" false) = true := by native_decide

private def temporalCompanion (profile : Profile) (companion : String)
    (scenario : Scenario := {}) (reverse : Bool := false)
    (partialScope : Option ValidationRelevanceScope := none)
    (selected : String := "FirstFilledValue(Rows/Value For Key,Fallback)") : Option (List Verdict) := do
  let document ← checked profile scenario
  let (left, right) := if reverse then (companion, selected) else (selected, companion)
  let dm : DmModel := {
    flat := model profile, rules := [], computations := [],
    conditionLanguage := "en_US", refusals := [] }
  let rule ← (checkRule dm .english {
    group := ["Form"], name := "Companion", errorCode := "COMPANION",
    errorEntityRelPath := "../Out", severity := "ERROR",
    condition := "FieldFilled(Out) And (" ++ left ++ " == " ++ right ++ ")" }).toOption
  if let some scope := partialScope then
    match ← (rule.evalAddressedPartial document scope (some world)).toOption with
    | .skipped => return []
    | .evaluated outcome => return [outcome.verdict]
  let context : AddressedValidationEvaluationContext (model profile) := {
    scalar := { fields := document.flatContext.withWorld world, groups := GroupPresenceContext.unavailable },
    outer := [], input := .checked document }
  pure [(← (rule.evalAddressedFull context true).toOption).verdict]

private def companions : List (Profile × String × Verdict) := [
  (.date, "AddDays(Rows/Value For Key,0)", .fired .value),
  (.date, "AddDays(Rows/Value For Key,1)", .notFired),
  (.date, "AddDays(Rows/Value For \"b\",0)", .notFired),
  (.stamp, "AddHours(Rows/Value For Key,0)", .fired .value),
  (.time, "MinValue(Rows/Children*/Value For Key)", .fired .omission),
  (.date, "MinValue(Rows/Children*/Value For Key)", .fired .omission),
  (.date, "MinValue(Rows/Value For Key,Rows/Local For \"b\")", .fired .value),
  (.date, "Date(\"1\",\"2\",YearFromDate(Rows/Value For Key))", .fired .value)]

example : companions.all (fun (profile, companion, expected) =>
    [false,true].all (fun reverse => [none, some ValidationRelevanceScope.full].all fun scope =>
      temporalCompanion profile companion {} reverse scope == some [expected])) = true := by native_decide

example : [false,true].all (fun reverse => [none, some ValidationRelevanceScope.full].all fun scope =>
    temporalCompanion .date "AddDays(Rows/Value For \"b\",0)" { key := "b" } reverse scope ==
      some [.fired .value] &&
    temporalCompanion .date "AddDays(Rows/Value For \"b\",0)" { key := "missing", fallback := some (second .date) } reverse scope ==
      some [.fired .omission] &&
    temporalCompanion .date "AddDays(Rows/Value For Key,0)" { selected := some "bad" } reverse scope ==
      some [.unknown] &&
    temporalCompanion .date "AddDays(Rows/Value For Key,0)" { secondId := "a" } reverse scope ==
      some [.unknown]) = true := by native_decide

example : temporalCompanion .date "AddDays(Rows/Value For Key,0)" {} false
    (some (.partialSet [])) = some [] := by native_decide

private def companionBindings (text : String) : Option (List FieldId) := do
  let parsed ← (parseText .english text).toOption
  let surface ← (lowerScalarTemporalExpression (model .date) ["Form"] parsed.body).toOption
  let checked ← (elaborateScalarTemporalExpression (model .date) ["Form"] surface).toOption
  pure checked.boundFieldIds

example : companionBindings "MinValue(Rows/Children*/Value For Key)" = some [3] ∧
    companionBindings "MinValue(Rows/Children*/Value For \"a\")" = some [] ∧
    companionBindings "MinValue(Rows/Value For Key,Rows/Local For \"b\")" = some [3] := by native_decide

private def companionScope : ValidationRelevanceScope :=
  .partialSet (["Out", "Fallback", "Direct", "Key"].map fun field =>
    { path := ["Form", field], indices := [.all, .all] })

example : temporalCompanion .date "AddDays(Rows/Value For Key,0)" {} false
      (some .full) "FirstFilledValue(Fallback,Direct)" = some [.notFired] ∧
    temporalCompanion .date "AddDays(Rows/Value For Key,0)" {} false
      (some companionScope) "FirstFilledValue(Fallback,Direct)" = some [.unknown] ∧
    temporalCompanion .date "AddDays(Rows/Value For \"b\",0)" { key := "missing", fallback := some (second .date) }
      false (some .full) "FirstFilledValue(Fallback,Direct)" = some [.fired .value] := by native_decide

example : [false,true].all (fun reverse =>
    temporalCompanion .date "MinValue(Rows*/Value Having FieldFilled(Rows/Value))" {} reverse ==
      some [.fired .omission] &&
    temporalCompanion .date "MinValue(Rows*/Value Having FieldFilled(Rows/Value))" {} reverse
      (some .full) == some []) = true := by native_decide

private def temporalCurrentRead (unavailable : Bool) (fail : Bool := false) :
    Option (Except (Sum CheckedAddressingError ScalarTemporalEvaluationFault) Verdict) := do
  let document ← checked .date
  let current ← checked .date { selected := some (fallback .date) }
  let parsed ← (parseText .english
    "FirstFilledValue(Fallback,Direct) == AddDays(Rows/Value For Key,0)").toOption
  let condition ← (lowerCondition (model .date) ["Form"] false parsed.body).toOption
  let .leaf (.firstFilledComparison comparison) := condition.core | none
  let result ← comparison.evaluatePartial? document [] document.flatContext .full fun row field =>
    if field == 5 && fail then throw (.checkedDocumentRequired ["Form", "Rows"])
    else if field == 5 && unavailable then pure none
    else ((if field == 5 then current else document).fullValidationAddressedCell row field).map
      (fun addressed => some addressed.cell)
  pure result

private def temporalCurrentEffects : Bool :=
  match temporalCurrentRead false, temporalCurrentRead true, temporalCurrentRead false true with
  | some (.ok (.fired .value)), some (.ok .unknown),
      some (.error (.inl (.checkedDocumentRequired path))) => path == ["Form", "Rows"]
  | _, _, _ => false

example : temporalCurrentEffects = true := by native_decide

end A12Kernel.Dm.SelectedFirstFilledLocks
