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
      field 9 "Suffix", field 10 "Direct"]
    repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 2, indexField := some 4 },
      { level := 20, path := ["Form", "Rows", "Children"], repeatability := some 3 }]
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
  localEmpty : Bool := false
  omitted : Bool := false

private def input (profile : Profile) (scenario : Scenario) : Lean.Json :=
  let row (id value localText : String) (selected : Bool) := Lean.Json.mkObj
    ([("Id", .str id), ("Out", .str (scenario.outSeed.getD (seed profile))),
      ("Local", .str (if scenario.localEmpty then "" else localText)),
      ("Children", .arr ((scenario.children.getD [value]).map (fun child =>
        Lean.Json.mkObj [("Value", .str child)])).toArray)] ++
      if selected && scenario.omitted then [] else [("Value", .str value)])
  Lean.Json.mkObj [("Form", Lean.Json.mkObj [
    ("Out", .str (scenario.outSeed.getD (seed profile))), ("Fallback", .str (scenario.fallback.getD (fallback profile))),
    ("Suffix", .str (scenario.suffix.getD (second profile))), ("Direct", .str (first profile)), ("Key", .str scenario.key),
    ("Rows", .arr #[row "a" (scenario.selected.getD (first profile)) (first profile) true,
      row scenario.secondId (second profile) (second profile) false])])]

private def checked (profile : Profile) (scenario : Scenario := {}) : Option (CheckedDocument (model profile)) := do
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler (model profile)).toOption
  let raw ← (readDocument { flat := model profile, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
    (input profile scenario)).toOption
  (checkDocument prepared "en_US" raw.data).toOption

private def definition (operation : String) (repeated : Bool := false) : DmComputation := {
  name := "Selected", group := ["Form"], targetRelPath := if repeated then "../Rows/Out" else "../Out"
  commonPrecondition := none, alternatives := [{ precondition := none, operation }], errorCodesToSuppress := [] }

private def run (profile : Profile) (operation : String) (scenario : Scenario := {})
    (repeated : Bool := false) (produceKey : Bool := false) : Option (List ComputedOutcome) := do
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler (model profile)).toOption
  let document ← checked profile scenario
  let step ← (lowerComputation (model profile) .english (definition operation repeated)).toOption
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

end A12Kernel.Dm.SelectedFirstFilledLocks
