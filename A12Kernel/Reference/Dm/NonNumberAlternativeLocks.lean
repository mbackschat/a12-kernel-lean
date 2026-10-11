import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document

namespace A12Kernel.Dm.NonNumberAlternativeLocks
open Lean

private def model (rows : Bool) : FlatModel :=
  let group := if rows then ["Form", "Rows"] else ["Form"]
  let scope := if rows then [10] else []
  let text (id : FieldId) (name : String) : FlatFieldDecl := {
    id, name, groupPath := group, repeatableScope := scope, policy := { kind := .string } }
  { fields := [{ text 1 "Out" with stringPolicy := { maxLength := some 3 } },
      text 2 "Left", text 3 "Right", text 4 "Bad",
      { id := 5, name := "Gate", groupPath := group, repeatableScope := scope,
        policy := { kind := .number { scale := 0, signed := true } } }]
    repeatableGroups := if rows then [{ level := 10, path := group, repeatability := some 2 }] else [] }

private def run (rows : Bool) (alternatives : List DmAlternative) (gate : String := "1") :
    Option (List String) := do
  let fixture := model rows
  let group := if rows then ["Form", "Rows"] else ["Form"]
  let definition : DmComputation := {
    group, name := "Select", targetRelPath := "../Out", commonPrecondition := none,
    alternatives, errorCodesToSuppress := [] }
  let dm : DmModel := { flat := fixture, rules := [], computations := [definition], conditionLanguage := "en_US", refusals := [] }
  let fields := Json.mkObj [("Out", "old"), ("Left", "A"), ("Right", "B"), ("Bad", "LONG"), ("Gate", .str gate)]
  let input ← (readDocument dm (Json.mkObj [("Form", if rows then Json.mkObj [("Rows", .arr #[fields, fields])] else fields)])).toOption
  if !input.refusals.isEmpty then none
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler fixture).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  let (_, operation) ← (lowerComputation fixture .english definition).toOption
  pure ((← (runComputations world prepared document [operation]).toOption).map (·.outcome))

private def alternative (operation guard : String) : DmAlternative := {
  operation, precondition := some guard }

private def first := "FirstFilledValue(Left, Right)"
private def bad := "FirstFilledValue(Bad, Right)"

example : [false, true].all (fun rows =>
    run rows [{ operation := first, precondition := none }] ==
      some (List.replicate (if rows then 2 else 1) "value A")) = true := by native_decide

example : [false, true].all (fun rows =>
    let expected := fun value => some (List.replicate (if rows then 2 else 1) value)
    run rows [alternative bad "[Gate] < 0", alternative first "[Gate] > 0"] == expected "value A" &&
    run rows [alternative first "[Gate] > 0", alternative bad "[Gate] > 0"] == expected "value A" &&
    run rows [alternative first "[Gate] < 0", alternative bad "[Gate] < 0"] == expected "cleared" &&
    run rows [alternative bad "[Gate] > 0", alternative first "[Gate] > 0"] == expected "errored LONG") = true := by native_decide

private inductive Family where
  | enumeration | boolean | confirm | fullDate | time | dateTime | dateRange
  deriving Repr, DecidableEq

private def values : Family → String × String
  | .enumeration => ("A", "B")
  | .boolean => ("true", "false")
  | .confirm => ("true", "true")
  | .fullDate => ("2024-01-01", "2024-01-02")
  | .time => ("03:04:05", "06:07:08")
  | .dateTime => ("2024-01-01T03:04:05", "2024-01-02T06:07:08")
  | .dateRange => ("2024-01-01/2024-01-02", "2024-01-03/2024-01-04")

private def familyField (family : Family) (field : FlatFieldDecl) : FlatFieldDecl :=
  match family with
  | .enumeration => { field with
      policy := { kind := .enumeration }
      stringPolicy := {}
      enumeration := some { storedTokens := ["A", "B"] } }
  | .boolean => { field with
      policy := { kind := .boolean }
      stringPolicy := {} }
  | .confirm => { field with policy := { kind := .confirm }, stringPolicy := {} }
  | .fullDate => { field with
      policy := { kind := .temporal .date TemporalComponents.fullDate }
      stringPolicy := {}
      temporalTargetPolicy := some { format := "yyyy-MM-dd" } }
  | .time => { field with
      policy := { kind := .temporal .time TemporalComponents.time }
      stringPolicy := {}
      temporalTargetPolicy := some { format := "HH:mm:ss" } }
  | .dateTime => { field with
      policy := { kind := .temporal .dateTime TemporalComponents.now }
      stringPolicy := {}
      temporalTargetPolicy := some { format := "yyyy-MM-dd'T'HH:mm:ss" } }
  | .dateRange => { field with
      policy := { kind := .dateRange }
      stringPolicy := {}
      dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" } }

private def runFamily (family : Family) (rows : Bool) (alternatives : List DmAlternative)
    (emptySources : Bool := false) (confirmTarget : Bool := false)
    (observeReadback : Bool := false) : Option (List String) := do
  let group := if rows then ["Form", "Rows"] else ["Form"]
  let fixture := { model rows with
    fields := ((model rows).fields.map fun field =>
      if field.id == 5 then field else
        let field := familyField family field
        if confirmTarget && field.id == 1 then { field with policy := { kind := .confirm } } else field) ++
      [{ id := 6, name := "After", groupPath := group, repeatableScope := if rows then [10] else [],
         policy := { kind := .number { scale := 0, signed := true } } }]
    timeZoneId := "UTC" }
  let group := if rows then ["Form", "Rows"] else ["Form"]
  let definition : DmComputation := {
    group, name := "Select", targetRelPath := "../Out", commonPrecondition := none,
    alternatives, errorCodesToSuppress := [] }
  let dm : DmModel := { flat := fixture, rules := [], computations := [definition], conditionLanguage := "en_US", refusals := [] }
  let (left, right) := values family
  let fields := fun left right => Json.mkObj [("Out", .str right),
    ("Left", .str (if emptySources then "" else left)), ("Right", .str (if emptySources then "" else right)),
    ("Bad", "bad"), ("Gate", "1"), ("After", "9")]
  let input ← (readDocument dm (Json.mkObj [("Form", if rows then Json.mkObj
    [("Rows", .arr #[fields left right, fields right left])] else fields left right)])).toOption
  if !input.refusals.isEmpty then none
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler fixture).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  let after : DmComputation := {
    group, name := "ReadBack", targetRelPath := "../After",
    commonPrecondition := some "FieldFilled(Out) Or FieldNotFilled(Out)",
    alternatives := [{ operation := "1", precondition := none }], errorCodesToSuppress := [] }
  let definitions := if observeReadback then [after, definition] else [definition]
  let steps ← definitions.mapM fun definition => do
    let (_, operation) ← (lowerComputation fixture .english definition).toOption
    match operation with
    | .rows step => some (MixedComputationStep.rows (step builtinStringPatternCompiler))
    | .number table _ => some (.number table)
    | _ => none
  let plan ← (certifyAuthoredMixedComputationPlan steps).toOption
  let outcomes ← (plan.execute world prepared.patterns document).toOption
  pure (outcomes.filterMap fun
    | .document _ outcome => some (match outcome with
        | .boolean (.poison _) | .enumeration (.poison _) | .time (.poison _)
        | .dateTime (.poison _) | .fullDate (.poison _) | .dateRange (.poison _) => "poison"
        | _ => match outcome.storedText? with
          | some text => "value " ++ text | none => "cleared")
    | .number entry => some (match entry.outcome with
        | .accepted value => "after " ++ value.render
        | _ => "after cleared")
    | _ => none)

private def families : List Family := [.enumeration, .boolean, .fullDate, .time, .dateTime, .dateRange]

example : families.all (fun family => [false, true].all (fun rows =>
    let (left, right) := values family
    runFamily family rows [{ operation := first, precondition := none }] ==
      some (if rows then ["value " ++ left, "value " ++ right] else ["value " ++ left]))) = true := by native_decide
example : families.all (fun family => [false, true].all (fun rows =>
    let (left, right) := values family
    let selected := some (if rows then ["value " ++ left, "value " ++ right] else ["value " ++ left])
    let cleared := some (List.replicate (if rows then 2 else 1) "cleared")
    let poison := some (List.replicate (if rows then 2 else 1) "poison")
    runFamily family rows [alternative bad "[Gate] < 0", alternative first "[Gate] > 0"] == selected &&
    runFamily family rows [alternative first "[Gate] > 0", alternative bad "[Gate] > 0"] == selected &&
    runFamily family rows [alternative first "[Gate] < 0", alternative bad "[Gate] < 0"] == cleared &&
    runFamily family rows [alternative bad "[Gate] > 0", alternative first "[Gate] > 0"] == poison &&
    runFamily family rows [alternative first "[Gate] > 0", alternative bad "[Gate] > 0"] true == cleared)) = true := by native_decide

example : [false, true].all (fun rows =>
    runFamily .boolean rows [{ operation := first, precondition := none }] false true == none &&
    runFamily .boolean rows [alternative first "[Gate] > 0", alternative bad "[Gate] > 0"] false true == none) = true := by native_decide

example : (families ++ [Family.confirm]).all (fun family => [false, true].all (fun rows =>
    let (left, right) := values family
    let selected := some (if rows then ["value " ++ left, "value " ++ right] else ["value " ++ left])
    let cleared := some (List.replicate (if rows then 2 else 1) "cleared")
    let poison := some (List.replicate (if rows then 2 else 1) "poison")
    runFamily family rows [alternative "[Bad]" "[Gate] < 0", alternative "[Left]" "[Gate] > 0"] == selected &&
    runFamily family rows [alternative "[Left]" "[Gate] > 0", alternative "[Bad]" "[Gate] > 0"] == selected &&
    runFamily family rows [alternative "[Left]" "[Gate] < 0", alternative "[Bad]" "[Gate] < 0"] == cleared &&
    runFamily family rows [alternative "[Bad]" "[Gate] > 0", alternative "[Left]" "[Gate] > 0"] == poison &&
    runFamily family rows [alternative "[Left]" "[Gate] > 0", alternative "[Right]" "[Gate] > 0"] true == cleared)) = true := by native_decide

example : families.all (fun family => [false, true].all (fun rows =>
    let (left, right) := values family
    runFamily family rows [alternative first "[Gate] > 0", alternative "[Bad]" "[Gate] > 0"] ==
      some (if rows then ["value " ++ left, "value " ++ right] else ["value " ++ left]))) = true := by native_decide

example : (families ++ [Family.confirm]).all (fun family => [false, true].all (fun rows =>
    let count := if rows then 2 else 1
    let expected := fun root after => some (List.replicate count root ++ List.replicate count after)
    runFamily family rows [alternative "[Bad]" "[Gate] > 0", alternative "[Left]" "[Gate] > 0"] false false true == expected "poison" "after cleared" &&
    runFamily family rows [alternative "[Left]" "[Gate] > 0", alternative "[Right]" "[Gate] > 0"] true false true == expected "cleared" "after 1" &&
    runFamily family rows [alternative "[Bad]" "[Gate] < 0", alternative "[Left]" "[Gate] < 0"] false false true == expected "cleared" "after 1")) = true := by native_decide

end A12Kernel.Dm.NonNumberAlternativeLocks
