import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.HavingFixture

namespace A12Kernel.Dm.FieldFillGuardLocks

private def number (id : FieldId) (name : String) : FlatFieldDecl := {
  id, name, groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := true } } }

private def model : FlatModel := {
  fields := [number 1 "A", number 2 "B", number 3 "Out", number 4 "Dependent",
    { number 5 "N" with groupPath := ["Form", "Rows"], repeatableScope := [10] },
    { number 6 "Gate" with groupPath := ["Form", "Rows"], repeatableScope := [10] },
    { number 7 "Out" with groupPath := ["Form", "Rows"], repeatableScope := [10] },
    { number 8 "Dependent" with groupPath := ["Form", "Rows"], repeatableScope := [10] }]
  repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 3 }] }

private def operators := ["AllFieldsFilled", "NoFieldFilled", "AtLeastOneFieldFilled",
  "MoreThanOneFieldFilled", "NotAllFieldsFilled", "NotExactlyOneFieldFilled", "FieldsNotCollectivelyFilled"]

private def run (operator operands : String) (rows : List (String × String))
    (a : String := "") (b : String := "") (stringTarget : Bool := false)
    (rowTarget : Bool := false) (producer : Bool := false)
    (fixture : FlatModel := model) (extra : List (String × Lean.Json) := [])
    (validation : Bool := false) : Option Char := do
  let model := if stringTarget then { fixture with fields := fixture.fields.map fun field =>
    if field.id == 3 then { field with policy := { kind := .string } } else field } else fixture
  let dm : DmModel := { flat := model, computations := [], rules := [], conditionLanguage := "en_US", refusals := [] }
  let data := Lean.Json.mkObj [("Form", Lean.Json.mkObj ([
    ("A", .str a), ("B", .str b), ("Out", .str "99"), ("Dependent", .str "99"),
    ("Rows", .arr (rows.map fun (n,g) => Lean.Json.mkObj [("N", .str n), ("Gate", .str g), ("Out", .str "99"), ("Dependent", .str "99")]).toArray)] ++ extra))]
  let input ← (readDocument dm data).toOption
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  if validation then
    let rule ← (checkRule dm .english {
      group := ["Form"], name := "FillRule", errorCode := "FILL", errorEntityRelPath := "../A",
      condition := "FieldFilled(A) And " ++ operator ++ "(" ++ operands ++ ")", severity := "ERROR" }).toOption
    let context : AddressedValidationEvaluationContext model := {
      scalar := { fields := checked.flatContext.withWorld world, groups := GroupPresenceContext.unavailable }
      outer := [], input := .checked checked }
    let result ← (rule.evalAddressedFull context true).toOption
    return match result.verdict with
      | .fired .omission => 'T'
      | .fired .value => 'P'
      | _ => 'F'
  let consumer : DmComputation := {
    name := "Consumer", group := ["Form"], targetRelPath := if rowTarget then "../Rows/Out" else "../Out"
    commonPrecondition := some (operator ++ "(" ++ operands ++ ")")
    alternatives := [{ precondition := none, operation := if stringTarget then "\"x\"" else "1" }], errorCodesToSuppress := [] }
  let dependent : DmComputation := {
    name := "Dependent", group := ["Form"], targetRelPath := if rowTarget then "../Rows/Dependent" else "../Dependent", commonPrecondition := none
    alternatives := [{ precondition := none, operation := if rowTarget then "[Rows/Out] + 1" else if stringTarget then "Length(Out) + 1" else "[Out] + 1" }], errorCodesToSuppress := [] }
  let gateProducer : DmComputation := {
    name := "Producer", group := ["Form"], targetRelPath := "../Rows/Gate", commonPrecondition := none
    alternatives := [{ precondition := none, operation := "1" }], errorCodesToSuppress := [] }
  let lowered ← ([consumer, dependent] ++ if producer then [gateProducer] else []).mapM fun definition => (lowerComputation model .english definition).toOption
  let results ← (runComputations world prepared checked (lowered.map (·.2))).toOption
  let outcomes := (results.filter fun result => !result.pointer.endsWith "/Gate").map (·.outcome)
  match outcomes with
  | ["value 1", "value 2"] | ["value x", "value 2"] => pure 'T'
  | ["cleared", "value 1"] => pure 'F'
  | ["cleared", "cleared"] => pure 'P'
  | ["value 1", "cleared", "value 2", "value 1"] => pure 'R'
  | _ => none

private def signature (operands : String) (rows : List (String × String))
    (a : String := "") (b : String := "") : Option String :=
  String.ofList <$> operators.mapM (fun operator => run operator operands rows a b)

private def filtered := "Rows*/N Having [Rows/Gate] > 0"
private def declared := "Rows*/N Having CurrentRepetition(Rows) > 0"
private def first := "Rows*/N Having CurrentRepetition(Rows) == 1"

example : signature filtered [] = some "TTFFFTF" ∧
    signature declared [] = some "FTFFTTF" := by native_decide

example : signature filtered [("1", "1")] = some "TFTFFFF" ∧
    signature declared [("1", "1")] = some "FFTFTFT" ∧
    signature first [("1", "1")] = some "TFTFFFF" := by native_decide

example : signature filtered [("1", "1"), ("2", "1"), ("3", "bad")] = some "PFTPPPP" ∧
    signature filtered [("1", "1"), ("2", "bad"), ("3", "1")] = some "PPPPPPP" := by native_decide

example : signature filtered [("1", "1"), ("2", "1"), ("bad", "1")] = some "PFTTPTP" ∧
    signature filtered [("bad", "0"), ("1", "1"), ("2", "1")] = some "TFTTFTF" := by native_decide

example : signature filtered [("", "1"), ("1", "1"), ("bad", "1")] = some "FFTPTPT" ∧
    signature filtered [("1", "1"), ("", "1"), ("bad", "1")] = some "FFTPTPT" := by native_decide

example : signature ("A," ++ filtered ++ ",B") [("1", "bad")] "1" "2" = some "PFTPPPP" ∧
    signature (filtered ++ ",A,B") [("1", "bad")] "1" "2" = some "PPPPPPP" ∧
    signature ("A," ++ filtered ++ ",B") [("1", "bad")] "" "2" = some "FPPPTPP" := by native_decide

example : run "AtLeastOneFieldFilled" filtered [("1", "bad")] "" "" false false true = some 'T' := by native_decide

example : run "AllFieldsFilled" "A,Rows/N" [("1", "1"), ("", "1")] "1" "" false true = some 'R' := by native_decide

example : run "AtLeastOneFieldFilled" filtered [("1", "1"), ("2", "1"), ("3", "bad")] "" "" true = some 'T' ∧
    run "MoreThanOneFieldFilled" filtered [("1", "1"), ("2", "1"), ("3", "bad")] "" "" true = some 'P' := by native_decide

example : run "AtLeastOneFieldFilled" "Rows*/N Having [$Out] > 0" [("1", "1")] = none ∧
    run "AllFieldsFilled" "A,Rows/N" [("1", "1")] "1" = none ∧
    run "AllFieldsFilled" "A,A" [] "1" = none := by native_decide

example : run "AtLeastOneFieldFilled" "Rows*/N Having [Rows/N] == [$Rows/N]"
    [("1", "1"), ("", "1")] "" "" false true = some 'R' := by native_decide


private def nestedModel : FlatModel := { model with
  timeZoneId := "Europe/Berlin"
  fields := model.fields.map fun field =>
    let field := if field.repeatableScope == [10] then
      { field with groupPath := ["Form", "Parents", "Rows"], repeatableScope := [20, 10] }
      else field
    if field.id == 6 then { field with
      policy := { kind := .temporal .dateTime (TemporalComponents.ofFormat "yyyy-MM-dd'T'HH:mm:ss") }
      temporalTargetPolicy := some { format := "yyyy-MM-dd'T'HH:mm:ss" } } else field
  repeatableGroups := [
    { level := 20, path := ["Form", "Parents"], repeatability := some 2 },
    { level := 10, path := ["Form", "Parents", "Rows"], repeatability := some 51 }] }

private def nestedRun (operator : String) (firstRows : Nat) (blankTail : Bool := false)
    (earlyWitness : Bool := false) (validation : Bool := false) : Option Char :=
  let row (value : String) := Lean.Json.mkObj [
    ("N", .str value), ("Gate", .str "2024-03-31T01:30:00")]
  let parent (rows : Array Lean.Json) := Lean.Json.mkObj [("Rows", .arr rows)]
  let first := List.replicate firstRows (row (if earlyWitness then "1" else ""))
  let second := #[row "1"] ++ if blankTail then #[Lean.Json.mkObj []] else #[]
  run operator
    "Parents*/Rows*/N Having (FieldFilled(Parents/Rows/Gate) Or [Parents/Rows/Gate] == \"31.03.2024T02:30:00\")"
    [] (a := "1") (fixture := nestedModel) (validation := validation)
    (extra := [("Parents", .arr #[parent first.toArray, parent second])])

example : operators.mapM (nestedRun · 1) = some ['P', 'F', 'T', 'F', 'P', 'F', 'P'] := by native_decide

example : operators.mapM (nestedRun · 51) = some ['F', 'P', 'T', 'P', 'T', 'P', 'T'] := by native_decide

example : nestedRun "AtLeastOneFieldFilled" 50 = some 'P' ∧
    nestedRun "AtLeastOneFieldFilled" 51 true = some 'P' ∧
    nestedRun "FieldsNotCollectivelyFilled" 50 = some 'P' ∧
    nestedRun "NoFieldFilled" 51 false true = some 'F' ∧
    nestedRun "MoreThanOneFieldFilled" 51 false true = some 'T' := by native_decide

example : operators.mapM (fun op => nestedRun op 1 false false true) =
    some ['P', 'F', 'T', 'F', 'P', 'F', 'P'] := by native_decide

example : operators.mapM (fun op => nestedRun op 50 false false true) =
    some ['F', 'P', 'P', 'P', 'T', 'P', 'P'] ∧
    operators.mapM (fun op => nestedRun op 51 false false true) =
    some ['F', 'P', 'T', 'P', 'T', 'P', 'T'] := by native_decide

example : operators.mapM (fun op => nestedRun op 50 false true true) =
    some ['P', 'F', 'T', 'T', 'P', 'T', 'P'] ∧
    operators.mapM (fun op => nestedRun op 51 true false true) =
    some ['F', 'P', 'P', 'P', 'T', 'P', 'P'] := by native_decide

end A12Kernel.Dm.FieldFillGuardLocks
