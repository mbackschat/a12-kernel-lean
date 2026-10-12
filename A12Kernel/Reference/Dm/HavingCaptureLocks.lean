import A12Kernel.Reference.Dm.HavingFixture

namespace A12Kernel.Dm.HavingCaptureLocks
open Lean A12Kernel

private def parentPath : GroupPath := ["Lease", "Parents"]
private def rowPath : GroupPath := parentPath ++ ["Periods"]
private def model (indexed : Bool) : FlatModel := {
  fields := [
    { id := 1, name := "Key", groupPath := rowPath, repeatableScope := [10, 20], policy := { kind := .string } },
    { id := 2, name := "Charge", groupPath := rowPath, repeatableScope := [10, 20], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 3, name := "Window", groupPath := rowPath, repeatableScope := [10, 20],
      policy := { kind := .dateRange }, dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" } },
    { id := 4, name := "Out", groupPath := rowPath, repeatableScope := [10, 20], policy := { kind := .number { scale := 0, signed := true } } }]
  repeatableGroups := [
    { level := 10, path := parentPath, repeatability := some 2 },
    { level := 20, path := rowPath, repeatability := some 3, indexField := if indexed then some 1 else none }] }
private def world : World := { now := { epochMillis := 0 } }
private def input : Json :=
  let parent (mixed : Bool) := Json.mkObj [("Periods", .arr (([
    "2025-01-01/2025-01-10",
    if mixed then "2025-01-05/2025-01-15" else "2025-02-01/2025-02-10",
    "2025-03-01/2025-03-10"].zipIdx).map fun (range, i) => Json.mkObj [
      ("Key", .str s!"K{i}"), ("Charge", .str (if i == 2 then "2" else "1")),
      ("Window", .str range), ("Out", .str "9")]).toArray)]
  Json.mkObj [("Lease", Json.mkObj [("Parents", .arr #[parent false, parent true])])]

private def run (indexed : Bool) (predicate : String) (queryPartial : Bool := true) :
    Option (List String × Option Bool × List (String × String)) := do
  let fixture := model indexed
  let dm : DmModel := { flat := fixture, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let raw ← (readDocument dm input).toOption
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler fixture).toOption
  let document ← (checkDocument prepared "en_US" raw.data).toOption
  let rule ← (checkRule dm .english {
    group := rowPath, name := "Captured", errorCode := "CAPTURED", errorEntityRelPath := "../Window",
    condition := "FieldFilled(Window) And " ++ predicate, severity := "ERROR" }).toOption
  let messages ← (runRule world document rule).toOption
  let partialSkipped ← if !queryPartial then pure none else do
    let partialResult ← (rule.evalOrdinaryRepeatablePartial document
      (.partialSet [{ path := ["Lease"], indices := [.all] }]) (some world)).toOption
    pure (some (match partialResult with
      | .skipped => true
      | .evaluated _ => false))
  let (_, computation) ← (lowerComputation fixture .english {
    group := rowPath, name := "Captured", targetRelPath := "../Out", commonPrecondition := some predicate,
    alternatives := [{ precondition := none, operation := "1" }], errorCodesToSuppress := [] }).toOption
  let outcomes ← (runComputations world prepared document [computation]).toOption
  pure (messages.map (fun message => renderPointer fixture message.errorAddress),
    partialSkipped,
    outcomes.map fun outcome => (outcome.pointer, outcome.outcome))

private inductive Case where
  | plain | excluded | included | pair | uniqueExcluded | uniqueIncluded
  deriving BEq, DecidableEq

private def captured (field comparison : String) : String :=
  "/Lease/Parents/Periods*/" ++ field ++
    " Having CurrentRepetition(/Lease/Parents/Periods) " ++ comparison ++
    " CurrentRepetition($/Lease/Parents/Periods)"

private def predicate : Case → String
  | .plain => "AtLeastOneDateRangeOverlaps(Window In /Lease/Parents/Periods*/Window)"
  | .excluded => "AtLeastOneDateRangeOverlaps(Window In " ++ captured "Window" "!=" ++ ")"
  | .included => "AtLeastOneDateRangeOverlaps(Window In " ++ captured "Window" "==" ++ ")"
  | .pair => "DateRangesOverlap(Window," ++ captured "Window" "!=" ++ ")"
  | .uniqueExcluded => "FieldValuesNotUnique(" ++ captured "Charge" "!=" ++ ")"
  | .uniqueIncluded => "FieldValuesNotUnique(" ++ captured "Charge" "==" ++ ")"

private def rows : List (Nat × Nat) := [(1, 1), (1, 2), (1, 3), (2, 1), (2, 2), (2, 3)]

private def firedRows : Case → List (Nat × Nat)
  | .plain | .included => rows
  | .excluded => [(2, 1), (2, 2)]
  | .pair => [(2, 1), (2, 2), (2, 3)]
  | .uniqueExcluded => [(1, 3), (2, 3)]
  | .uniqueIncluded => []

private def path (parent row : Nat) (field : String) : String :=
  "Lease/Parents" ++ (if parent == 1 then "" else s!"[{parent}]") ++
    "/Periods" ++ (if row == 1 then "" else s!"[{row}]") ++ "/" ++ field

private def expected (test : Case) : List String × Option Bool × List (String × String) :=
  let fired := firedRows test
  (fired.map (fun (parent, row) => path parent row "Window"),
    if test == .plain then none else some true,
    rows.map fun (parent, row) =>
      (path parent row "Out", if fired.contains (parent, row) then "value 1" else "cleared"))

-- The two parent populations expose a leaking enclosing binding while preserving the peer's
-- six row outcomes (a12-dmkits 60dc914fd50637053e50b4c313357051aec37d8e,
-- OverlapFilterBindingDiffTest). Partial Having must skip before evaluation (spec/10 §5).
example : [false, true].all (fun indexed =>
    [.plain, .excluded, .included, .pair, .uniqueExcluded, .uniqueIncluded].all fun test =>
      run indexed (predicate test) (queryPartial := test != .plain) == some (expected test)) := by native_decide

example : [false, true].all (fun indexed =>
    run indexed "FieldFilled(Window)" == some (
      rows.map (fun (parent, row) => path parent row "Window"), some false,
      rows.map (fun (parent, row) => (path parent row "Out", "value 1")))) := by native_decide

end A12Kernel.Dm.HavingCaptureLocks

namespace A12Kernel.Dm.OffPathCaptureLocks
open Lean A12Kernel

private def root : GroupPath := ["Form"]
private def host : GroupPath := root ++ ["Hosts"]
private def child : GroupPath := host ++ ["Children"]
private def number (id : FieldId) (name : String) (path : GroupPath) (scope : List RepeatableLevel) : FlatFieldDecl :=
  { id, name, groupPath := path, repeatableScope := scope, policy := { kind := .number { scale := 0, signed := true } } }
private def model : FlatModel := {
  fields := [number 1 "Base" (root ++ ["Rows"]) [10], number 2 "Gate" (root ++ ["Rows"]) [10],
    number 3 "Threshold" host [20], number 4 "Flag" child [20, 30],
    number 5 "Marker" (child ++ ["Box"]) [20, 30], number 6 "Error" child [20, 30], number 7 "Out" child [20, 30]]
  repeatableGroups := [{ level := 10, path := root ++ ["Rows"], repeatability := some 3 },
    { level := 20, path := host, repeatability := some 2 },
    { level := 30, path := child, repeatability := some 2 }] }
private def world : World := { now := { epochMillis := 0 } }
private def filter := "[/Form/Rows/Gate] > [$/Form/Hosts/Threshold] And [$/Form/Hosts/Children/Flag] == 1 And GroupFilled($/Form/Hosts/Children/Box)"
private def operation := "Sum(/Form/Rows*/Base Having (" ++ filter ++ "))"
private def input (malformed : Bool) (emptyGroup : Bool := false) : Json :=
  let item (flag : String) (marker : Bool) := Json.mkObj [
    ("Flag", .str flag), ("Error", .str "1"), ("Out", .str "9"),
    ("Box", Json.mkObj (if marker then [("Marker", .str "1")] else []))]
  let parent (threshold : String) := Json.mkObj [("Threshold", .str threshold),
    ("Children", .arr #[item "1" (!emptyGroup), item "0" true])]
  Json.mkObj [("Form", Json.mkObj [
    ("Rows", .arr ([("1", "0"), ("2", "1"), ("4", "2")].map fun (base, gate) =>
      Json.mkObj [("Base", .str base), ("Gate", .str gate)]).toArray),
    ("Hosts", .arr #[parent "0", parent (if malformed then "bad" else "1")])])]

private def run (malformed emptyGroup : Bool) (expected : String) : Option (List String × Bool × List (String × String)) := do
  let dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let raw ← (readDocument dm (input malformed emptyGroup)).toOption
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let document ← (checkDocument prepared "en_US" raw.data).toOption
  let rule ← (checkRule dm .english {
    group := child, name := "OffPath", errorCode := "OFF_PATH", errorEntityRelPath := "../Error",
    condition := "FieldFilled(Error) And " ++ operation ++ " == " ++ expected, severity := "ERROR" }).toOption
  let messages ← (runRule world document rule).toOption
  let partialResult ← (rule.evalOrdinaryRepeatablePartial document .full (some world)).toOption
  let (_, computation) ← (lowerComputation model .english {
    group := child, name := "OffPath", targetRelPath := "../Out", commonPrecondition := none,
    alternatives := [{ precondition := none, operation }], errorCodesToSuppress := [] }).toOption
  let outcomes ← (runComputations world prepared document [computation]).toOption
  pure (messages.map (fun message => renderPointer model message.errorAddress),
    match partialResult with | .skipped => true | .evaluated _ => false,
    outcomes.map fun outcome => (outcome.pointer, outcome.outcome))

private def errorPaths := ["Form/Hosts/Children/Error", "Form/Hosts/Children[2]/Error",
  "Form/Hosts[2]/Children/Error", "Form/Hosts[2]/Children[2]/Error"]
private def outcomes (values : List String) : List (String × String) :=
  ["Form/Hosts/Children/Out", "Form/Hosts/Children[2]/Out",
    "Form/Hosts[2]/Children/Out", "Form/Hosts[2]/Children[2]/Out"].zip values

-- Kernel RtInternalIdentifier.createFromTemplate and EbenenIterator.createEbenenIterator
-- resolve every marked field/group from the complete captured state; spec/07 §3 retains phase effects.
example : run false false "6" == some (["Form/Hosts/Children/Error"], true,
    outcomes ["value 6", "value 0", "value 4", "value 0"]) := by native_decide

example : run true false "0" == some (errorPaths.tail, true,
    outcomes ["value 6", "value 0", "cleared", "cleared"]) := by native_decide

example : run false true "0" == some (errorPaths, true,
    outcomes ["value 0", "value 0", "value 0", "value 0"]) := by native_decide

end A12Kernel.Dm.OffPathCaptureLocks
