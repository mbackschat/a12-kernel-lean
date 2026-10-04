import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document

namespace A12Kernel.Dm.TemporalRowsetLocks

private def date (id : FieldId) (name : String) (group : GroupPath := ["G"])
    (scope : List RepeatableLevel := []) : FlatFieldDecl := {
  id, name, groupPath := group, repeatableScope := scope
  policy := { kind := .temporal .date TemporalComponents.fullDate }
  temporalTargetPolicy := some { format := "yyyy-MM-dd" } }

private def model : FlatModel := {
  fields := [date 1 "A", date 2 "B", date 3 "Out", date 4 "After", date 5 "Fallback",
    date 6 "D" ["G", "Rows"] [10],
    { id := 7, name := "Keep", groupPath := ["G", "Rows"], repeatableScope := [10]
      policy := { kind := .number { scale := 0, signed := true } } },
    date 8 "A" ["G", "Pool"], date 9 "B" ["G", "Pool"],
    date 10 "A" ["G", "PoolRows"] [20], date 11 "B" ["G", "PoolRows"] [20]]
  repeatableGroups := [
    { level := 10, path := ["G", "Rows"], repeatability := some 3 },
    { level := 20, path := ["G", "PoolRows"], repeatability := some 3 }] }

private def execute (model : FlatModel) (data : Lean.Json) (definitions : List DmComputation) :
    Option (List String) := do
  let dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let input ← (readDocument dm data).toOption
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let lowered ← definitions.mapM fun definition => (lowerComputation model .english definition).toOption
  pure ((← (runComputations world prepared checked (lowered.map (·.2))).toOption).map (·.outcome))

private def computation (target operation : String) (group : GroupPath := ["G"])
    (guard : Option String := none) : DmComputation := {
  name := target ++ "Comp", group, targetRelPath := "../" ++ target, commonPrecondition := guard
  alternatives := [{ precondition := none, operation }], errorCodesToSuppress := [] }

private def run (expression : String) (rows : List (String × String))
    (pool : List (String × Lean.Json) := [])
    (poolRows : List Lean.Json := []) : Option (List String) :=
  execute model (Lean.Json.mkObj [("G", Lean.Json.mkObj [
    ("A", "2024-01-01"), ("B", "2024-01-03"), ("Out", "2024-01-10"),
    ("After", "2024-01-10"), ("Fallback", "2024-01-09"),
    ("Rows", .arr (rows.map fun (date, keep) => Lean.Json.mkObj [("D", .str date), ("Keep", .str keep)]).toArray),
    ("Pool", Lean.Json.mkObj pool), ("PoolRows", .arr poolRows.toArray)])])
    [computation "After" "FirstFilledValue(Out, Fallback)", computation "Out" expression]

example : run "MinValue(Rows*/D)" [("2024-01-03", "1"), ("2024-01-01", "1")] =
    some ["value 2024-01-01", "value 2024-01-01"] ∧
    run "MaxValue(Rows*/D)" [("2024-01-03", "1"), ("2024-01-01", "1")] =
    some ["value 2024-01-03", "value 2024-01-03"] := by native_decide

example : ["MinValue", "MaxValue"].all (fun op =>
    run s!"{op}(Rows*/D)" [] == some ["cleared", "value 2024-01-09"] &&
    run s!"{op}(Rows*/D)" [("2024-01-01", "1"), ("bad", "1")] == some ["cleared", "cleared"] &&
    run s!"{op}(Rows*/D Having [Rows/Keep] > 0)" [("2024-01-01", "1"), ("bad", "0")] ==
      some ["value 2024-01-01", "value 2024-01-01"] &&
    run s!"{op}(Rows*/D Having [Rows/Keep] > 0)" [("2024-01-01", "1"), ("2024-01-03", "bad")] ==
      some ["cleared", "cleared"] &&
    run s!"{op}(A, Rows*/D Having 1 / [Rows/Keep] > 0)" [("2024-01-03", "0")] ==
      some ["value 2024-01-01", "value 2024-01-01"]) = true := by native_decide

example : run "MinValue(Pool)" [] [("A", "2024-01-03"), ("B", "2024-01-01")] =
    some ["value 2024-01-01", "value 2024-01-01"] ∧
    run "MaxValue(PoolRows*)" [] [] [
      Lean.Json.mkObj [("A", "2024-01-01"), ("B", "2024-01-05")],
      Lean.Json.mkObj [("A", "2024-01-03"), ("B", "2024-01-02")]] =
    some ["value 2024-01-05", "value 2024-01-05"] := by native_decide

private def numericModel : FlatModel := { model with fields := model.fields ++ [
  { id := 12, name := "N", groupPath := ["G"]
    policy := { kind := .number { scale := 0, signed := true } } }] }

private def input : Lean.Json := Lean.Json.mkObj [("G", Lean.Json.mkObj [
  ("A", "2024-01-01"), ("B", "2024-01-03"), ("Out", "2024-01-10"), ("N", "0"),
  ("Rows", .arr #[Lean.Json.mkObj [("D", "2024-01-03"), ("Keep", "1")],
    Lean.Json.mkObj [("D", "2024-01-01"), ("Keep", "1")]])])]

example : execute numericModel input [computation "N" "DayFromDate(MinValue(Rows*/D))"] =
    none := by native_decide

example : execute model input [computation "Out" "AddDays(MinValue(Rows*/D),2)"] =
    none := by native_decide

example : execute model input [computation "Out" "[A]" ["G"]
    (some "MinValue(Rows*/D) == [A]")] = some ["value 2024-01-01"] := by native_decide

private def seededInput : Lean.Json := Lean.Json.mkObj [("G", Lean.Json.mkObj [
  ("A", "2024-01-01"), ("B", "2024-01-03"), ("Out", "2024-01-10"),
  ("Rows", .arr #[Lean.Json.mkObj [("D", "2024-01-10"), ("Keep", "1")],
    Lean.Json.mkObj [("D", "2024-01-10"), ("Keep", "1")]])])]

example : execute model seededInput [
    computation "Out" "MinValue(Rows*/D)",
    computation "D" "[../B]" ["G", "Rows"]] =
    some ["value 2024-01-03", "value 2024-01-03", "value 2024-01-03"] := by native_decide

example : execute model input [
    computation "Out" "MaxValue(Rows*/D Having [Rows/Keep] > 0)",
    computation "Keep" "0" ["G", "Rows"]] =
    some ["value 0", "value 0", "cleared"] := by native_decide

example : execute model seededInput [computation "D" "MinValue(../A,../B)" ["G", "Rows"]] =
    some ["value 2024-01-01", "value 2024-01-01"] := by native_decide

private def nestedModel : FlatModel := { model with
  fields := model.fields ++ [date 13 "E" ["G", "Rows", "Items"] [10, 30]]
  repeatableGroups := model.repeatableGroups ++ [
    { level := 30, path := ["G", "Rows", "Items"], repeatability := some 2 }] }

example : execute nestedModel (Lean.Json.mkObj [("G", Lean.Json.mkObj [
    ("Out", "2024-01-10"), ("Rows", .arr #[
      Lean.Json.mkObj [("D", "2024-01-10"), ("Items", .arr #[
        Lean.Json.mkObj [("E", "2024-01-03")], Lean.Json.mkObj [("E", "2024-01-01")]])],
      Lean.Json.mkObj [("D", "2024-01-10"), ("Items", .arr #[])]])])])
    [computation "Out" "MinValue(Rows*/D)", computation "D" "MinValue(Items*/E)" ["G", "Rows"]] =
    some ["value 2024-01-01", "cleared", "value 2024-01-01"] := by native_decide

private def formatted (kind : TemporalKind) (components : TemporalComponents) (format targetFormat : String)
    (targetComponents : TemporalComponents) (values : List String) (initial : String)
    (baseYear : Option Int := none) (operator : String := "MinValue") : Option (List String) :=
  let fields := [
    { (date 1 "Out") with
      policy := { kind := .temporal kind targetComponents }
      temporalTargetPolicy := some { format := targetFormat } },
    { (date 2 "D" ["G", "Rows"] [10]) with
      policy := { kind := .temporal kind components }
      temporalTargetPolicy := some { format } }]
  execute { fields, baseYear, repeatableGroups := [
      { level := 10, path := ["G", "Rows"], repeatability := some 3 }] }
    (Lean.Json.mkObj [("G", Lean.Json.mkObj [("Out", .str initial),
      ("Rows", .arr (values.map fun value => Lean.Json.mkObj [("D", .str value)]).toArray)])])
    [computation "Out" s!"{operator}(Rows*/D)"]

example : formatted .time .time "HH:mm:ss" "HH:mm:ss" .time ["03:02:01", "01:02:03"] "12:00:00" =
    some ["value 01:02:03"] ∧
    formatted .time .time "HH:mm:ss" "HH:mm:ss" .time ["03:02:01", "01:02:03"] "12:00:00" (some 2024) =
    some ["value 01:02:03"] := by native_decide

example : formatted .dateTime .now "yyyy-MM-dd'T'HH:mm:ss" "yyyy-MM-dd'T'HH:mm:ss" .now
    ["2024-01-03T01:02:03", "2024-01-01T03:02:01"] "2024-01-10T00:00:00" =
    some ["value 2024-01-01T03:02:01"] := by native_decide

example : formatted .date { TemporalComponents.fullDate with day := false } "yyyy-MM" "yyyy-MM-dd" .fullDate
    ["2024-03", "2024-01"] "2024-01-10" = some ["value 2024-01-01"] ∧
    formatted .date { TemporalComponents.fullDate with year := false } "MM-dd" "yyyy-MM-dd" .fullDate
    ["03-02", "01-03"] "2024-01-10" (some 2024) = some ["value 2024-01-03"] := by native_decide

private def correlatedModel : FlatModel := { nestedModel with fields := nestedModel.fields ++ [
  { id := 14, name := "K", groupPath := ["G", "Rows", "Items"], repeatableScope := [10, 30]
    policy := { kind := .number { scale := 0, signed := true } } }] }

example : execute correlatedModel (Lean.Json.mkObj [("G", Lean.Json.mkObj [("Rows", .arr #[
    Lean.Json.mkObj [("D", "2024-01-10"), ("Keep", "1"), ("Items", .arr #[
      Lean.Json.mkObj [("E", "2024-01-03"), ("K", "1")],
      Lean.Json.mkObj [("E", "2024-01-01"), ("K", "2")]])],
    Lean.Json.mkObj [("D", "2024-01-10"), ("Keep", "2"), ("Items", .arr #[
      Lean.Json.mkObj [("E", "2024-01-02"), ("K", "1")],
      Lean.Json.mkObj [("E", "2024-01-04"), ("K", "2")]])]])])])
    [{ (computation "D" "MinValue(Rows/Items*/E Having [Rows/Items/K] == [$Rows/Keep])") with
      targetRelPath := "../Rows/D" }] = some ["value 2024-01-03", "value 2024-01-04"] := by native_decide

private def groupModel : FlatModel := { model with
  fields := model.fields ++ [date 13 "F" ["G", "Rows", "Fixed"] [10],
    date 14 "E" ["G", "Pool", "Children"] [40]]
  repeatableGroups := model.repeatableGroups ++ [
    { level := 40, path := ["G", "Pool", "Children"], repeatability := some 3 }] }

example : execute groupModel (Lean.Json.mkObj [("G", Lean.Json.mkObj [
    ("Out", "2024-01-10"), ("Rows", .arr #[
      Lean.Json.mkObj [("Fixed", Lean.Json.mkObj [("F", "2024-01-01")])],
      Lean.Json.mkObj [("Fixed", Lean.Json.mkObj [("F", "2024-01-03")])]])])])
    [computation "Out" "MaxValue(Rows*/Fixed)"] = some ["value 2024-01-03"] := by native_decide

example : execute groupModel (Lean.Json.mkObj [("G", Lean.Json.mkObj [
    ("Out", "2024-01-10"), ("Pool", Lean.Json.mkObj [("A", "2024-01-02"), ("Children", .arr #[
      Lean.Json.mkObj [("E", "2024-01-03")], Lean.Json.mkObj [("E", "2024-01-01")]])])])])
    [computation "Out" "MinValue(Pool)"] = some ["value 2024-01-01"] := by native_decide

example : execute model input [computation "Out" "Max(MinValue(Rows*/D),[B])"] =
    some ["value 2024-01-03"] ∧
    execute model input [computation "Out" "MinValue(Out,Rows*/D)"] = none := by native_decide

private def monthOnly : TemporalComponents := { TemporalComponents.fullDate with year := false, day := false }

example : formatted .date monthOnly "MM" "MM" monthOnly ["03", "01"] "10" = some ["value 01"] ∧
    formatted .date monthOnly "MM" "MM" monthOnly ["03", "01"] "10" none "MaxValue" =
      some ["value 03"] := by native_decide

example : formatted .date .fullDate "yyyy-MM-dd" "MM" monthOnly
    ["2025-03-02", "2024-01-03"] "10" (some 2024) = some ["value 01"] := by native_decide

end A12Kernel.Dm.TemporalRowsetLocks
