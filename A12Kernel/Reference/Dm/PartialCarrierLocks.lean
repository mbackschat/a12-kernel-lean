import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.ParallelValidation
import A12Kernel.Reference.Dm.Replay

/-! # Partial validation over first-filled, extremum, count, construction and keyed carriers

Each lock runs one admitted rule through the partial evaluator of its iteration plan and names a
separating relevance set. Kernel oracle: the retained partial-carrier capture
(`docs/sources/model-structure-and-declaration-probes.md#src-partial-carrier-calibration`), whose 74
partial firings and every silent row agree with this evaluator.
-/

namespace A12Kernel.Dm.PartialCarrierLocks

private def model : FlatModel :=
  let number (id : Nat) (name : String) (groupPath : GroupPath) (scope : List Nat := []) : FlatFieldDecl :=
    { id, name, groupPath, repeatableScope := scope, policy := { kind := .number { scale := 0, signed := true } } }
  -- A constructed-date component needs a nonnegative Number of its position's stored width (spec/05 §3).
  let part (id : Nat) (name : String) (width : Nat) : FlatFieldDecl :=
    { id, name, groupPath := ["P", "Rows"], repeatableScope := [10],
      policy := { kind := .number { scale := 0, signed := false } }
      numericTargetConstraints := { maxStoredLength := some width } }
  let date (id : Nat) (name : String) (groupPath : GroupPath) (scope : List Nat := []) : FlatFieldDecl :=
    { id, name, groupPath, repeatableScope := scope,
      policy := { kind := .temporal .date .fullDate }, temporalTargetPolicy := some { format := "yyyy-MM-dd" } }
  { fields := [number 1 "Total" ["P"], date 2 "D" ["P"],
      number 3 "Amt" ["P", "Rows"] [10], date 4 "RD" ["P", "Rows"] [10],
      part 5 "Y" 4, part 6 "M" 2, part 7 "Dd" 2,
      { id := 8, name := "Sku", groupPath := ["P", "Items"], repeatableScope := [20], policy := { kind := .string } },
      { id := 9, name := "Label", groupPath := ["P", "Items"], repeatableScope := [20], policy := { kind := .string } },
      date 10 "Dt" ["P", "Items"] [20],
      number 11 "A" ["P", "Items", "Grp"] [20], number 12 "B" ["P", "Items", "Grp"] [20],
      number 13 "Y" ["P", "Items", "Sub"] [20, 30]]
    repeatableGroups := [
      { level := 10, path := ["P", "Rows"], repeatability := some 4 },
      { level := 20, path := ["P", "Items"], repeatability := some 4, indexField := some 8 },
      { level := 30, path := ["P", "Items", "Sub"], repeatability := some 3 }] }

private def item (sku : String) (rest : List (String × Lean.Json)) : Lean.Json :=
  Lean.Json.mkObj (("Sku", .str sku) :: rest)

private def document (duplicate : Bool) : Lean.Json :=
  let first := item "a" [("Label", .str "q"), ("Dt", .str "2026-07-01"),
    ("Grp", Lean.Json.mkObj [("A", .str "3"), ("B", .str "4")]),
    ("Sub", .arr #[Lean.Json.mkObj [("Y", .str "2")], Lean.Json.mkObj [("Y", .str "2")]])]
  let items := #[first, item "b" []] ++ (if duplicate then #[item "a" [("Label", .str "z")]] else #[])
  Lean.Json.mkObj [("P", Lean.Json.mkObj [
    ("Total", .str "1"), ("D", .str "2026-05-01"),
    ("Rows", .arr #[
      Lean.Json.mkObj [("Amt", .str "1"), ("RD", .str "2026-01-01"), ("Y", .str "2026"), ("M", .str "2"), ("Dd", .str "30")],
      Lean.Json.mkObj [("Amt", .str "2"), ("RD", .str "2026-06-01")]]),
    ("Items", .arr items)])]

/-- A relevance entry in the probe's spelling: one index per path part, `0` for every instance. -/
private def relevant (path : List String) (reps : List Nat) : RelevantEntityPattern :=
  { path := "P" :: path, indices := reps.map fun n => if n == 0 then .all else .concrete n }

/-- The fired message types under one relevance set, or `none` when the rule or document is refused. -/
private def fired (condition : String) (coverage : List RelevantEntityPattern)
    (errorField : String := "Total") (duplicate : Bool := false) : Option (List String) := do
  let dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let world : World := { now := { epochMillis := 0 }, modelZoneRules := ModelZone.concreteRules }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let read ← (readDocument dm (document duplicate)).toOption
  let checked ← (checkDocument prepared "en_US" read.data).toOption
  let rule ← match checkValidationRule dm .english {
      name := "Partial", group := ["P"], errorCode := "PART", errorEntityRelPath := "../" ++ errorField,
      condition, severity := "ERROR" } world with
    | .ok (.ordinary rule) => some rule
    | _ => none
  let messages ← (runRulePartial world checked coverage (.ordinary rule)).toOption
  pure (messages.map fun message => (observe model message).messageType)

private def total := relevant ["Total"] [1, 1]
private def root := [relevant [] [1]]

/-- Typed first-filled and extremum reads need the whole starred column relevant; the error field alone
leaves them unavailable. Capture rows `f05`, `e01` under `root` and `total`. -/
example :
    fired "FieldFilled(Total) And FirstFilledValue(Items/Dt For \"a\", D) > [D]" root = some ["VALUE_ERROR"] ∧
    fired "FieldFilled(Total) And FirstFilledValue(Items/Dt For \"a\", D) > [D]" [total] = some [] ∧
    fired "FieldFilled(Total) And MaxValue(Rows*/RD) > [D]" root = some ["OMISSION_ERROR"] ∧
    fired "FieldFilled(Total) And MaxValue(Rows*/RD) > [D]" [total] = some [] := by
  native_decide

/-- A row rule pairing a fill quantifier with an unreal constructed date fires only at a relevant row,
and an upward-sensitive filled count fires once every row is relevant. Capture rows `c03`, `n04`. -/
example :
    fired "[Rows/Amt] > 0 And AllFieldsFilled(Rows/Y, Rows/M, Rows/Dd) And Invalid(Date(Rows/Dd, Rows/M, Rows/Y))"
      [total, relevant ["Rows"] [1, 1]] "Rows/Amt" = some ["VALUE_ERROR"] ∧
    fired "[Rows/Amt] > 0 And AllFieldsFilled(Rows/Y, Rows/M, Rows/Dd) And Invalid(Date(Rows/Dd, Rows/M, Rows/Y))"
      [total, relevant ["Rows"] [1, 2]] "Rows/Amt" = some [] ∧
    fired "NumberOfFilledFields(Rows*/Amt) < 3 And FieldFilled(Total)" [total, relevant ["Rows"] [1, 0]] =
      some ["OMISSION_ERROR"] ∧
    fired "NumberOfFilledFields(Rows*/Amt) < 3 And FieldFilled(Total)" [total, relevant ["Rows"] [1, 1]] = some [] := by
  native_decide

/-- A keyed read needs its index column covered: the selected row alone or the key column alone
reads nothing. A duplicate key outside the relevant rows does not compromise the selection, while
under whole-document relevance it silences the rule. Capture rows `k01`, `k02`, `k07` under
`itemsA`, `itemsGrp`, `keyOnly` and the `dup` document. -/
example :
    fired "[Items/Label For \"a\"] == \"q\" And FieldFilled(Total)" [total, relevant ["Items"] [1, 1]] = some ["VALUE_ERROR"] ∧
    fired "Sum(Items/Grp For \"a\") > 5 And FieldFilled(Total)" [total, relevant ["Items", "Grp"] [1, 1, 1]] = some [] ∧
    fired "Sum(Items/Grp For \"a\") > 5 And FieldFilled(Total)" [total, relevant ["Items", "Sku"] [1, 0, 1]] = some [] ∧
    fired "FieldValuesNotUnique(Items/Sub*/Y For \"a\") And FieldFilled(Total)" [total, relevant ["Items"] [1, 1]] =
      some ["VALUE_ERROR"] ∧
    fired "[Items/Label For \"a\"] == \"q\" And FieldFilled(Total)" [total, relevant ["Items"] [1, 1]] "Total" true =
      some ["VALUE_ERROR"] ∧
    fired "[Items/Label For \"a\"] == \"q\" And FieldFilled(Total)" root "Total" true = some [] := by
  native_decide

end A12Kernel.Dm.PartialCarrierLocks
