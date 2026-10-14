import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.ParallelValidation
import A12Kernel.Elaboration.ValidationCondition.Omission

/-! # Filtered shift amounts

Each lock runs one admitted rule whose shift amount reads a filtered entity list, so the amount comes
from the ordinary filtered carrier rather than the Having atom family. Kernel oracle: the retained
expanded-shift-amount capture
(`docs/sources/temporal-runtime-fold-probes.md#src-expanded-shift-amounts`), whose filtered batch
agrees row for row with this evaluator, its references and its fill-to-fix sets.
-/

namespace A12Kernel.Dm.FilteredShiftAmountLocks

private def model : FlatModel :=
  let date (id : Nat) (name : String) (groupPath : GroupPath) (scope : List Nat := []) : FlatFieldDecl :=
    { id, name, groupPath, repeatableScope := scope,
      policy := { kind := .temporal .date .fullDate }, temporalTargetPolicy := some { format := "yyyy-MM-dd" } }
  { fields := [
      { id := 1, name := "Tot", groupPath := ["P"], policy := { kind := .number { scale := 0, signed := true } } },
      date 2 "D" ["P"], date 3 "D2" ["P"],
      { id := 4, name := "Amt", groupPath := ["P", "Rows"], repeatableScope := [10]
        policy := { kind := .number { scale := 0, signed := true } } },
      { id := 5, name := "S", groupPath := ["P", "Rows"], repeatableScope := [10], policy := { kind := .string } },
      date 6 "RD" ["P", "Rows"] [10], date 7 "DE" ["P"],
      { id := 8, name := "GA", groupPath := ["P", "G"], policy := { kind := .number { scale := 0, signed := true } } },
      { id := 9, name := "GB", groupPath := ["P", "G"], policy := { kind := .number { scale := 0, signed := true } } },
      { id := 11, name := "HA", groupPath := ["P", "H"], policy := { kind := .number { scale := 0, signed := true } } }]
    repeatableGroups := [{ level := 10, path := ["P", "Rows"], repeatability := some 6 }] }

private def dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }

private def world : World := { now := { epochMillis := 0 }, modelZoneRules := ModelZone.concreteRules }

/-- The filtered capture's `base` document: one `x` row lacks its amount and another its Date. -/
private def document : Lean.Json :=
  Lean.Json.mkObj [("P", Lean.Json.mkObj [("Tot", .str "1"), ("D", .str "2026-05-01"), ("D2", .str "2026-05-03"),
    ("Rows", .arr #[
      Lean.Json.mkObj [("Amt", .str "1"), ("S", .str "x"), ("RD", .str "2026-01-01")],
      Lean.Json.mkObj [("Amt", .str "3"), ("S", .str "y"), ("RD", .str "2026-01-02")],
      Lean.Json.mkObj [("S", .str "x"), ("RD", .str "2026-01-03")],
      Lean.Json.mkObj [("Amt", .str "2"), ("S", .str "x")]])])]

/-- Rules at the root carry the `FieldFilled(Tot)` guard and error field `Tot`; row rules name their
own guard and use the row's `Amt`. -/
private def rule? (condition : String) (row : Bool := false) : Option (CheckedResolvedValidationRule model) :=
  match checkValidationRule dm .english {
      name := "Shift", group := ["P"], errorCode := "SHIFT",
      errorEntityRelPath := if row then "../Rows/Amt" else "../Tot",
      condition := if row then condition else "FieldFilled(Tot) And " ++ condition, severity := "ERROR" } world with
  | .ok (.ordinary rule) => some rule
  | _ => none

private def firedOn (document : Lean.Json) (condition : String) (row : Bool := false) : Option (List String) := do
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let read ← (readDocument dm document).toOption
  let checked ← (checkDocument prepared "en_US" read.data).toOption
  let messages ← (runValidationRule world checked (.ordinary (← rule? condition row))).toOption
  pure (messages.map fun message => (observe model message).messageType)

private def fired (condition : String) : Option (List String) := firedOn document condition

/-- Each expectation is the Kernel's outcome on the capture's `base` document. The `x` rows sum to 3
and their maximum is 2, so the filtered maximum stays silent (the unfiltered maximum 3 would shift
past `D2`; that twin is computed, not captured); the captured filter `[Rows/Amt] > [$Tot]` sums 5.
Capture rows `f01`, `f02`, `f08`, `f16` and `f17`. -/
example :
    fired "AddDays(D, Sum(Rows*/Amt Having [Rows/S] == \"x\")) > [D2]" = some ["OMISSION_ERROR"] ∧
    fired "AddDays(D, MaxValue(Rows*/Amt Having [Rows/S] == \"x\")) > [D2]" = some [] ∧
    fired "AddDays(D, NumberOfFilledFields(Rows*/S Having [Rows/Amt] > 0)) > [D2]" = some ["OMISSION_ERROR"] ∧
    fired "AddDays(D, Sum(Rows*/Amt Having [Rows/Amt] > [$Tot])) > [D2]" = some ["OMISSION_ERROR"] ∧
    fired "DifferenceInDays(AddDays(D, Sum(Rows*/Amt Having [Rows/S] == \"x\")), D2) > 0" = some [] := by
  native_decide

private def sets? (condition : String) : Option (List String × List String) := do
  let rule ← rule? condition
  let render (pointers : List MessagePointer) :=
    (pointers.map (renderPointer model)).mergeSort (compare · · != .gt)
  pure (render (← (rule.condition.core.referencePointers []).toOption),
    render (← (rule.condition.core.omissionPointers []).toOption))

/-- An upward filtered count keeps only its filter read as fill-to-fix; a sum keeps every read.
Capture rows `f08` and `f01`. -/
example :
    sets? "AddDays(D, NumberOfFilledFields(Rows*/S Having [Rows/Amt] > 0)) > [D2]" = some
      (["/P[1]/Rows[0]/Amt", "/P[1]/Rows[0]/S", "P/D", "P/D2", "P/Tot"], ["/P[1]/Rows[0]/Amt"]) ∧
    sets? "AddDays(D, Sum(Rows*/Amt Having [Rows/S] == \"x\")) > [D2]" = some
      (["/P[1]/Rows[0]/Amt", "/P[1]/Rows[0]/S", "P/D", "P/D2", "P/Tot"],
        ["/P[1]/Rows[0]/Amt", "/P[1]/Rows[0]/S", "P/D", "P/D2"]) := by
  native_decide

/-- The supplementary capture's documents: `grp` holds a malformed member of `G`, `grpok` its
well-formed twin. `D` equals `D2` and both rows are filled, so a shift by any count of at least one
fires the first rule of each pair and a count of zero fires the second. -/
private def groupDocument (ga : String) : Lean.Json :=
  Lean.Json.mkObj [("P", Lean.Json.mkObj [("Tot", .str "1"), ("D", .str "2026-05-01"), ("D2", .str "2026-05-01"),
    ("G", Lean.Json.mkObj [("GA", .str ga)]), ("H", Lean.Json.mkObj [("HA", .str "1")]),
    ("Rows", .arr #[
      Lean.Json.mkObj [("Amt", .str "1"), ("S", .str "x"), ("RD", .str "2026-05-01")],
      Lean.Json.mkObj [("Amt", .str "2"), ("S", .str "y"), ("RD", .str "2026-04-01")]])])]

/-- A malformed member leaves a counted group amount undecided, so both twins stay silent, on the
ordinary and on the filter route alike; the well-formed twin fires. Capture rows `s01`–`s04`. -/
example :
    firedOn (groupDocument "q") "AddDays(D, NumberOfFilledGroups(G, H)) > [D2]" = some [] ∧
    firedOn (groupDocument "q") "AddDays(D, NumberOfFilledGroups(G, H)) <= [D2]" = some [] ∧
    firedOn (groupDocument "q")
      "NumberOfFilledFields(Rows*/Amt Having AddDays(Rows/RD, NumberOfFilledGroups(G, H)) > [$D2]) > 0" = some [] ∧
    firedOn (groupDocument "q")
      "NumberOfFilledFields(Rows*/Amt Having AddDays(Rows/RD, NumberOfFilledGroups(G, H)) <= [$D2]) > 0" = some [] ∧
    firedOn (groupDocument "2") "AddDays(D, NumberOfFilledGroups(G, H)) > [D2]" = some ["VALUE_ERROR"] := by
  native_decide

/-- A first-filled comparison reads an expanded amount's members at its own bound row, as the plain
comparison does. Capture rows `r03` and `s05` on `grpok`. -/
example :
    firedOn (groupDocument "2") "FieldFilled(Rows/Amt) And FirstFilledValue(Rows/RD, D) < AddDays(D, Sum(Rows*/Amt))"
      (row := true) = some ["OMISSION_ERROR", "OMISSION_ERROR"] ∧
    firedOn (groupDocument "2") "FirstFilledValue(DE, D) < AddDays(D, Sum(G))" = some ["OMISSION_ERROR"] := by
  native_decide

/-- A starred amount member is no iteration of the error field, filtered or not, so the row rule
needs another iterated reference. Static rows `b01`–`b03`. -/
example :
    (rule? "FieldFilled(Rows/RD) And AddDays(Rows/RD, Sum(Rows*/Amt Having [Rows/S] == \"x\")) > [D]"
      (row := true)).isNone ∧
    (rule? "FieldFilled(Rows/RD) And AddDays(Rows/RD, Sum(Rows*/Amt)) > [D]" (row := true)).isNone ∧
    (rule? "FieldFilled(Rows/Amt) And AddDays(Rows/RD, Sum(Rows*/Amt Having [Rows/S] == \"x\")) < [D]"
      (row := true)).isSome := by
  native_decide

/-- A group-only expanded amount inside an ordered temporal difference needs the addressed route; the
scalar route would otherwise answer an admitted rule with silent unavailability. -/
example :
    (rule? "DifferenceInDays(AddDays(D, Sum(G)), D2) < 0").map (·.requiresAddressedValidation) = some true ∧
    (rule? "DifferenceInDays(AddDays(D, NumberOfFilledFields(G)), D2) < 0").map
      (·.requiresAddressedValidation) = some true := by
  native_decide

end A12Kernel.Dm.FilteredShiftAmountLocks
