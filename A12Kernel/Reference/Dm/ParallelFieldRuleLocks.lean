import A12Kernel.Reference.Dm.ParallelValidation
import A12Kernel.Reference.Dm.Document

namespace A12Kernel.Dm.ParallelFieldRuleLocks
open Lean

private def model (signed : Bool := false)
    (rightKind : FieldKind := .number { scale := 0, signed := true }) : FlatModel := {
  fields := [
    { id := 1, name := "Key", groupPath := ["Form", "L"], repeatableScope := [10], policy := { kind := .string } },
    { id := 2, name := "N", groupPath := ["Form", "L"], repeatableScope := [10], policy := { kind := .number { scale := 0, signed } } },
    { id := 3, name := "Key", groupPath := ["Form", "R"], repeatableScope := [20], policy := { kind := .string } },
    { id := 4, name := "N", groupPath := ["Form", "R"], repeatableScope := [20], policy := { kind := rightKind } } ]
  repeatableGroups := [
    { level := 10, path := ["Form", "L"], repeatability := some 3, indexField := some 1 },
    { level := 20, path := ["Form", "R"], repeatability := some 3, indexField := some 3 } ] }

private def dm (candidate : FlatModel := model) : DmModel := {
  flat := candidate, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }

private def rule (condition : String) : DmRule := {
  group := ["Form"], name := "Pair", errorCode := "PAIR", severity := "ERROR",
  errorEntityRelPath := "../L/N", condition }

private def groupJson (left right : List (String × String)) : Json :=
  .mkObj [
    ("L", .arr (left.map fun (key, number) => Json.mkObj [("Key", .str key), ("N", .str number)]).toArray),
    ("R", .arr (right.map fun (key, number) => Json.mkObj [("Key", .str key), ("N", .str number)]).toArray)]

private def documentJson (left right : List (String × String)) : Json :=
  .mkObj [("Form", groupJson left right)]

private def world : World := { now := { epochMillis := 0 } }

private def runDefinition (definition : DmRule) (candidate : FlatModel) (document : Json) :
    Option (List (String × String)) := do
  let input ← (readDocument (dm candidate) document).toOption
  if !input.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler candidate).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let plan ← (checkValidationRule (dm candidate) .english definition).toOption
  let messages ← (runValidationRule world checked plan).toOption
  pure (messages.map fun message =>
    let observed := observe candidate message
    (observed.pointer, observed.messageType))

private def run (condition : String) (candidate : FlatModel := model)
    (left : List (String × String) := [("Zulu", "7"), ("Alpha", "3")])
    (right : List (String × String) := [("Alpha", "8"), ("Beta", "2")]) :
    Option (List (String × String)) :=
  runDefinition (rule condition) candidate (documentJson left right)

private def admitted (condition : String) (candidate : FlatModel := model) : Bool :=
  (checkParallelRule (dm candidate) .english (rule condition)).isOk

example : (model).validate.isOk = true ∧ (model true).validate.isOk = true := by native_decide

example : run "[L/N] > [R/N]" = some [("Form/L/N", "OMISSION_ERROR")] ∧
    run "[L/N] < [R/N]" = some [("Form/L[2]/N", "VALUE_ERROR"), ("/Form[1]/L[-5]/N", "OMISSION_ERROR")] ∧
    run "[R/N] > [L/N]" = run "[L/N] < [R/N]" := by native_decide

example : run "FieldsNotCollectivelyFilled(L/N, R/N)" =
    some [("/Form[1]/L[-5]/N", "OMISSION_ERROR"), ("Form/L/N", "OMISSION_ERROR")] ∧
    run "FieldsNotCollectivelyFilled(R/N, L/N)" = run "FieldsNotCollectivelyFilled(L/N, R/N)" := by native_decide

example : run "[L/N] > [R/N]" model [] [("Beta", "-2")] =
    some [("/Form[1]/L[-5]/N", "VALUE_ERROR")] ∧
    run "[L/N] > [R/N]" (model true) [] [("Beta", "-2")] =
    some [("/Form[1]/L[-5]/N", "OMISSION_ERROR")] := by native_decide

example : run "FieldsNotCollectivelyFilled(L/N, R/N)" model
    [("Zulu", "7"), ("Alpha", "3")] [("Alpha", "8"), ("Beta", "2"), ("", "4")] =
    some [("/Form[1]/L[-5]/N", "OMISSION_ERROR")] := by native_decide

example : run "FieldFilled(L/N) And FieldFilled(R/N)" =
    some [("Form/L[2]/N", "VALUE_ERROR")] := by native_decide

example : ["==", "!=", "<", "<=", ">", ">="].all
    (fun op => admitted ("[L/N] " ++ op ++ " [R/N]")) = true ∧
    ["AllFieldsFilled", "AtLeastOneFieldFilled", "MoreThanOneFieldFilled", "FieldsNotCollectivelyFilled"].all
      (fun op => admitted (op ++ "(L/N, R/N)")) = true := by native_decide

example : ["NoFieldFilled", "NotAllFieldsFilled", "NotExactlyOneFieldFilled"].all
    (fun op => !admitted (op ++ "(L/N, R/N)") &&
      admitted ("FieldFilled(L/N) And " ++ op ++ "(L/N, R/N)") &&
      !admitted ("FieldFilled(L/N) Or " ++ op ++ "(L/N, R/N)")) = true := by native_decide

example : ["NoFieldFilled", "NotExactlyOneFieldFilled"].all
    (fun op => run ("[L/N] == [R/N] And " ++ op ++ "(L/N, R/N)") model
      [("Zulu", ""), ("Alpha", "")] [("Alpha", ""), ("Beta", "")] ==
      some [("Form/L[2]/N", "OMISSION_ERROR"), ("/Form[1]/L[-5]/N", "OMISSION_ERROR"),
        ("Form/L/N", "OMISSION_ERROR")]) = true := by native_decide

example :
    let mixed := model false (.number { scale := 2, signed := true })
    !admitted "[L/N] == [R/N]" mixed && admitted "[L/N] > [R/N]" mixed &&
      admitted "@SuppressWarning(MVK_INVALID_COMPARE_DEC_PLACES) [L/N] == [R/N]" mixed = true := by native_decide

example :
    let textRight := model false .string
    !admitted "[L/N] > [R/N]" textRight &&
      admitted "FieldsNotCollectivelyFilled(L/N, R/N)" textRight = true := by native_decide

example : ["FieldsNotCollectivelyFilled([L/N], R/N)", "[L/N] > R/N",
    "[L/N] > [R*/N]", "[L/N] > [R/N For \"Beta\"]",
    "FieldsNotCollectivelyFilled(L/N, L/N)", "[L/N] > 0",
    "@SuppressWarning(MVK_NO_NUMBER) [L/N] > [R/N]"].all
    (fun text => !admitted text) = true := by native_decide

private def leftDeclaredRule : DmRule := {
  (rule "[L/N] > [R/N]") with
  group := ["Form", "L"], errorEntityRelPath := "../N", condition := "[N] > [/Form/R/N]" }

example : (checkParallelRule dm .english leftDeclaredRule).isOk = true ∧
    runDefinition leftDeclaredRule model
      (documentJson [("Zulu", "7"), ("Alpha", "3")] [("Alpha", "8"), ("Beta", "2")]) =
      some [("Form/L/N", "OMISSION_ERROR")] := by native_decide

example : run "FieldsNotCollectivelyFilled(L/N, R/N)" model
    [("Zulu", "7"), ("Alpha", "3")] [("Alpha", "8"), ("Beta", "2"), ("Alpha", "4")] =
    some [("/Form[1]/L[-5]/N", "OMISSION_ERROR")] ∧
    run "[L/N] > [R/N]" model [] [] = some [] := by native_decide

example : run "[L/N] < [R/N]" model [("Alpha", "bad")] [("Alpha", "8")] = some [] ∧
    run "[L/N] < [R/N]" model [("Alpha", "3")] [("Alpha", "8")] =
    some [("Form/L/N", "VALUE_ERROR")] := by native_decide

private def numberIndexModel (rightMinimum : Nat := 2) : FlatModel :=
  let base := model
  { base with fields := base.fields.map fun declaration =>
      if declaration.id == 1 || declaration.id == 3 then
        { declaration with
          policy := { kind := .number { scale := 2, signed := true } }
          numericTargetConstraints := {
            minFractionalDigits := if declaration.id == 3 then rightMinimum else 0 } }
      else declaration }

example : run "AllFieldsFilled(L/N, R/N)" (numberIndexModel 2)
    [("5", "7")] [("5.00", "8")] =
      some [("Form/L/N", "VALUE_ERROR"), ("Form/L/N", "VALUE_ERROR")] ∧
    run "AllFieldsFilled(L/N, R/N)" (numberIndexModel 0)
      [("5", "7")] [("5.00", "8")] = some [("Form/L/N", "VALUE_ERROR")] ∧
    run "FieldsNotCollectivelyFilled(L/N, R/N)" (numberIndexModel 2)
      [("5", "7")] [("6.00", "8")] =
      some [("Form/L/N", "OMISSION_ERROR"), ("/Form[1]/L[-5]/N", "OMISSION_ERROR")] := by
  native_decide

private def commonOuterModel : FlatModel :=
  let base : FlatModel := model
  { base with
    fields := base.fields.map fun declaration => { declaration with repeatableScope := 99 :: declaration.repeatableScope }
    repeatableGroups := { level := 99, path := ["Form"], repeatability := some 2 } :: base.repeatableGroups }

example : commonOuterModel.validate.isOk = true ∧
    admitted "[L/N] > [R/N]" = true ∧
    admitted "[L/N] > [R/N]" commonOuterModel = true := by native_decide

private def commonOuterDocument : Json := .mkObj [("Form", .arr #[
  groupJson [("Alpha", "3")] [("Alpha", "8")],
  groupJson [("Alpha", "9")] [("Alpha", "4")]])]

example : runDefinition (rule "[L/N] > [R/N]") commonOuterModel commonOuterDocument =
    some [("Form[2]/L/N", "VALUE_ERROR")] ∧
    runDefinition (rule "[L/N] < [R/N]") commonOuterModel commonOuterDocument =
      some [("Form/L/N", "VALUE_ERROR")] := by native_decide

example : !(checkParallelRule dm .english
    { (rule "[L/N] > [R/N]") with errorEntityRelPath := "../L/Key" }).isOk := by native_decide

-- Atom kinds beyond a plain field read the joined rows through the ordinary validation folds: an
-- empty operand is skipped or substituted, a formally invalid one makes the comparison UNKNOWN,
-- and neither poisons the way a computation does.
private def atomModel : FlatModel :=
  let base := model true
  { base with fields := base.fields ++ [
      { id := 5, name := "M", groupPath := ["Form", "L"], repeatableScope := [10],
        policy := { kind := .number { scale := 0, signed := true } } },
      { id := 6, name := "D", groupPath := ["Form", "R"], repeatableScope := [20],
        policy := { kind := .temporal .date .fullDate }
        temporalTargetPolicy := some { format := "yyyy-MM-dd" } } ] }

private def atomRow (cells : List (String × String)) : Json :=
  .mkObj (cells.map fun (name, value) => (name, .str value))

private def leftRow (key n m : String) := atomRow [("Key", key), ("N", n), ("M", m)]
private def rightRow (key n d : String) := atomRow [("Key", key), ("N", n), ("D", d)]

private def runAtoms (condition : String) (left right : List Json) : Option (List (String × String)) :=
  runDefinition (rule condition) atomModel
    (.mkObj [("Form", .mkObj [("L", .arr left.toArray), ("R", .arr right.toArray)])])

private def admittedAtoms (condition : String) : Bool := admitted condition atomModel

example : atomModel.validate.isOk = true := by native_decide

-- Only the matched Alpha row fires; Zulu and Beta have a missing side and balance to equality.
example :
    let right := [rightRow "Alpha" "8" "", rightRow "Beta" "" ""]
    runAtoms "[L/M] != Sum(R/N, L/N)" [leftRow "Zulu" "1" "1", leftRow "Alpha" "3" "9"] right =
      some [("Form/L[2]/N", "VALUE_ERROR")] ∧
    runAtoms "[L/M] != Sum(R/N, L/N)" [leftRow "Zulu" "1" "1", leftRow "Alpha" "3" "11"] right = some [] ∧
    runAtoms "[L/M] != MaxValue(R/N, L/N)" [leftRow "Alpha" "3" "9"] right =
      some [("Form/L/N", "VALUE_ERROR")] ∧
    runAtoms "[L/M] != MaxValue(R/N, L/N)" [leftRow "Alpha" "3" "8"] right = some [] := by native_decide

-- An empty operand is skipped by the sum yet leaves the result movable (omission); an invalid one is UNKNOWN.
example :
    let left := [leftRow "Alpha" "3" "4"]
    runAtoms "[L/M] != Sum(R/N, L/N)" left [rightRow "Alpha" "" ""] =
      some [("Form/L/N", "OMISSION_ERROR")] ∧
    runAtoms "[L/M] != Sum(R/N, L/N)" [leftRow "Alpha" "3" "3"] [rightRow "Alpha" "" ""] = some [] ∧
    runAtoms "[L/M] != Sum(R/N, L/N)" left [rightRow "Alpha" "bad" ""] = some [] := by native_decide

example :
    let right := [rightRow "Alpha" "8" "2024-03-15"]
    runAtoms "[L/N] != DayFromDate(R/D) + [L/M]" [leftRow "Alpha" "17" "2"] right = some [] ∧
    runAtoms "[L/N] != DayFromDate(R/D) + [L/M]" [leftRow "Alpha" "3" "2"] right =
      some [("Form/L/N", "VALUE_ERROR")] ∧
    runAtoms "[L/N] != DayFromDate(R/D) + [L/M]" [leftRow "Alpha" "3" "2"] [rightRow "Alpha" "8" ""] =
      some [("Form/L/N", "OMISSION_ERROR")] ∧
    runAtoms "[L/N] != DayFromDate(R/D) + [L/M]" [leftRow "Alpha" "3" "2"] [rightRow "Alpha" "8" "bad"] =
      some [] := by native_decide

-- Each refusal has an admitted twin differing only in the refused feature. A distinct count keeps
-- the ordinary positive-threshold guard, measured on String operands (joined-carrier capture, rows
-- `d01b` and `d02b`, 2026-10-14) and assumed for Number ones.
example : admittedAtoms "[L/M] != Sum(R/N, L/N)" = true ∧
    admittedAtoms "[L/N] != DayFromDate(R/D) + [L/M]" = true ∧
    admittedAtoms "[L/M] != Sum(R/N)" = false ∧
    admittedAtoms "[L/M] != Sum(R*/N, L/N)" = false ∧
    admittedAtoms "[L/M] != Sum(R/N, R/N)" = false ∧
    admittedAtoms "[L/N] != DayFromDate(R*/D) + [L/M]" = false ∧
    admittedAtoms "Sum(R/N, L/N) > 3" = true ∧
    admittedAtoms "Sum(R/N, L/N) >= 0" = false ∧
    admittedAtoms "NumberOfDifferentValues(R/N, L/N) > 3" = true ∧
    admittedAtoms "NumberOfDifferentValues(R/N, L/N) < 3" = false := by native_decide

example : renderFieldPointer model { field := 2, coordinates := [.unknown] } = "/Form[1]/L[-5]/N" ∧
    renderFieldPointer model { field := 2, coordinates := [.wildcard] } = "/Form[1]/L[0]/N" ∧
    renderFieldPointer model { field := 2, coordinates := [.concrete 2] } = "Form/L[2]/N" ∧
    renderFieldPointer commonOuterModel { field := 2, coordinates := [.unknown, .concrete 2] } =
      "/Form[-5]/L[2]/N" ∧
    renderFieldPointer commonOuterModel { field := 2, coordinates := [.concrete 2, .unknown] } =
      "/Form[2]/L[-5]/N" := by native_decide

-- Message references: the structural inventory of the condition plus, per joined side that
-- contributes at least one field, that side's index field. Each fired row points a side's fields at
-- its own matched row, and an unmatched side at the unknown joined level.
private abbrev FiredReferences :=
  Option (List (String × (ParallelReferenceError ⊕ (List String × List String))))

private def referencesOf (definition : DmRule) (candidate : FlatModel) (document : Json) :
    FiredReferences := do
  let input ← (readDocument (dm candidate) document).toOption
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler candidate).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let .parallel rule ← (checkValidationRule (dm candidate) .english definition).toOption | none
  let fired ← (runParallelRuleReferences checked rule).toOption
  let sorted := fun (pointers : List MessagePointer) =>
    (pointers.map (renderFieldPointer candidate)).eraseDups.mergeSort (compare · · != .gt)
  pure (fired.map fun (message, references) =>
    ((observe candidate message).pointer,
      match references with
      | .ok r => .inr (sorted r.referenced, sorted r.fillToFix)
      | .error error => .inl error))

private def referencesRun (condition : String) (candidate : FlatModel := model)
    (left : List (String × String) := [("Zulu", "7"), ("Alpha", "3")])
    (right : List (String × String) := [("Alpha", "8"), ("Beta", "2")]) :=
  referencesOf (rule condition) candidate (documentJson left right)

-- A VALUE firing has no fill-to-fix set, and the matched pair is pointed at its own rows. The
-- unmatched left side of Beta is an OMISSION whose numeric operands are both responsible.
example : referencesRun "[L/N] < [R/N]" =
    some [("Form/L[2]/N", .inr (["Form/L[2]/Key", "Form/L[2]/N", "Form/R/Key", "Form/R/N"], [])),
      ("/Form[1]/L[-5]/N", .inr (
        ["/Form[1]/L[-5]/Key", "/Form[1]/L[-5]/N", "Form/R[2]/Key", "Form/R[2]/N"],
        ["/Form[1]/L[-5]/Key", "/Form[1]/L[-5]/N", "Form/R[2]/Key", "Form/R[2]/N"]))] := by native_decide

-- Only the negative presence leaf is omission-responsible, and with it only its own side and
-- that side's index; the positive right-hand leaf is referenced alone.
example : referencesRun "FieldNotFilled(L/N) And FieldFilled(R/N)" =
    some [("/Form[1]/L[-5]/N", .inr (
      ["/Form[1]/L[-5]/Key", "/Form[1]/L[-5]/N", "Form/R[2]/Key", "Form/R[2]/N"],
      ["/Form[1]/L[-5]/Key", "/Form[1]/L[-5]/N"]))] := by native_decide

private def sideDocument (left right : List Json) : Json :=
  .mkObj [("Form", .mkObj [("L", .arr left.toArray), ("R", .arr right.toArray)])]

-- A group operand expands to its whole subtree (here the extra `M`, which no field operand names),
-- reachable through the negative group predicate on the unmatched side.
example : referencesOf (rule "GroupNotFilled(L) And FieldFilled(R/N)") atomModel
    (sideDocument [] [rightRow "Beta" "2" ""]) =
    some [("/Form[1]/L[-5]/N", .inr (
      ["/Form[1]/L[-5]/Key", "/Form[1]/L[-5]/M", "/Form[1]/L[-5]/N", "Form/R/Key", "Form/R/N"],
      ["/Form[1]/L[-5]/Key", "/Form[1]/L[-5]/M", "/Form[1]/L[-5]/N"]))] := by native_decide

example : referencesOf (rule "GroupFilled(L) And GroupFilled(R)") atomModel
    (.mkObj [("Form", .mkObj [("L", .arr #[leftRow "Alpha" "3" "4"]),
      ("R", .arr #[rightRow "Alpha" "8" "2024-03-15"])])]) =
    some [("Form/L/N", .inr (
      ["Form/L/Key", "Form/L/M", "Form/L/N", "Form/R/D", "Form/R/Key", "Form/R/N"], []))] := by native_decide

-- The root group's presence names no field, so the unreferenced `M` and `D` stay out.
example : referencesOf (rule "GroupFilled(/Form) And FieldFilled(L/N) And FieldFilled(R/N)") atomModel
    (.mkObj [("Form", .mkObj [("L", .arr #[leftRow "Alpha" "3" "4"]),
      ("R", .arr #[rightRow "Alpha" "8" "2024-03-15"])])]) =
    some [("Form/L/N", .inr (["Form/L/Key", "Form/L/N", "Form/R/Key", "Form/R/N"], []))] := by native_decide

-- A group above the joined groups expands with every joined level wildcarded beside the joined-row
-- reads, and a group at the joined level wildcards only its own repeatable child. Kernel oracle: rows
-- `ANCPOS` and `SUBPOS` of the retained parallel-group-references capture.
private def midModel : FlatModel :=
  let base := model
  { base with
    fields := base.fields.map fun declaration =>
      { declaration with groupPath := ["Form", "Mid"] ++ declaration.groupPath.drop 1 }
    repeatableGroups := base.repeatableGroups.map fun group =>
      { group with path := ["Form", "Mid"] ++ group.path.drop 1 } }

private def midRun (condition : String) : FiredReferences :=
  referencesOf { rule condition with errorEntityRelPath := "../Mid/L/N" } midModel
    (.mkObj [("Form", .mkObj [("Mid", groupJson [("Alpha", "3")] [("Alpha", "8")])])])

example : midModel.validate.isOk = true := by native_decide

example : midRun "[Mid/L/N] < [Mid/R/N]" =
    some [("Form/Mid/L/N", .inr (
      ["Form/Mid/L/Key", "Form/Mid/L/N", "Form/Mid/R/Key", "Form/Mid/R/N"], []))] := by native_decide

example : midRun "GroupFilled(Mid) And [Mid/L/N] < [Mid/R/N]" = some [("Form/Mid/L/N", .inr (
    ["/Form[1]/Mid[1]/L[0]/Key", "/Form[1]/Mid[1]/L[0]/N", "/Form[1]/Mid[1]/R[0]/Key", "/Form[1]/Mid[1]/R[0]/N",
      "Form/Mid/L/Key", "Form/Mid/L/N", "Form/Mid/R/Key", "Form/Mid/R/N"], []))] := by native_decide

private def nestedModel : FlatModel :=
  let base := model
  { base with
    fields := base.fields ++ [
      { id := 7, name := "Q", groupPath := ["Form", "L", "Sub"], repeatableScope := [10, 11],
        policy := { kind := .string } }]
    repeatableGroups := base.repeatableGroups ++ [
      { level := 11, path := ["Form", "L", "Sub"], repeatability := some 2 }] }

private def nestedRun (condition : String) : FiredReferences :=
  referencesOf (rule condition) nestedModel
    (sideDocument [.mkObj [("Key", "Alpha"), ("N", "3"), ("Sub", .arr #[.mkObj [("Q", "x")]])]]
      [atomRow [("Key", "Alpha"), ("N", "8")]])

example : nestedModel.validate.isOk = true := by native_decide

example : nestedRun "GroupFilled(R) And [L/N] < [R/N]" = some [("Form/L/N", .inr (
    ["Form/L/Key", "Form/L/N", "Form/R/Key", "Form/R/N"], []))] := by native_decide

example : nestedRun "GroupFilled(L) And [L/N] < [R/N]" = some [("Form/L/N", .inr (
    ["/Form[1]/L[1]/Sub[0]/Q", "Form/L/Key", "Form/L/N", "Form/R/Key", "Form/R/N"], []))] := by native_decide

end A12Kernel.Dm.ParallelFieldRuleLocks
