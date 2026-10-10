import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document

namespace A12Kernel.Dm.CapturedFilterScopeLocks

private def number (id : FieldId) (name : String) : FlatFieldDecl := {
  id, name, groupPath := ["Form", "Rows"], repeatableScope := [10]
  policy := { kind := .number { scale := 0, signed := true } } }

private def model (kind : FieldKind) (format : String := "") : FlatModel :=
  let temporalTargetPolicy := if format.isEmpty then none else some { format }
  let code : FlatFieldDecl := { number 5 "Code" with
    policy := { kind := .enumeration }
    enumeration := some {
      storedTokens := ["a", "b"]
      categories := [{ name := "Band", tokens := ["yes", "no"] }] } }
  {
  fields := [
    { number 1 "A" with policy := { kind }, temporalTargetPolicy },
    { number 2 "Lead" with
      groupPath := ["Form"], repeatableScope := []
      policy := { kind }, temporalTargetPolicy },
    number 3 "Keep", number 4 "Out", code,
    { code with id := 6, groupPath := ["Form"], repeatableScope := [] }]
  repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 3 }] }

private def checkedGuardScopes (m : FlatModel) (guard : String) : Option (List Bool) := do
  let parsed ← (parseText .english guard).toOption
  let surface ← (lowerGuard m ["Form"] false parsed.body (some ["Form", "Rows"])).toOption
  let condition ← (m.elaborateCheckedComputationCondition ["Form"] ["Form", "Rows"] surface).toOption
  let .leaf (.predicate predicate) := condition | none
  pure ([[], [10], [10, 20], [20]].map predicate.rowBoundBool)

private def guardScopes (kind : FieldKind) (format : String) (leading captured : Bool) :
    Option (List Bool) := do
  let m := model kind format
  let guard := "FieldValuesNotUnique(" ++ (if leading then "Lead," else "") ++
    "Rows*/A Having CurrentRepetition(Rows) <= [" ++
    (if captured then "$" else "") ++ "Rows/Keep])"
  checkedGuardScopes m guard

private def profiles : List (FieldKind × String) := [
  (.number { scale := 0, signed := true }, ""), (.string, ""),
  (.temporal .date .fullDate, "yyyy-MM-dd"),
  (.temporal .time (TemporalComponents.ofFormat "HH:mm:ss"), "HH:mm:ss"),
  (.temporal .dateTime (TemporalComponents.ofFormat "yyyy-MM-dd'T'HH:mm:ss"), "yyyy-MM-dd'T'HH:mm:ss")]

example : profiles.all (fun (kind, format) => [false, true].all fun leading =>
    guardScopes kind format leading false == some [true, true, true, true]) := by native_decide

example : profiles.all (fun (kind, format) => [false, true].all fun leading =>
    guardScopes kind format leading true == some [false, true, true, false]) := by native_decide

private def projectedSource (captured : Bool) : SurfaceTokenValueCountSource := {
  first := .starHaving
    { base := .absolute, groups := [{ name := "Form" }, { name := "Rows", starred := true }]
      field := "Code" } (.category "Band")
    (.compareFields .equal {
      origin := .inner
      field := { base := .absolute, groups := ["Form", "Rows"], field := "Code" }
      projectionRef := .category "Band" } {
      origin := if captured then .outer else .inner
      field := { base := .absolute, groups := ["Form", "Rows"], field := "Code" }
      projectionRef := .category "Band" })
  rest := [] }

private def projectedScopes (declaring : GroupPath) (target binding : Option GroupPath)
    (captured : Bool) (written : GroupPath := declaring) : Option (List Bool) := do
  let source ← (elaborateTokenValueCountSource (model .string) declaring "yes"
    (projectedSource captured) (fixedTargetGroup? := target)
    (writtenGroup := written) (bindingGroup? := binding)).toOption
  pure ([[], [10], [10, 20], [20]].map fun scope =>
    source.source.bindingScopes.all (·.isPrefixOf scope))

example : projectedScopes ["Form", "Rows"] none none true = some [false, true, true, false] ∧
    projectedScopes ["Form"] (some ["Form", "Rows"]) (some ["Form", "Rows"]) true = some [false, true, true, false] ∧
    projectedScopes ["Form"] none none true = none ∧
    projectedScopes ["Form"] (some ["Form", "Rows"]) none false = some [true, true, true, true] := by native_decide

example : projectedScopes ["Form"] (some ["Form", "Rows"]) none true = some [false, true, true, false] ∧
    projectedScopes ["Form"] none (some ["Form", "Rows"]) true = some [false, true, true, false] ∧
    projectedScopes ["Form"] none none true ["Form", "Rows"] = none ∧
    projectedScopes ["Form"] (some ["Form", "Rows"]) (some ["Form"]) true = none := by native_decide

private def world : World := { now := { epochMillis := 0 } }

private def document (m : FlatModel) (value : String) : Option (CheckedDocument m) := do
  let dm : DmModel := {
    flat := m, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let row (keep code : String) := Lean.Json.mkObj [
    ("A", .str value), ("Keep", .str keep), ("Code", .str code), ("Out", .str "9")]
  let input ← (readDocument dm (Lean.Json.mkObj [("Form", Lean.Json.mkObj [
    ("Rows", .arr #[row "1" "a", row "2" "b"])])])).toOption
  if !input.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler m).toOption
  (checkDocument prepared "en_US" input.data).toOption

private def projectedCounts (declaring : GroupPath) (target : Option GroupPath) (leading : Bool := false) :
    Option (List (NumericOperand × NumericOperand)) := do
  let m := model .string
  let checked ← document m "x"
  let authored := projectedSource true
  let authored := if leading then {
    first := .field (.category { base := .absolute, groups := ["Form"], field := "Code" } "Band")
    rest := [authored.first] } else authored
  let source ← (elaborateTokenValueCountSource m declaring "yes" authored
    (fixedTargetGroup? := target)).toOption
  let context := checked.computationFillContext
  [1, 2].mapM fun row => do
    let outer := [(10, row)]
    let validation ← (source.evaluateCheckedDocumentValidation checked outer).toOption
    let computation ← (source.evaluateComputation context.document outer (context.read outer)
      context.read context.read (filterStoredText := context.storedText)
      (filterNumberText := context.numberText)).toOption
    pure (validation, computation)

example : [false, true].all (fun leading =>
    projectedCounts ["Form"] (some ["Form", "Rows"]) leading ==
      some [(.value 1 .both, .value 1 .both), (.value 0 .growOnly, .value 0 .growOnly)] &&
    projectedCounts ["Form", "Rows"] none leading == projectedCounts ["Form"] (some ["Form", "Rows"]) leading) := by native_decide

private def guardedRun (kind : FieldKind) (format value : String) : Option (List String) := do
  let m := model kind format
  let checked ← document m value
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler m).toOption
  let (_, step) ← (lowerComputation m .english {
    name := "Guarded", group := ["Form"], targetRelPath := "../Rows/Out"
    commonPrecondition := some "FieldValuesNotUnique(Rows*/A Having CurrentRepetition(Rows) <= [$Rows/Keep])"
    alternatives := [{ precondition := none, operation := "1" }], errorCodesToSuppress := [] }).toOption
  pure ((← (runComputations world prepared checked [step]).toOption).map (·.outcome))

example : (profiles.drop 2 |>.zip ["2024-01-01", "12:30:00", "2024-01-01T12:30:00"]).all (fun ((kind, format), value) =>
      guardedRun kind format value == some ["cleared", "value 1"]) := by native_decide

end A12Kernel.Dm.CapturedFilterScopeLocks
