import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.LowerValidation
import A12Kernel.Elaboration.GeneratedComputationValidation

namespace A12Kernel.Dm.BandedComputationLocks
open A12Kernel

private def model : FlatModel := { fields := [
  { id := 1, groupPath := ["Form"], name := "Source", policy := { kind := .number { scale := 3, signed := true } } },
  { id := 2, groupPath := ["Form"], name := "Out", policy := { kind := .number { scale := 2, signed := true } } }] }

private def result (mode : String) (band : Option String) (value : Rat) : Option (List String) := do
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let input : DocumentData := { instantiatedRows := [], cells := [
    { address := { field := 1, path := [] }, stored := (StoredNumber.fromComputed value 0).2.render, raw := .parsed (.num value),
      numericDecimal := some { unscaled := (StoredNumber.fromComputed value 0).2.unscaled, scale := (StoredNumber.fromComputed value 0).2.scale } },
    { address := { field := 2, path := [] }, stored := "9", raw := .parsed (.num 9) }] }
  let checked ← (checkDocument prepared "en_US" input).toOption
  let (_, computation) ← (lowerComputation model .english {
    group := ["Form"], name := "Computed", targetRelPath := "../Out", commonPrecondition := none
    roundingMode := mode
    alternatives := [{ operation := "[Source]", precondition := none, toleranceRangeOp := band }]
    errorCodesToSuppress := ["MVK_INVALID_COMPARE_DEC_PLACES"] }).toOption
  pure ((← (runComputations world prepared checked [computation]).toOption).map (·.outcome))

example : ["DiffersWithToleranceRange1", "DiffersWithToleranceRange2", "DiffersWithToleranceRange5",
    "DiffersWithToleranceRange10"].all (fun band =>
      result "RoundUp" (some band) (125 / 100) == some ["value 2"] &&
      result "RoundUp" (some band) (-125 / 100) == some ["value -1"] &&
      result "RoundDown" (some band) (-125 / 100) == some ["value -2"] &&
      result "Exact" (some band) (-1255 / 1000) == some ["value -1.26"]) = true := by native_decide

example : result "RoundUp" none 1 = none ∧ result "RoundDown" none 1 = none ∧
    result "roundup" (some "DiffersWithToleranceRange1") 1 = none ∧
    result "Exact" (some "DiffersWithToleranceRange3") 1 = none ∧
    result "Exact" none (1255 / 1000) = some ["errored 1.255"] := by native_decide

private def runTable (repeated : Bool) (mode source : String)
    (alternatives : List DmAlternative) : Option (List String) := do
  let group := if repeated then ["Form", "Rows"] else ["Form"]
  let scope := if repeated then [10] else []
  let model : FlatModel := {
    fields := model.fields.map fun field => { field with groupPath := group, repeatableScope := scope }
    repeatableGroups := if repeated then [{ level := 10, path := group, repeatability := some 2 }] else [] }
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let paths := if repeated then [[1], [2]] else [[]]
  let declaration ← model.fields.head?
  let cells ← paths.mapM fun path =>
    (classifyStored model declaration { field := 1, path } source).toOption
  let input : DocumentData := {
    instantiatedRows := if repeated then [{ group := 10, path := [1] }, { group := 10, path := [2] }] else []
    cells }
  let checked ← (checkDocument prepared "en_US" input).toOption
  let (_, computation) ← (lowerComputation model .english {
    group, name := "Computed", targetRelPath := "../Out", commonPrecondition := none
    roundingMode := mode, alternatives, errorCodesToSuppress := ["MVK_INVALID_COMPARE_DEC_PLACES"] }).toOption
  pure ((← (runComputations world prepared checked [computation]).toOption).map (·.outcome))

example : ["DiffersWithToleranceRange1", "DiffersWithToleranceRange2", "DiffersWithToleranceRange5",
    "DiffersWithToleranceRange10"].all (fun band => [false, true].all fun repeated =>
      let alternatives := [{
        precondition := some s!"[Source] {band} 0",
        operation := "[Source]", toleranceRangeOp := some band }]
      runTable repeated "RoundUp" "11.25" alternatives ==
        some (if repeated then ["value 12", "value 12"] else ["value 12"]) &&
      runTable repeated "RoundUp" "0" alternatives ==
        some []) = true := by native_decide

example :
    let banded : DmAlternative := {
      precondition := some "[Source] > 0", operation := "[Source]",
      toleranceRangeOp := some "DiffersWithToleranceRange1" }
    let plain : DmAlternative := { precondition := some "[Source] > 0", operation := "[Source]" }
    runTable false "Exact" "1.255" [banded, plain] = some ["value 1.25"] ∧
    runTable false "Exact" "1.255" [plain, banded] = some ["errored 1.255"] ∧
    runTable false "RoundUp" "1.255" [banded, plain] = none ∧
    runTable false "RoundDown" "1.255" [plain, banded] = none := by native_decide

example :
    let banded : DmAlternative := {
      precondition := none, operation := "[Source]",
      toleranceRangeOp := some "DiffersWithToleranceRange1" }
    runTable false "RoundUp" "" [banded] = some ["value 0"] ∧
    runTable false "RoundUp" "broken" [banded] = some [] := by native_decide

private def readMetadata (mode band : Option Lean.Json) : Option (String × Option String) := do
  let computation := Lean.Json.mkObj [("type", "Computation"), ("name", "C"),
    ("Computation", Lean.Json.mkObj (mode.toList.map ("roundingMode", ·) ++ [
      ("computationAlternatives", Lean.Json.arr #[Lean.Json.mkObj
        ([("operation", Lean.Json.str "1")] ++ band.toList.map ("toleranceRangeOp", ·))])]))]
  let json := Lean.Json.mkObj [("content", Lean.Json.mkObj [("modelRoot", Lean.Json.mkObj [
    ("rootGroups", Lean.Json.arr #[Lean.Json.mkObj [("type", "Group"), ("name", "Form"),
      ("Group", Lean.Json.mkObj [("elements", Lean.Json.arr #[computation])])]])])])]
  let computation ← (← (readModel json).toOption).computations.head?
  pure (computation.roundingMode, (← computation.alternatives.head?).toleranceRangeOp)

example : readMetadata (some "RoundDown") (some "DiffersWithToleranceRange5") =
    some ("RoundDown", some "DiffersWithToleranceRange5") ∧
    readMetadata none none = some ("Exact", none) ∧
    readMetadata (some .null) (some .null) = some ("Exact", none) ∧
    readMetadata (some (Lean.toJson (7 : Nat))) none = some ("7", none) ∧
    readMetadata none (some (Lean.toJson (7 : Nat))) = some ("Exact", some "7") ∧
    readMetadata (some (.bool true)) none = some ("true", none) ∧
    readMetadata (some (Lean.Json.mkObj [])) none = none ∧
    readMetadata none (some (.arr #[])) = none := by native_decide

private def generated (mode : ComputationRoundingMode) (source stored : Rat)
    (band : Option NumericToleranceRange := some .range1) :
    Option (NumericTargetCheckResult × Bool) := do
  let parsed ← (parseText .english "[Source]").toOption
  let expression ← (lowerNumericExpr (lowerCompleteComputationNumericAtom model ["Form"])
    (lowerNumericFieldAtom model ["Form"] (lowerCompleteComputationNumericAtom model ["Form"])) parsed.body).toOption
  let operation ← (elaborateCompleteNumericComputationOperation model ["Form"] 2 expression true).toOption
  let table : GeneratedComputationTable (CheckedNumericComputationOperation model) (CheckedComputationCondition model) := {
    targetField := 2, name := "Computed", roundingMode := mode
    alternatives := .singleton { operation, tolerance := band }
    messagePlan := { parts := [.text "mismatch"] } }
  let raw : RawFlatContext := { read := fun field => match field with
    | 1 => .parsed (.num source)
    | 2 => .parsed (.num stored)
    | _ => .empty }
  let computed ← (table.evaluateNumericTarget { read := (model.checkContext raw).read }).toOption
  let rule ← (assembleGeneratedNumericOperationTableRule model table).toOption
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption
  let outcome ← (rule.evalFull prepared "en_US" raw GroupPresenceContext.unavailable true).toOption
  pure (computed, match outcome with | .fired _ => true | _ => false)

example : generated .roundUp (125 / 100) (30 / 100) =
    some (.supported (.accepted { unscaled := 2, scale := 0 }), false) ∧
    generated .roundDown (125 / 100) (220 / 100) =
    some (.supported (.accepted { unscaled := 1, scale := 0 }), false) ∧
    generated .exact (1259 / 1000) (25 / 100) =
    some (.supported (.accepted { unscaled := 125, scale := 2 }), true) := by native_decide

example : [ComputationRoundingMode.exact, .roundUp, .roundDown].all (fun mode =>
    (generated mode (125 / 100) (30 / 100)).map Prod.snd == some false &&
    (generated mode (125 / 100) (220 / 100)).map Prod.snd == some false &&
    (generated mode (1259 / 1000) (25 / 100)).map Prod.snd == some true) = true ∧
    generated .roundUp 1 0 none = none ∧ generated .roundDown 1 0 none = none := by native_decide

private def parallelModel : FlatModel := {
  fields := [
    { id := 1, groupPath := ["Form", "SourceRows"], name := "Key", repeatableScope := [10], policy := { kind := .string } },
    { id := 2, groupPath := ["Form", "SourceRows"], name := "Source", repeatableScope := [10], policy := { kind := .number { scale := 3, signed := true } } },
    { id := 3, groupPath := ["Form", "Targets"], name := "Key", repeatableScope := [20], policy := { kind := .string } },
    { id := 4, groupPath := ["Form", "Targets"], name := "Out", repeatableScope := [20], policy := { kind := .number { scale := 2, signed := true } } }]
  repeatableGroups := [
    { level := 10, path := ["Form", "SourceRows"], repeatability := some 3, indexField := some 1 },
    { level := 20, path := ["Form", "Targets"], repeatability := some 3, indexField := some 3 }] }

private def parallelDefinition (mode : String) (band : Option String) : DmComputation := {
  group := ["Form", "Targets"], name := "Computed", targetRelPath := "../Out", commonPrecondition := none
  roundingMode := mode
  alternatives := [{ operation := "[/Form/SourceRows/Source]", precondition := none, toleranceRangeOp := band }]
  errorCodesToSuppress := ["MVK_INVALID_COMPARE_DEC_PLACES"] }

private def parallelInput (value : String) (stored : String := "9") : Option DocumentData := do
  let dm : DmModel := { flat := parallelModel, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let input ← (readDocument dm (Lean.Json.mkObj [("Form", Lean.Json.mkObj [
    ("SourceRows", .arr #[Lean.Json.mkObj [("Key", "A"), ("Source", .str value)]]),
    ("Targets", .arr #[Lean.Json.mkObj [("Key", "A"), ("Out", .str stored)],
      Lean.Json.mkObj [("Key", "B"), ("Out", .str stored)]])])])).toOption
  if !input.refusals.isEmpty then none
  pure input.data

private def parallelTableResult (definition : DmComputation) (value : String) :
    Option (List (String × String)) := do
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler parallelModel).toOption
  let checked ← (checkDocument prepared "en_US" (← parallelInput value)).toOption
  let (_, computation) ← (lowerComputation parallelModel .english definition).toOption
  pure ((← (runComputations world prepared checked [computation]).toOption).map fun result =>
    (result.pointer, result.outcome))

private def parallelResult (mode value : String) (band : Option String := some "DiffersWithToleranceRange1") :
    Option (List (String × String)) :=
  parallelTableResult (parallelDefinition mode band) value

example : parallelResult "Exact" "1.25" none =
    some [("Form/Targets/Out", "value 1.25"), ("Form/Targets[2]/Out", "value 0")] := by native_decide

example : parallelResult "RoundUp" "1.25" =
    some [("Form/Targets/Out", "value 2"), ("Form/Targets[2]/Out", "value 0")] ∧
    parallelResult "RoundDown" "-1.25" =
    some [("Form/Targets/Out", "value -2"), ("Form/Targets[2]/Out", "value 0")] := by native_decide

example :
    let boundaries : List (String × String × String × String) := [
      ("1.249", "1.24", "2", "1"), ("1.25", "1.25", "2", "1"), ("1.251", "1.25", "2", "1"),
      ("-1.249", "-1.25", "-1", "-2"), ("-1.25", "-1.25", "-1", "-2"), ("-1.251", "-1.26", "-1", "-2"),
      ("1.999", "1.99", "2", "1"), ("2", "2", "2", "2"), ("2.001", "2", "3", "2"),
      ("-1.999", "-2", "-1", "-2"), ("-2", "-2", "-2", "-2"), ("-2.001", "-2.01", "-2", "-3")]
    ["DiffersWithToleranceRange1", "DiffersWithToleranceRange2", "DiffersWithToleranceRange5",
      "DiffersWithToleranceRange10"].all (fun band => boundaries.all fun (source, exact, up, down) =>
        [("Exact", exact), ("RoundUp", up), ("RoundDown", down)].all fun (mode, expected) =>
          parallelResult mode source (some band) ==
            some [("Form/Targets/Out", "value " ++ expected), ("Form/Targets[2]/Out", "value 0")]) = true := by
  native_decide

example : ["Exact", "RoundUp", "RoundDown"].all (fun mode =>
    parallelResult mode "" ==
      some [("Form/Targets/Out", "value 0"), ("Form/Targets[2]/Out", "value 0")] &&
    parallelResult mode "broken" ==
      some [("Form/Targets/Out", "cleared"), ("Form/Targets[2]/Out", "value 0")]) = true ∧
    parallelResult "Exact" "" none = parallelResult "Exact" "" ∧
    parallelResult "Exact" "broken" none = parallelResult "Exact" "broken" := by native_decide

example : parallelResult "RoundUp" "1.25" none = none ∧
    parallelResult "RoundDown" "1.25" none = none ∧
    parallelResult "roundup" "1.25" = none ∧
    parallelResult "Exact" "1.25" (some "DiffersWithToleranceRange3") = none ∧
    parallelResult "Exact" "1.255" none =
      some [("Form/Targets/Out", "errored 1.255"), ("Form/Targets[2]/Out", "value 0")] ∧
    parallelResult "Exact" "1.255" =
      some [("Form/Targets/Out", "value 1.25"), ("Form/Targets[2]/Out", "value 0")] := by native_decide

private def parallelMixed (bandedFirst : Bool) (mode : String := "Exact") (overlap : Bool := true) : DmComputation :=
  let banded : DmAlternative := {
    precondition := some "FieldFilled(/Form/SourceRows/Source)", operation := "[/Form/SourceRows/Source]",
    toleranceRangeOp := some "DiffersWithToleranceRange1" }
  let plain : DmAlternative := { banded with toleranceRangeOp := none }
  let first := if bandedFirst then banded else plain
  let second := if bandedFirst then plain else banded
  let first := if overlap then first else
    { first with precondition := some "FieldNotFilled(/Form/SourceRows/Source)" }
  { parallelDefinition mode none with alternatives := [first, second] }

example : parallelTableResult (parallelMixed true) "1.255" =
    some [("Form/Targets/Out", "value 1.25"), ("Form/Targets[2]/Out", "cleared")] ∧
    parallelTableResult (parallelMixed false) "1.255" =
    some [("Form/Targets/Out", "errored 1.255"), ("Form/Targets[2]/Out", "cleared")] ∧
    parallelTableResult (parallelMixed true "Exact" false) "1.255" =
    some [("Form/Targets/Out", "errored 1.255"), ("Form/Targets[2]/Out", "value 0")] ∧
    parallelTableResult (parallelMixed false "Exact" false) "1.255" =
    some [("Form/Targets/Out", "value 1.25"), ("Form/Targets[2]/Out", "value 0")] := by native_decide

example : ["RoundUp", "RoundDown"].all (fun mode => [false, true].all fun bandedFirst =>
    parallelTableResult (parallelMixed bandedFirst mode) "1.255" == none) = true := by native_decide

/-- Exercise the generated mismatch at the resolved-value boundary after the real parallel join.
The public generated-table assembler remains a scalar-target carrier (spec/09, KF474). -/
private def parallelGenerated (mode source stored : String) :
    Option (List (String × Bool × Bool)) := do
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler parallelModel).toOption
  let checked ← (checkDocument prepared "en_US" (← parallelInput source stored)).toOption
  let (_, .parallel step) ← (lowerComputation parallelModel .english
    (parallelDefinition mode (some "DiffersWithToleranceRange1"))).toOption | none
  let operation ← step.operations.head?
  let preliminary ← checked.applyFullIndexPreliminary.toOption
  let targets ← (CheckedIsolatedParallelNumericDirectRun.executableTargets
    operation.route operation.additionalRoutes preliminary).toOption
  targets.mapM fun target => do
    let key ← (operation.targetKeyFor preliminary target.environment target.address).toOption
    let cells ← (operation.operandCells preliminary target.environment key).toOption
    let context : ScalarComputationContext := {
      read := fun field => (cells.find? (fun cell => cell.1 == field)).map Prod.snd
        |>.getD malformedCheckedCell }
    let .value raw ← (operation.expression.evaluateResolvedComputation context).toOption | none
    let .accepted rounded ← (operation.evaluateSelected context).toOption | none
    let targetCell ← (checked.read target.address).toOption
    let validation : FlatContext := { read := fun _ => targetCell }
    let mismatch := fun amount =>
      match (generatedLiteralNumberComparison operation.route.target amount (some .range1)).evalSelected validation with
      | .fired _ => true
      | _ => false
    pure (rounded.render, mismatch raw, mismatch rounded.amount)

example :
    let cases : List (String × String × String × List (String × Bool × Bool)) := [
      ("RoundUp", "1.25", "0.30", [("2", false, true), ("0", false, false)]),
      ("RoundDown", "1.25", "2.20", [("1", false, true), ("0", true, true)]),
      ("Exact", "1.259", "0.25", [("1.25", true, false), ("0", false, false)]),
      ("RoundUp", "-1.25", "-2.20", [("-1", false, true), ("0", true, true)]),
      ("RoundDown", "-1.25", "-0.30", [("-2", false, true), ("0", false, false)]),
      ("Exact", "-1.249", "-2.25", [("-1.25", true, false), ("0", true, true)])]
    cases.all (fun (mode, source, stored, expected) =>
      parallelGenerated mode source stored == some expected) = true := by native_decide

end A12Kernel.Dm.BandedComputationLocks
