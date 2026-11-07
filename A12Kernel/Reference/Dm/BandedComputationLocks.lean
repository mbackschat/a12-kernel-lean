import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.LowerValidation
import A12Kernel.Elaboration.GeneratedComputationValidation
import A12Kernel.Reference.Dm.EntryFrameFixture
import A12Kernel.Reference.Dm.ComputationCheck

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
      ("computedFieldRelPath", Lean.Json.str "../Target"),
      ("computationAlternatives", Lean.Json.arr #[Lean.Json.mkObj
        ([("operation", Lean.Json.str "1")] ++ band.toList.map ("toleranceRangeOp", ·))])]))]
  -- The target is declared: the converter drops a computation naming no field (kernel 31.1.1).
  let target := Lean.Json.mkObj [("type", "Field"), ("name", "Target"),
    ("Field", Lean.Json.mkObj [("fieldType", Lean.Json.mkObj [("type", "StringType")])])]
  let json := checkedEntryFrame <| Lean.Json.mkObj [("content", Lean.Json.mkObj [("modelRoot", Lean.Json.mkObj [
    ("rootGroups", Lean.Json.arr #[Lean.Json.mkObj [("type", "Group"), ("name", "Form"),
      ("Group", Lean.Json.mkObj [("elements", Lean.Json.arr #[target, computation])])]])])])]
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

example : [NumericToleranceRange.range2, .range5, .range10].all (fun band =>
    let width := band.threshold
    [ComputationRoundingMode.exact, .roundUp, .roundDown].all fun mode =>
      [ (width - 1 / 100, 0, false), (width, 0, false), (width + 1 / 100, 0, true),
        (-width + 1 / 100, 0, false), (-width, 0, false), (-width - 1 / 100, 0, true),
        (1259 / 1000, 125 / 100 - width, true),
        (-1255 / 1000, -126 / 100 + width, false),
        (125 / 100, 150 / 100 - width, false),
        (125 / 100, 120 / 100 + width, false) ].all fun (source, stored, fires) =>
          (generated mode source stored (some band)).map Prod.snd == some fires) = true := by
  native_decide

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
    operation.route.join (operation.additionalRoutes.map (·.join)) preliminary).toOption
  targets.mapM fun target => do
    let key ← (operation.targetKeyFor preliminary target.environment target.address).toOption
    let cells ← (operation.operandCells preliminary target.environment key).toOption
    let context : ScalarComputationContext := {
      read := fun field => (cells.find? (fun cell => cell.1 == field)).map Prod.snd
        |>.getD malformedCheckedCell }
    let joined : ParallelNumericGuardContext :=
      { joinedRead := context.read, ordinary := checked.parallelGuardContextAt target.environment }
    let .value raw ← (operation.expression.evaluateComputationWith
      ParallelNumericOperationAtom.numericComputationFault? (·.read joined)).toOption | none
    let .accepted rounded ← (operation.evaluateSelected joined).toOption | none
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

/-! ## The tolerance operator's target kinds

A tolerance-banded alternative into a String or Date target under every rounding mode, or a Custom target under
`Exact`, the only mode measured on it, draws the generated comparison's `MVK_INVALID_TYPE_FOR_TOLERANCE_OP`,
ahead of the kind class a String target reading a Number meets unbanded, while a Number target is admitted; the
unbanded twins keep the rounding mode's class.
Kernel 31.3.1, each computation `c<kind><mode><band>` named by its target kind (`S`, `D`, `N`, `C`, `SN` for a
String target reading a Number), rounding mode (`E`, `U`, `D`) and band (`b`, `u`)
([checkpoint](../../../docs/sources/kernel-31-calibration-probes.md#src-tolerance-band-target-kinds)).
-/

private def toleranceModel : Option DmModel := do
  let json ← (Lean.Json.parse (r#"{"content":{"modelConfig":{"conditionLanguage":{"code":"en_US"}},"modelRoot":{"rootGroups":[{"type":"Group","id":"/Form","name":"Form","Group":{"repeatability":1,"elements":[
{"type":"Field","id":"/Form/Src","name":"Src","Field":{"fieldType":{"type":"StringType"}}},
{"type":"Field","id":"/Form/SrcD","name":"SrcD","Field":{"fieldType":{"type":"DateType","DateType":{"format":"yyyy-MM-dd"}}}},
{"type":"Field","id":"/Form/SrcN","name":"SrcN","Field":{"fieldType":{"type":"NumberType","NumberType":{"maxFractionalDigits":0}}}},
{"type":"Field","id":"/Form/TSEb","name":"TSEb","Field":{"fieldType":{"type":"StringType"}}},
{"type":"Computation","id":"/Form/cSEb","name":"cSEb","Computation":{"computedFieldRelPath":"../TSEb","roundingMode":"Exact","computationAlternatives":[{"operation":"[Src]","toleranceRangeOp":"DiffersWithToleranceRange1"}],"errorMessage":[{"locale":"en_US","text":"m"}]}},
{"type":"Field","id":"/Form/TSEu","name":"TSEu","Field":{"fieldType":{"type":"StringType"}}},
{"type":"Computation","id":"/Form/cSEu","name":"cSEu","Computation":{"computedFieldRelPath":"../TSEu","roundingMode":"Exact","computationAlternatives":[{"operation":"[Src]"}],"errorMessage":[{"locale":"en_US","text":"m"}]}},
{"type":"Field","id":"/Form/TSUb","name":"TSUb","Field":{"fieldType":{"type":"StringType"}}},
{"type":"Computation","id":"/Form/cSUb","name":"cSUb","Computation":{"computedFieldRelPath":"../TSUb","roundingMode":"RoundUp","computationAlternatives":[{"operation":"[Src]","toleranceRangeOp":"DiffersWithToleranceRange1"}],"errorMessage":[{"locale":"en_US","text":"m"}]}},
{"type":"Field","id":"/Form/TSUu","name":"TSUu","Field":{"fieldType":{"type":"StringType"}}},
{"type":"Computation","id":"/Form/cSUu","name":"cSUu","Computation":{"computedFieldRelPath":"../TSUu","roundingMode":"RoundUp","computationAlternatives":[{"operation":"[Src]"}],"errorMessage":[{"locale":"en_US","text":"m"}]}},
{"type":"Field","id":"/Form/TSDb","name":"TSDb","Field":{"fieldType":{"type":"StringType"}}},
{"type":"Computation","id":"/Form/cSDb","name":"cSDb","Computation":{"computedFieldRelPath":"../TSDb","roundingMode":"RoundDown","computationAlternatives":[{"operation":"[Src]","toleranceRangeOp":"DiffersWithToleranceRange1"}],"errorMessage":[{"locale":"en_US","text":"m"}]}},
{"type":"Field","id":"/Form/TSDu","name":"TSDu","Field":{"fieldType":{"type":"StringType"}}},
{"type":"Computation","id":"/Form/cSDu","name":"cSDu","Computation":{"computedFieldRelPath":"../TSDu","roundingMode":"RoundDown","computationAlternatives":[{"operation":"[Src]"}],"errorMessage":[{"locale":"en_US","text":"m"}]}},
{"type":"Field","id":"/Form/TDEb","name":"TDEb","Field":{"fieldType":{"type":"DateType","DateType":{"format":"yyyy-MM-dd"}}}},
{"type":"Computation","id":"/Form/cDEb","name":"cDEb","Computation":{"computedFieldRelPath":"../TDEb","roundingMode":"Exact","computationAlternatives":[{"operation":"[SrcD]","toleranceRangeOp":"DiffersWithToleranceRange1"}],"errorMessage":[{"locale":"en_US","text":"m"}]}},
{"type":"Field","id":"/Form/TDEu","name":"TDEu","Field":{"fieldType":{"type":"DateType","DateType":{"format":"yyyy-MM-dd"}}}},
{"type":"Computation","id":"/Form/cDEu","name":"cDEu","Computation":{"computedFieldRelPath":"../TDEu","roundingMode":"Exact","computationAlternatives":[{"operation":"[SrcD]"}],"errorMessage":[{"locale":"en_US","text":"m"}]}},
{"type":"Field","id":"/Form/TDUb","name":"TDUb","Field":{"fieldType":{"type":"DateType","DateType":{"format":"yyyy-MM-dd"}}}},
{"type":"Computation","id":"/Form/cDUb","name":"cDUb","Computation":{"computedFieldRelPath":"../TDUb","roundingMode":"RoundUp","computationAlternatives":[{"operation":"[SrcD]","toleranceRangeOp":"DiffersWithToleranceRange1"}],"errorMessage":[{"locale":"en_US","text":"m"}]}},
{"type":"Field","id":"/Form/TDUu","name":"TDUu","Field":{"fieldType":{"type":"DateType","DateType":{"format":"yyyy-MM-dd"}}}},
{"type":"Computation","id":"/Form/cDUu","name":"cDUu","Computation":{"computedFieldRelPath":"../TDUu","roundingMode":"RoundUp","computationAlternatives":[{"operation":"[SrcD]"}],"errorMessage":[{"locale":"en_US","text":"m"}]}},
{"type":"Field","id":"/Form/TDDb","name":"TDDb","Field":{"fieldType":{"type":"DateType","DateType":{"format":"yyyy-MM-dd"}}}},
{"type":"Computation","id":"/Form/cDDb","name":"cDDb","Computation":{"computedFieldRelPath":"../TDDb","roundingMode":"RoundDown","computationAlternatives":[{"operation":"[SrcD]","toleranceRangeOp":"DiffersWithToleranceRange1"}],"errorMessage":[{"locale":"en_US","text":"m"}]}},
{"type":"Field","id":"/Form/TDDu","name":"TDDu","Field":{"fieldType":{"type":"DateType","DateType":{"format":"yyyy-MM-dd"}}}},
{"type":"Computation","id":"/Form/cDDu","name":"cDDu","Computation":{"computedFieldRelPath":"../TDDu","roundingMode":"RoundDown","computationAlternatives":[{"operation":"[SrcD]"}],"errorMessage":[{"locale":"en_US","text":"m"}]}},
{"type":"Field","id":"/Form/TNEb","name":"TNEb","Field":{"fieldType":{"type":"NumberType","NumberType":{"maxFractionalDigits":0}}}},
{"type":"Computation","id":"/Form/cNEb","name":"cNEb","Computation":{"computedFieldRelPath":"../TNEb","roundingMode":"Exact","computationAlternatives":[{"operation":"[SrcN]","toleranceRangeOp":"DiffersWithToleranceRange1"}],"errorMessage":[{"locale":"en_US","text":"m"}]}},
{"type":"Field","id":"/Form/TNEu","name":"TNEu","Field":{"fieldType":{"type":"NumberType","NumberType":{"maxFractionalDigits":0}}}},
{"type":"Computation","id":"/Form/cNEu","name":"cNEu","Computation":{"computedFieldRelPath":"../TNEu","roundingMode":"Exact","computationAlternatives":[{"operation":"[SrcN]"}],"errorMessage":[{"locale":"en_US","text":"m"}]}},
{"type":"Field","id":"/Form/TNUb","name":"TNUb","Field":{"fieldType":{"type":"NumberType","NumberType":{"maxFractionalDigits":0}}}},
{"type":"Computation","id":"/Form/cNUb","name":"cNUb","Computation":{"computedFieldRelPath":"../TNUb","roundingMode":"RoundUp","computationAlternatives":[{"operation":"[SrcN]","toleranceRangeOp":"DiffersWithToleranceRange1"}],"errorMessage":[{"locale":"en_US","text":"m"}]}},
{"type":"Field","id":"/Form/TNUu","name":"TNUu","Field":{"fieldType":{"type":"NumberType","NumberType":{"maxFractionalDigits":0}}}},
{"type":"Computation","id":"/Form/cNUu","name":"cNUu","Computation":{"computedFieldRelPath":"../TNUu","roundingMode":"RoundUp","computationAlternatives":[{"operation":"[SrcN]"}],"errorMessage":[{"locale":"en_US","text":"m"}]}},
{"type":"Field","id":"/Form/TNDb","name":"TNDb","Field":{"fieldType":{"type":"NumberType","NumberType":{"maxFractionalDigits":0}}}},
{"type":"Computation","id":"/Form/cNDb","name":"cNDb","Computation":{"computedFieldRelPath":"../TNDb","roundingMode":"RoundDown","computationAlternatives":[{"operation":"[SrcN]","toleranceRangeOp":"DiffersWithToleranceRange1"}],"errorMessage":[{"locale":"en_US","text":"m"}]}},
{"type":"Field","id":"/Form/TNDu","name":"TNDu","Field":{"fieldType":{"type":"NumberType","NumberType":{"maxFractionalDigits":0}}}},
{"type":"Computation","id":"/Form/cNDu","name":"cNDu","Computation":{"computedFieldRelPath":"../TNDu","roundingMode":"RoundDown","computationAlternatives":[{"operation":"[SrcN]"}],"errorMessage":[{"locale":"en_US","text":"m"}]}},
{"type":"Field","id":"/Form/SrcC","name":"SrcC","Field":{"fieldType":{"type":"CustomFieldType","CustomFieldType":{"name":"PolicyCode"}}}},
{"type":"Field","id":"/Form/TCEb","name":"TCEb","Field":{"fieldType":{"type":"CustomFieldType","CustomFieldType":{"name":"PolicyCode"}}}},
{"type":"Computation","id":"/Form/cCEb","name":"cCEb","Computation":{"computedFieldRelPath":"../TCEb","roundingMode":"Exact","computationAlternatives":[{"operation":"[SrcC]","toleranceRangeOp":"DiffersWithToleranceRange1"}],"errorMessage":[{"locale":"en_US","text":"m"}]}},
{"type":"Field","id":"/Form/TCEu","name":"TCEu","Field":{"fieldType":{"type":"CustomFieldType","CustomFieldType":{"name":"PolicyCode"}}}},
{"type":"Computation","id":"/Form/cCEu","name":"cCEu","Computation":{"computedFieldRelPath":"../TCEu","roundingMode":"Exact","computationAlternatives":[{"operation":"[SrcC]"}],"errorMessage":[{"locale":"en_US","text":"m"}]}},
{"type":"Field","id":"/Form/TSNEb","name":"TSNEb","Field":{"fieldType":{"type":"StringType"}}},
{"type":"Computation","id":"/Form/cSNEb","name":"cSNEb","Computation":{"computedFieldRelPath":"../TSNEb","roundingMode":"Exact","computationAlternatives":[{"operation":"[SrcN]","toleranceRangeOp":"DiffersWithToleranceRange1"}],"errorMessage":[{"locale":"en_US","text":"m"}]}},
{"type":"Field","id":"/Form/TSNEu","name":"TSNEu","Field":{"fieldType":{"type":"StringType"}}},
{"type":"Computation","id":"/Form/cSNEu","name":"cSNEu","Computation":{"computedFieldRelPath":"../TSNEu","roundingMode":"Exact","computationAlternatives":[{"operation":"[SrcN]"}],"errorMessage":[{"locale":"en_US","text":"m"}]}}]}}]}}}"#)).toOption
  let dm ← (readModel (checkedEntryFrame json)).toOption
  if dm.refusals.isEmpty then some dm else none

private def toleranceVerdicts : Option (List (String × String)) := do
  let dm ← toleranceModel
  pure (dm.computations.map fun computation => (computation.name.drop 1 |>.toString,
    match checkComputation dm .english computation with
    | .ok _ => "admitted"
    | .error refusal => refusal.kernelClass?.getD s!"unclassified {refusal.detail}"))

example : toleranceVerdicts = some [("SEb", "MVK_INVALID_TYPE_FOR_TOLERANCE_OP"), ("SEu", "admitted"), ("SUb", "MVK_INVALID_TYPE_FOR_TOLERANCE_OP"), ("SUu", "MVK_ERROR_WRONG_ROUNDING_MODE"), ("SDb", "MVK_INVALID_TYPE_FOR_TOLERANCE_OP"), ("SDu", "MVK_ERROR_WRONG_ROUNDING_MODE"), ("DEb", "MVK_INVALID_TYPE_FOR_TOLERANCE_OP"), ("DEu", "admitted"), ("DUb", "MVK_INVALID_TYPE_FOR_TOLERANCE_OP"), ("DUu", "MVK_ERROR_WRONG_ROUNDING_MODE"), ("DDb", "MVK_INVALID_TYPE_FOR_TOLERANCE_OP"), ("DDu", "MVK_ERROR_WRONG_ROUNDING_MODE"), ("NEb", "admitted"), ("NEu", "admitted"), ("NUb", "admitted"), ("NUu", "MVK_ERROR_WRONG_ROUNDING_MODE"), ("NDb", "admitted"), ("NDu", "MVK_ERROR_WRONG_ROUNDING_MODE"), ("CEb", "MVK_INVALID_TYPE_FOR_TOLERANCE_OP"), ("CEu", "admitted"), ("SNEb", "MVK_INVALID_TYPE_FOR_TOLERANCE_OP"), ("SNEu", "MVK_INVALID_COMPARE_TO_ENUM_OR_STRING")] := by
  native_decide

/-! ## The tolerance class's place among a computation's gates

The tolerance operator's class answers in the generated comparison, after the preamble, the operation's syntax
and its name resolution and ahead of the self-read: a banded String target reading an unknown name, an
incomplete operation or an unsupported preamble name draws that gate's class, while one reading itself draws
the tolerance class (Kernel 31.3.1, computations `t0`–`t6` of the
[precedence batch](../../../docs/sources/kernel-31-calibration-probes.md#src-computation-precedence)).
-/

private def precedenceVerdicts : Option (List (String × String)) := do
  let json ← (Lean.Json.parse (r#"{"content":{"modelConfig":{"conditionLanguage":{"code":"en_US"}},"modelRoot":{"rootGroups":[{"type":"Group","id":"/Form","name":"Form","Group":{"repeatability":1,"elements":[
{"type":"Field","id":"/Form/Src","name":"Src","Field":{"fieldType":{"type":"StringType"}}},
{"type":"Field","id":"/Form/T0","name":"T0","Field":{"fieldType":{"type":"StringType"}}},
{"type":"Field","id":"/Form/T1","name":"T1","Field":{"fieldType":{"type":"StringType"}}},
{"type":"Field","id":"/Form/T3","name":"T3","Field":{"fieldType":{"type":"StringType"}}},
{"type":"Field","id":"/Form/T4","name":"T4","Field":{"fieldType":{"type":"StringType"}}},
{"type":"Field","id":"/Form/T5","name":"T5","Field":{"fieldType":{"type":"StringType"}}},
{"type":"Field","id":"/Form/T6","name":"T6","Field":{"fieldType":{"type":"StringType"}}},
{"type":"Computation","id":"/Form/t0","name":"t0","Computation":{"computedFieldRelPath":"../T0","computationAlternatives":[{"operation":"[Nope]","toleranceRangeOp":"DiffersWithToleranceRange1"}],"errorMessage":[{"locale":"en_US","text":"m"}],"roundingMode":"Exact"}},
{"type":"Computation","id":"/Form/t1","name":"t1","Computation":{"computedFieldRelPath":"../T1","computationAlternatives":[{"operation":"[Src] +","toleranceRangeOp":"DiffersWithToleranceRange1"}],"errorMessage":[{"locale":"en_US","text":"m"}],"roundingMode":"Exact"}},
{"type":"Computation","id":"/Form/t3","name":"t3","Computation":{"computedFieldRelPath":"../T3","computationAlternatives":[{"operation":"[T3]","toleranceRangeOp":"DiffersWithToleranceRange1"}],"errorMessage":[{"locale":"en_US","text":"m"}],"roundingMode":"Exact"}},
{"type":"Computation","id":"/Form/t4","name":"t4","Computation":{"computedFieldRelPath":"../T4","computationAlternatives":[{"operation":"[Src]","toleranceRangeOp":"DiffersWithToleranceRange1"}],"errorMessage":[{"locale":"en_US","text":"m"}],"roundingMode":"Exact","additionalParserInformation":"@SuppressWarning(MVK_NOT_A_CODE)"}},
{"type":"Computation","id":"/Form/t5","name":"t5","Computation":{"computedFieldRelPath":"../T5","computationAlternatives":[{"operation":"[Nope]"}],"errorMessage":[{"locale":"en_US","text":"m"}],"roundingMode":"Exact"}},
{"type":"Computation","id":"/Form/t6","name":"t6","Computation":{"computedFieldRelPath":"../T6","computationAlternatives":[{"operation":"[Src] + [Src]","toleranceRangeOp":"DiffersWithToleranceRange1"}],"errorMessage":[{"locale":"en_US","text":"m"}],"roundingMode":"Exact"}}]}}]}}}"#)).toOption
  let dm ← (readModel (checkedEntryFrame json)).toOption
  if !dm.refusals.isEmpty then none
  pure (dm.computations.map fun computation => (computation.name,
    match checkComputation dm .english computation with
    | .ok _ => "admitted"
    | .error refusal => refusal.kernelClass?.getD s!"unclassified {refusal.detail}"))

example : precedenceVerdicts = some [("t0", "MVK_INVALID_ENTITY"), ("t1", "MVK_INCOMPLETE_INPUT"),
    ("t3", "MVK_INVALID_TYPE_FOR_TOLERANCE_OP"), ("t4", "MVK_INVALID_SUPPRESSED_WARNING"),
    ("t5", "MVK_INVALID_ENTITY"), ("t6", "MVK_INVALID_TYPE_FOR_TOLERANCE_OP")] := by
  native_decide

end A12Kernel.Dm.BandedComputationLocks
