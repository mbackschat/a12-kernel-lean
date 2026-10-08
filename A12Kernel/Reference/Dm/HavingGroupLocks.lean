import A12Kernel.Reference.Dm.HavingFixture

namespace A12Kernel.Dm.HavingGroupLocks
open Lean A12Kernel HavingFixture

private def groupedModel : FlatModel := { model with
  fields := model.fields ++ [
    { id := 6, groupPath := ["Form", "Info"], name := "Value",
      policy := { kind := .number { scale := 0, signed := true } } },
    { id := 7, groupPath := ["Form", "Other"], name := "Value",
      policy := { kind := .number { scale := 0, signed := true } } }] }

private def candidateModel : FlatModel := { groupedModel with
  fields := groupedModel.fields ++ [
    { id := 8, groupPath := ["Form", "Rows", "Info"], name := "Value", repeatableScope := [10],
      policy := { kind := .number { scale := 0, signed := true } } },
    { id := 9, groupPath := ["Form", "Rows", "Other"], name := "Value", repeatableScope := [10],
      policy := { kind := .number { scale := 0, signed := true } } },
    { id := 10, groupPath := ["Form", "Rows"], name := "Result", repeatableScope := [10],
      policy := { kind := .number { scale := 0, signed := true } } }] }

private def candidateRows : Array Json :=
  let row (n : String) (value : Json) := Json.mkObj [
    ("Tag", Json.null), ("N", Json.str n), ("Result", Json.str "99"),
    ("Info", Json.mkObj [("Value", value)]), ("Other", Json.mkObj [("Value", Json.null)])]
  #[row "2" (Json.str "3"), row "5" Json.null, row "7" (Json.str "bad")]

private def candidateRun (filter validationSum computationSum : String) : Bool :=
  runModel candidateModel filter false "" "" ""
    (ruleExpected := validationSum) (rowsOverride := some candidateRows) ==
      some (.fired .omission, ["value " ++ computationSum])

private def ordinaryCandidate (predicate : String) (rows : Array Json := candidateRows) :
    Option (List Verdict × List String) := do
  let dm : DmModel := {
    flat := candidateModel, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let input ← (readDocument dm (Json.mkObj [("Form", Json.mkObj [
    ("Rows", Json.arr rows)])])).toOption
  if !input.refusals.isEmpty then none
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler candidateModel).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  let parsed ← (parseText .english (predicate.replace "Rows/" "/Form/Rows/" |>.replace "(Rows)" "(/Form/Rows)")).toOption
  let checked ← (lowerCondition candidateModel ["Form", "Rows"] false parsed.body world).toOption
  let verdicts ← [1, 2, 3].mapM fun index =>
    (checked.core.evalAddressed {
      scalar := { fields := document.flatContext, groups := fun path =>
        (document.groupPresenceInput path [(10, index)] .fullyRelevant false).toOption.map (·.derive) },
      outer := [(10, index)], input := .checked document }).toOption
  let (_, computation) ← (lowerComputation candidateModel .english {
    group := ["Form"], name := "Present", targetRelPath := "../Rows/Result",
    commonPrecondition := some predicate,
    alternatives := [{ precondition := none, operation := "1" }], errorCodesToSuppress := [] }).toOption
  let outcomes ← (runComputations world prepared document [computation]).toOption
  pure (verdicts, outcomes.map (·.outcome))

example : runModel candidateModel "" false "" "" ""
    (operationOverride := some "Sum(Rows*/N)")
    (ruleExpected := "14") (rowsOverride := some candidateRows) =
      some (.fired .value, ["value 14"]) := by native_decide

example : [
    ("GroupFilled(Rows/Info)", [.fired .value, .notFired, .notFired], ["value 1", "cleared", "value 1"]),
    ("GroupNotFilled(Rows/Info)", [.notFired, .fired .omission, .unknown], ["cleared", "value 1", "cleared"]),
    ("AllGroupsFilled(Rows/Info, Rows/Other)", [.unknown, .unknown, .unknown], ["cleared", "cleared", "cleared"]),
    ("NoGroupFilled(Rows/Info, Rows/Other)", [.unknown, .fired .omission, .unknown], ["cleared", "value 1", "cleared"]),
    ("AtLeastOneGroupFilled(Rows/Info, Rows/Other)", [.fired .value, .unknown, .unknown], ["value 1", "cleared", "value 1"]),
    ("NotAllGroupsFilled(Rows/Info, Rows/Other)", [.fired .omission, .fired .omission, .fired .omission], ["value 1", "value 1", "value 1"]),
    ("GroupsNotCollectivelyFilled(Rows/Info, Rows/Other)", [.fired .omission, .unknown, .unknown], ["value 1", "cleared", "value 1"])].all
    (fun (predicate, verdicts, outcomes) => ordinaryCandidate predicate == some (verdicts, outcomes)) = true := by
  native_decide

example : ordinaryCandidate "GroupFilled(Rows)" =
    some ([.fired .value, .fired .value, .fired .value], ["value 1", "value 1", "value 1"]) := by
  native_decide

example : ordinaryCandidate "GroupFilled(Rows)" #[Json.mkObj [], Json.mkObj [], Json.mkObj []] =
    some ([.fired .value, .fired .value, .fired .value], ["value 1", "value 1", "value 1"]) := by
  native_decide

private inductive AdmissionStatus where
  | syntaxRefused
  | readerRefused (construct detail : String)
  | operandRefused
  | refused (diagnostic : Option KernelStaticDiagnostic)
  | admitted
  deriving BEq, Repr, DecidableEq

private def groupAdmission (fixture : FlatModel) (filter : String) : AdmissionStatus :=
  match parseText .english filter with
  | .error _ => .syntaxRefused
  | .ok parsed => match lowerHaving parsed.body with
    | .error error => .readerRefused error.construct error.detail
    | .ok authored => match elaborateStarFieldPath fixture ["Form"] {
        base := .relative 0, groups := [{ name := "Rows", starred := true }], field := "N" } with
      | .error _ => .operandRefused
      | .ok source => match elaborateStarHavingCore fixture ["Form"] source authored with
        | .ok _ => .admitted
        | .error error => .refused error.diagnostic?

example : ["GroupFilled(Info)", "GroupNotFilled(Info)",
    "AllGroupsFilled(Info, Other)", "NoGroupFilled(Info, Other)",
    "AtLeastOneGroupFilled(Info, Other)", "NotAllGroupsFilled(Info, Other)",
    "GroupsNotCollectivelyFilled(Info, Other)"].all (fun predicate =>
      groupAdmission groupedModel predicate == .refused (some .noIterationForWildcard) &&
      groupAdmission groupedModel ("[Rows/N] > 0 And " ++ predicate) == .admitted &&
      groupAdmission groupedModel (predicate ++ " And [Rows/N] > 0") == .admitted) = true := by
  native_decide

example : groupAdmission groupedModel "GroupFilled(/Form)" = .refused (some .noIterationForWildcard) ∧
    groupAdmission groupedModel "[Rows/N] > 0 And GroupFilled(/Form)" = .admitted ∧
    groupAdmission candidateModel "GroupFilled(Rows/Info)" = .admitted ∧
    groupAdmission candidateModel "GroupFilled(Rows)" = .admitted := by
  native_decide

example : groupAdmission groupedModel "[Rows/N] > 0 And GroupFilled($/Form/Info)" = .admitted ∧
    groupAdmission groupedModel "GroupFilled($/Form/Info)" = .refused (some .noIterationForWildcard) ∧
    groupAdmission groupedModel "GroupFilled($/Form/Rows)" = .refused (some .noWildcard) ∧
    groupAdmission groupedModel "[Rows/N] > 0 And GroupFilled($/Form/Rows)" = .refused (some .noWildcard) := by
  native_decide

example : groupAdmission groupedModel "[Rows/N] > 0 And GroupFilled(Form)" =
    .refused (some .invalidEntity) ∧
    groupAdmission groupedModel "[Rows/N] > 0 And GroupFilled(RuleGroup)" = .admitted := by native_decide

private def overlayGroup (path : GroupPath) (row : Env) (overlay : Bool) :
    Option (K × ComputationConditionResult) := do
  let dm : DmModel := {
    flat := candidateModel, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let input ← (readDocument dm (Json.mkObj [("Form", Json.mkObj [("Rows", Json.arr candidateRows)])])).toOption
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler candidateModel).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  let read := fun address =>
    if overlay && (address.field == 6 || (address.field == 8 && address.path == [2])) then
      Except.ok ({ rawPresent := true, parsed := some (.num 4), findings := [] } : CheckedCell)
    else document.read address
  let context := document.resolvingCorrelationContextWithRead read
  let source : ComputationGroupOperand := {
    reference := { path, origin := .path, boundRepeatableScope := candidateModel.repeatableScopeForGroupPath path }
    content := candidateModel.computationGroupSource path
    members := (candidateModel.groupSubtreeFields path).map (·.id) }
  let leaf := CorrelatedHavingLeaf.groupPresence .filled .inner source
  let frame : CorrelationFrame := { innerEnv := row, outerEnv := [] }
  pure (← (leaf.evalTruthInResolving context frame).toOption,
    ← (leaf.evalComputationInResolving context frame).toOption)

example : overlayGroup ["Form", "Info"] [] false = some (.fls, .notTrue) ∧
    overlayGroup ["Form", "Info"] [] true = some (.tru, .holds) ∧
    overlayGroup ["Form", "Rows", "Info"] [(10, 2)] false = some (.fls, .notTrue) ∧
    overlayGroup ["Form", "Rows", "Info"] [(10, 2)] true = some (.tru, .holds) ∧
    overlayGroup ["Form", "Rows", "Info"] [(10, 3)] true = some (.fls, .holds) := by native_decide

private def groupRow (predicate : String) (value : Option String)
    (validationHolds computationHolds : Bool) (otherValue : Option String := none) : Bool :=
  let extra := [
    ("Info", Json.mkObj [("Value", (value.map Json.str).getD Json.null)]),
    ("Other", Json.mkObj [("Value", (otherValue.map Json.str).getD Json.null)])]
  runModel groupedModel ("[Rows/N] > 0 And " ++ predicate) false "" "" ""
    (extra := extra) (ruleExpected := if validationHolds then "14" else "0") ==
      some (.fired .omission, [if computationHolds then "value 14" else "value 0"])

private def fixedGroupCases : List (String × Bool × Bool × Bool × Bool × Bool) := [
    ("GroupFilled(Info)", true, false, false, true, true),
    ("GroupNotFilled(Info)", false, true, false, false, false),
    ("AllGroupsFilled(Info, Other)", false, false, false, false, true),
    ("NoGroupFilled(Info, Other)", false, true, false, false, false),
    ("AtLeastOneGroupFilled(Info, Other)", true, false, false, true, true),
    ("NotAllGroupsFilled(Info, Other)", true, true, true, true, false),
    ("GroupsNotCollectivelyFilled(Info, Other)", true, false, false, true, false)]

example : fixedGroupCases.all
    (fun (predicate, filled, empty, malformedValidation, malformedComputation, bothFilled) =>
      groupRow predicate (some "3") filled filled &&
      groupRow predicate none empty empty &&
      groupRow predicate (some "bad") malformedValidation malformedComputation &&
      groupRow predicate (some "3") bothFilled bothFilled (some "4")) = true := by
  native_decide

example : runModel groupedModel "[Rows/N] > 0 And GroupFilled(/Form)" false "" "" ""
    (ruleExpected := "14") = some (.fired .omission, ["value 14"]) := by
  native_decide

example : [
    ("GroupFilled(Rows/Info)", "2", "9"),
    ("GroupNotFilled(Rows/Info)", "5", "5"),
    ("AllGroupsFilled(Rows/Info, Rows/Other)", "0", "0"),
    ("NoGroupFilled(Rows/Info, Rows/Other)", "5", "5"),
    ("AtLeastOneGroupFilled(Rows/Info, Rows/Other)", "2", "9"),
    ("NotAllGroupsFilled(Rows/Info, Rows/Other)", "14", "14"),
    ("GroupsNotCollectivelyFilled(Rows/Info, Rows/Other)", "2", "9")].all
    (fun (predicate, validationSum, computationSum) =>
      candidateRun predicate validationSum computationSum) = true := by
  native_decide

example : candidateRun "GroupFilled(Rows)" "14" "14" ∧
    candidateRun "GroupNotFilled(Rows)" "0" "0" := by native_decide

example : [
    ("GroupFilled(Info)", true), ("GroupNotFilled(Info)", false),
    ("AllGroupsFilled(Info, Other)", false), ("NoGroupFilled(Info, Other)", false),
    ("AtLeastOneGroupFilled(Info, Other)", true), ("NotAllGroupsFilled(Info, Other)", true),
    ("GroupsNotCollectivelyFilled(Info, Other)", true)].all (fun (predicate, expected) =>
      groupRow (predicate.replace "(Info" "($/Form/Info" |>.replace ", Other" ", $/Form/Other")
        (some "3") expected expected) = true := by native_decide

private def guardDependencies (carrier predicate : String) : Option (List Bool) := do
  let model := { groupedModel with fields := groupedModel.fields ++ [
    { id := 11, groupPath := ["Form", "Info"], name := "Producer",
      policy := { kind := .number { scale := 0, signed := true } } }] }
  let parsed ← (parseText .english (carrier ++ "(Rows*/N Having [Rows/N] > 0 And " ++ predicate ++ ")")).toOption
  let surface ← (lowerGuard model ["Form"] false parsed.body (some ["Form", "Info"])).toOption
  let guard ← (model.elaborateCheckedComputationCondition ["Form"] ["Form", "Info"] surface).toOption
  pure [guard.referencesField 6, guard.forbidsTarget 6,
    guard.requiresProducer 6 6 (fun _ => false),
    guard.requiresProducer 6 11 (fun _ => true),
    guard.requiresProducer 6 11 (fun _ => false),
    guard.requiresProducer 6 4 (fun _ => true)]

example : ["AllFieldsFilled", "FieldValuesNotUnique"].all (fun carrier =>
    guardDependencies carrier "GroupFilled(Info)" == some [true, false, false, false, true, true]) = true := by
  native_decide

example : ["AllFieldsFilled", "FieldValuesNotUnique"].all (fun carrier =>
    guardDependencies carrier "GroupNotFilled(Info)" == some [true, true, true, true, true, true]) = true := by
  native_decide

private def temporalGroupRun (filter : String) (value : String) (otherValue : String := "") : Option (Verdict × List String) :=
  let dates := { groupedModel with fields := groupedModel.fields.map fun field =>
    if field.id == 2 || field.id == 3 then { field with
      policy := { kind := .temporal .date TemporalComponents.fullDate }
      temporalTargetPolicy := some { format := "yyyy-MM-dd" } } else field }
  let condition := "MinValue(Rows*/Tag" ++ (if filter.isEmpty then "" else " Having [Rows/N] > 0 And " ++ filter) ++ ") == [Expected]"
  runModel dates "" false "2024-03-01" "2024-03-01" "2024-03-02"
    (extra := [("Info", Json.mkObj [("Value", Json.str value)]),
      ("Other", Json.mkObj [("Value", Json.str otherValue)])])
    (operationOverride := some "1") (ruleCondition := some ("FieldFilled(Error) And " ++ condition)) (computationPrecondition := some condition)

example : temporalGroupRun "" "3" = some (.fired .value, ["value 1"]) := by native_decide

example : fixedGroupCases.all (fun (predicate, filled, empty, malformedValidation, malformedComputation, bothFilled) =>
    [("3", "", filled, filled), ("", "", empty, empty),
      ("bad", "", malformedValidation, malformedComputation), ("3", "4", bothFilled, bothFilled)].all
      (fun (value, otherValue, validation, computation) => temporalGroupRun predicate value otherValue ==
        some (if validation then .fired .omission else .notFired, if computation then ["value 1"] else []))) = true := by
  native_decide

private def containingTargetRun (kind : FieldKind) (stored : String)
    (operation : String := "FirstFilledValue") (predicate : String := "GroupFilled(/Form)") :
    Option (Verdict × List String) :=
  let targetModel := { model with fields := model.fields.map fun field =>
    if field.id == 2 || field.id == 3 || field.id == 5 then
      { field with policy := { kind }, temporalTargetPolicy :=
          match kind with | .temporal .date _ => some { format := "yyyy-MM-dd" } | _ => none }
    else field }
  runModel targetModel "" false stored stored stored
    (operationOverride := some (operation ++ "(Rows*/Tag Having [Rows/N] > 0 And " ++ predicate ++ ")"))
    (ruleCondition := some "FieldFilled(Error)")

example : [(.boolean, "true"), (.string, "kept"),
    (.temporal .date TemporalComponents.fullDate, "2024-03-01")].all (fun (kind, stored) =>
      containingTargetRun kind stored == some (.fired .value, ["value " ++ stored]) &&
      (containingTargetRun kind stored (predicate := "GroupNotFilled(/Form)")).isNone) = true := by
  native_decide

example : containingTargetRun (.temporal .date TemporalComponents.fullDate) "2024-03-01" "MinValue" =
    some (.fired .value, ["value 2024-03-01"]) := by native_decide

private def groupOverlapCertificate (origin : HavingOrigin) : Option Bool := do
  let source ← (groupedModel.resolveHavingGroupPresence ["Form"] [] .inner
    (.path { base := .absolute, groups := ["Form", "Info"] })).toOption
  let leaf := CorrelatedHavingLeaf.groupFill .atLeastOneGroupFilled
    (.group .inner { source with dependencyKind := .ordinaryList }) [.field { origin, field := 6 }]
  pure (leaf.wellFormedForEnvironments groupedModel [10] [])

example : groupOverlapCertificate .inner = some false ∧
    groupOverlapCertificate .outer = some false := by native_decide

private def descendantModel : FlatModel := { groupedModel with
  fields := groupedModel.fields ++ [
    { id := 12, groupPath := ["Form", "Info", "Child"], name := "Value",
      policy := { kind := .number { scale := 0, signed := true } } }] }

example : [
    "AtLeastOneGroupFilled(Info, $/Form/Info/Value)",
    "AtLeastOneGroupFilled($/Form/Info, Info/Value)",
    "AllGroupsFilled(Info, $/Form/Info/Child)"].all (fun predicate =>
      groupAdmission descendantModel ("[Rows/N] > 0 And " ++ predicate) ==
        .refused (some .duplicateParam2)) = true := by native_decide

example : groupAdmission groupedModel
      "[Rows/N] > 0 And AllGroupsFilled(Info, $/Form/Info)" = .admitted ∧
    groupAdmission groupedModel "[Rows/N] > 0 And AllGroupsFilled(Info, Info)" =
      .refused (some .duplicateParam1) := by native_decide

private def producerProtection (condition : String) : Option Bool := do
  let parsed ← (parseText .english condition).toOption
  let surface ← (lowerGuard groupedModel ["Form"] false parsed.body (some ["Form", "Info"])).toOption
  let guard ← (groupedModel.elaborateCheckedComputationCondition ["Form"] ["Form", "Info"] surface).toOption
  pure (computationProducerProtection groupedModel (fun _ => 6) (fun guard => [some guard]) [guard]
    6 { path := ["Form", "Info"], origin := .path } CheckedComputationPredicate.groupReference?)

example : producerProtection "GroupFilled(Info)" = some true ∧
    producerProtection "Sum(Rows*/N Having [Rows/N] > 0 And GroupFilled(Info)) > 0" = some false := by
  native_decide

example : ["AtLeastOneGroupFilled(Rows*)", "NoGroupFilled(Rows*)"].all (fun predicate =>
    groupAdmission groupedModel ("[Rows/N] > 0 And " ++ predicate) == .admitted) = true ∧
    runModel groupedModel "[Rows/N] > 0 And AtLeastOneGroupFilled(Rows*)" false "" "" ""
      (ruleExpected := "14") = some (.fired .omission, ["value 14"]) ∧
    runModel groupedModel "[Rows/N] > 0 And NoGroupFilled(Rows*)" false "" "" ""
      (ruleExpected := "0") = some (.fired .omission, ["value 0"]) := by native_decide

private def groupStarRows (values : List String) : Array Json :=
  ((["2", "5", "7", "11"].zip values).map fun (n, value) => Json.mkObj [
    ("N", .str n), ("Info", Json.mkObj [("Value", .str value)])]).toArray

private def groupStarMatrix (operands : String) (rows : Array Json)
    (validationNo computationNo validationSome computationSome : String)
    (extra : List (String × Json) := []) : Bool :=
  [("NoGroupFilled", validationNo, computationNo),
    ("AtLeastOneGroupFilled", validationSome, computationSome)].all fun (operator, validation, computation) =>
      runModel candidateModel ("FieldFilled(Rows/N) And " ++ operator ++ "(" ++ operands ++ ")")
        false "" "" "" (ruleExpected := validation) (rowsOverride := some rows) (extra := extra) ==
          some (.fired .omission, ["value " ++ computation])

example : groupStarMatrix "Rows*" candidateRows "0" "0" "14" "14" ∧
    groupStarMatrix "Rows*/Info" candidateRows "0" "0" "14" "14" ∧
    groupStarMatrix "Rows*, Rows*" candidateRows "0" "0" "14" "14" ∧
    groupStarMatrix "Rows*/Info, Rows*/Info" candidateRows "0" "0" "14" "14" ∧
    groupStarMatrix "Rows*/Info, Rows*/Other" candidateRows "0" "0" "14" "14" ∧
    groupStarMatrix "Rows*/Info" (groupStarRows ["", "", ""]) "14" "14" "0" "0" ∧
    groupStarMatrix "Rows*/Info" (groupStarRows ["bad", "", ""]) "0" "0" "0" "14" ∧
    groupStarMatrix "Rows*/Info" (groupStarRows ["", "", "", "3"]) "14" "14" "0" "0" ∧
    groupStarMatrix "Rows*, Info, Other/Value" candidateRows "0" "0" "14" "14" ∧
    groupStarMatrix "Rows*/Info, Info, Other/Value" (groupStarRows ["", "", ""])
      "0" "0" "14" "14" [("Other", Json.mkObj [("Value", .str "3")])] := by native_decide

private def groupStarRead (predicate : String) (rows : Array Json)
    (extra : List (String × Json) := []) : Option (K × ComputationConditionResult) := do
  let dm : DmModel := {
    flat := candidateModel, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let input ← (readDocument dm (Json.mkObj [("Form", Json.mkObj (("Rows", .arr rows) :: extra))])).toOption
  if !input.refusals.isEmpty then none
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler candidateModel).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  let parsed ← (parseText .english (predicate ++ " And FieldFilled(Rows/N)")).toOption
  let authored ← (lowerHaving parsed.body).toOption
  let path ← (elaborateStarFieldPath candidateModel ["Form"] {
    base := .relative 0, groups := [{ name := "Rows", starred := true }], field := "N" }).toOption
  let checked ← (elaborateStarHavingCore candidateModel ["Form"] path authored).toOption
  let .and (.leaf leaf@(.groupFill _ _ _)) _ := checked.condition | none
  let frame : CorrelationFrame := { innerEnv := [(10, 1)], outerEnv := [] }
  pure (← (leaf.evalTruthInResolving document.resolvingCorrelationContext frame).toOption,
    ← (leaf.evalComputationInResolving document.resolvingCorrelationContext frame).toOption)

example : ["Rows*", "Rows*/Info"].all (fun operand =>
    groupStarRead ("NoGroupFilled(" ++ operand ++ ")") #[] == some (.tru, .holds) &&
    groupStarRead ("AtLeastOneGroupFilled(" ++ operand ++ ")") #[] == some (.unknown, .notTrue)) = true ∧
    [#[Json.mkObj []], #[Json.mkObj [("N", .str "bad")]]].all (fun rows =>
      groupStarRead "AtLeastOneGroupFilled(Rows*)" rows == some (.tru, .holds) &&
      groupStarRead "NoGroupFilled(Rows*)" rows == some (.unknown, .notTrue)) = true ∧
    groupStarRead "NoGroupFilled(Rows*/Info)" (groupStarRows ["bad"]) = some (.unknown, .notTrue) ∧
    groupStarRead "AtLeastOneGroupFilled(Rows*/Info)" (groupStarRows ["bad"]) = some (.unknown, .holds) := by
  native_decide

example : groupStarRead "AtLeastOneGroupFilled(Rows*, Info/Value)" candidateRows
      [("Info", Json.mkObj [("Value", .str "bad")])] = some (.tru, .holds) ∧
    groupStarRead "AtLeastOneGroupFilled(Info/Value, Rows*)" candidateRows
      [("Info", Json.mkObj [("Value", .str "bad")])] = some (.tru, .poison .malformed) ∧
    groupStarRead "NoGroupFilled(Rows*, Info/Value)" candidateRows
      [("Info", Json.mkObj [("Value", .str "bad")])] = some (.unknown, .notTrue) ∧
    groupStarRead "NoGroupFilled(Info/Value, Rows*)" candidateRows
      [("Info", Json.mkObj [("Value", .str "bad")])] = some (.unknown, .poison .malformed) := by
  native_decide

private def groupStarDeclarations : FlatModel := { candidateModel with
  fields := candidateModel.fields ++ [{
    id := 12, groupPath := ["Form", "Rows", "Descendant", "Child"], name := "Value", repeatableScope := [10],
    policy := { kind := .number { scale := 0, signed := true } } }]
  repeatableGroups := candidateModel.repeatableGroups ++ [{
    level := 40, path := ["Form", "Hollow"], repeatability := some 2 }] }

private def groupCategoryModel : FlatModel := { candidateModel with fields := candidateModel.fields.map fun field =>
  if field.id == 6 then { field with policy := { kind := .enumeration }, enumeration := some {
    storedTokens := ["1", "2"], categories := [{ name := "Label", tokens := ["one", "two"] }] } } else field }

example : ["NoGroupFilled", "AtLeastOneGroupFilled"].all (fun operator =>
    ["Rows*", "Rows*/Info", "Rows*, Rows*", "Rows*/Info, Rows*/Info", "Rows*, Info, Other/Value"].all
      (fun operands => groupAdmission candidateModel
        ("FieldFilled(Rows/N) And " ++ operator ++ "(" ++ operands ++ ")") == .admitted) &&
    groupAdmission candidateModel (operator ++ "(Rows*)") == .refused (some .noIterationForWildcard) &&
    groupAdmission candidateModel (operator ++ "(Rows*/Info)") == .refused (some .noIterationForWildcard) &&
    groupAdmission candidateModel ("FieldFilled(Rows/N) And " ++ operator ++ "(Info, Info)") ==
      .refused (some .duplicateParam1) &&
    groupAdmission candidateModel ("FieldFilled(Rows/N) And " ++ operator ++ "(Rows*/Info, Rows/Info/Value)") ==
      .refused (some .duplicateParam2) &&
    groupAdmission candidateModel ("FieldFilled(Rows/N) And " ++ operator ++ "(Rows*, $/Form/Rows*/Info)") ==
      .refused (some .duplicateParam2) &&
    groupAdmission groupCategoryModel ("FieldFilled(Rows/N) And " ++ operator ++ "(Rows*, Info/Value -> Label)") ==
      .refused (some .categoryNotAllowed) &&
    groupAdmission groupCategoryModel ("FieldFilled(Rows/N) And " ++ operator ++ "(Rows*, Info/Value)") == .admitted &&
    groupAdmission groupStarDeclarations ("FieldFilled(Rows/N) And " ++ operator ++ "(Rows*/Descendant)") == .admitted &&
    groupAdmission groupStarDeclarations ("FieldFilled(Rows/N) And " ++ operator ++ "(Hollow*)") ==
      .refused (some .groupIsEmpty)) = true := by native_decide

example : ["AllGroupsFilled", "NotAllGroupsFilled", "GroupsNotCollectivelyFilled"].all (fun operator =>
    ["Rows*, Info", "Rows*/Info, Info"].all (fun operands =>
      groupAdmission candidateModel ("FieldFilled(Rows/N) And " ++ operator ++ "(" ++ operands ++ ")") ==
        .refused (some .noWildcardsGAllowed)) &&
    groupAdmission groupCategoryModel ("FieldFilled(Rows/N) And " ++ operator ++ "(Info/Value -> Label, Other)") ==
      .refused (some .categoryNotAllowed)) = true ∧
    groupAdmission candidateModel "FieldFilled(Rows/N) And GroupFilled(Rows*)" =
      .readerRefused "Having" "group path" := by native_decide

private def nestedGroupModel : FlatModel := { model with
  fields := (model.fields.map fun field => if field.id == 5 then
    { field with groupPath := ["Form", "Rows"], repeatableScope := [10] } else field) ++ [{
      id := 11, groupPath := ["Form", "Rows", "Bucket", "Items"], name := "C", repeatableScope := [10, 20],
      policy := { kind := .number { scale := 0, signed := true } } }]
  repeatableGroups := model.repeatableGroups ++ [{
    level := 20, path := ["Form", "Rows", "Bucket", "Items"], repeatability := some 2 }] }

private def nestedGroupFilter (operator operand : String) :=
  operator ++ "(" ++ operand ++ ") And FieldFilled(N)"

private def nestedGroupRun (operator operand : String) : Option (List Bool × List String) := do
  let world : World := { now := { epochMillis := 0 } }
  let dm : DmModel := {
    flat := nestedGroupModel, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let row (n : String) (values : List String) := Json.mkObj [
    ("N", .str n), ("Tag", .str "x"), ("Out", .str "99"), ("Bucket", Json.mkObj [
      ("Items", .arr ((values.map fun value => Json.mkObj [("C", .str value)]).toArray))])]
  let input ← (readDocument dm (Json.mkObj [("Form", Json.mkObj [
    ("Rows", .arr #[row "2" ["1", "1"], row "5" ["2"], row "13" []])])])).toOption
  if !input.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler nestedGroupModel).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  let operation := "Sum(/Form/Rows*/N Having " ++ nestedGroupFilter operator operand ++ ")"
  let rule ← (checkRule dm .english {
    group := ["Form", "Rows"], name := "Nested", errorCode := "NESTED", errorEntityRelPath := "../N",
    condition := "FieldFilled(N) And " ++ operation ++ " > 0", severity := "ERROR" } world).toOption
  let verdicts ← (rule.evalOrdinaryRepeatableFull document (some world)).toOption
  let (_, computation) ← (lowerComputation nestedGroupModel .english {
    group := ["Form", "Rows"], name := "Nested", targetRelPath := "../Out", commonPrecondition := none,
    alternatives := [{ precondition := none, operation }], errorCodesToSuppress := [] }).toOption
  let outcomes ← (runComputations world prepared document [computation]).toOption
  pure (verdicts.map (fun result => result.2.verdict.keepsHaving), outcomes.map (·.outcome))

example : ["Bucket", "Bucket/Items*"].all (fun operand =>
    nestedGroupRun "AtLeastOneGroupFilled" operand == some ([true, true, true], ["value 7", "value 7", "value 7"]) &&
    nestedGroupRun "AtLeastOneGroupFilled" ("$" ++ operand) ==
      some ([true, true, false], ["value 20", "value 20", "value 0"]) &&
    nestedGroupRun "NoGroupFilled" operand == some ([true, true, true], ["value 13", "value 13", "value 13"]) &&
    nestedGroupRun "NoGroupFilled" ("$" ++ operand) ==
      some ([false, false, true], ["value 0", "value 0", "value 20"])) = true := by native_decide

private def nestedGroupReferences (operator operand : String) :
    Option (Option (List RepeatableLevel) × Bool × Bool) := do
  let filter := nestedGroupFilter operator operand
  let parsed ← (parseText .english ("FieldValuesNotUnique(/Form/Rows*/Tag Having " ++ filter ++ ")")).toOption
  let checked ← (lowerCondition nestedGroupModel ["Form", "Rows"] false parsed.body).toOption
  let numeric ← (parseText .english ("Sum(/Form/Rows*/N Having " ++ filter ++ ") > 0")).toOption
  let numericChecked ← (lowerCondition nestedGroupModel ["Form", "Rows"] false numeric.body).toOption
  let scope ← numericChecked.core.ordinaryIterationScope.toOption
  let pointers ← (checked.core.referencePointers [(10, 2)]).toOption
  pure (scope, pointers.contains { field := 11, coordinates := [.wildcard, .wildcard] },
    pointers.contains { field := 11, coordinates := [.concrete 2, .wildcard] })

example : ["NoGroupFilled", "AtLeastOneGroupFilled"].all (fun operator =>
    ["Bucket", "Bucket/Items*"].all (fun operand =>
      nestedGroupReferences operator operand == some (none, true, false) &&
      nestedGroupReferences operator ("$" ++ operand) == some (some [10], false, true))) = true := by
  native_decide

private def freshGroupStar (operator expected : String) : Option (Verdict × List String) := do
  let world : World := { now := { epochMillis := 0 } }
  let dm : DmModel := {
    flat := candidateModel, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let input ← (readDocument dm (Json.mkObj [("Form", Json.mkObj [
    ("Error", .str "ready"), ("Rows", .arr (groupStarRows ["", "", ""]))])])).toOption
  if !input.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler candidateModel).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  let operation := "Sum(Rows*/N Having FieldFilled(Rows/N) And " ++ operator ++ "(Rows*/Info))"
  let rule ← (checkRule dm .english {
    group := ["Form"], name := "Fresh", errorCode := "FRESH", errorEntityRelPath := "../Error",
    condition := "FieldFilled(Error) And " ++ operation ++ " == " ++ expected, severity := "ERROR" } world).toOption
  let context : AddressedValidationEvaluationContext candidateModel := {
    scalar := { fields := document.flatContext.withWorld world, groups := GroupPresenceContext.unavailable }
    outer := [], input := .checked document }
  let verdict := (← (rule.evalAddressedFull context true).toOption).verdict
  let computation (name : String) (group : GroupPath) (target operation : String) := lowerComputation candidateModel .english {
    group, name, targetRelPath := target, commonPrecondition := none,
    alternatives := [{ precondition := none, operation }], errorCodesToSuppress := [] }
  let (_, consumer) ← (computation "Consumer" ["Form"] "../Out" operation).toOption
  let (_, producer) ← (computation "Producer" ["Form", "Rows", "Info"] "../Value" "4").toOption
  let outcomes ← (runComputations world prepared document [consumer, producer]).toOption
  pure (verdict, outcomes.map (·.outcome))

example : freshGroupStar "AtLeastOneGroupFilled" "0" =
      some (.fired .omission, ["value 4", "value 4", "value 4", "value 14"]) ∧
    freshGroupStar "NoGroupFilled" "14" =
      some (.fired .omission, ["value 4", "value 4", "value 4", "value 0"]) := by native_decide

private def groupStarCertificate : Option (List Bool) := do
  let parsed ← (parseText .english "AtLeastOneGroupFilled(Rows*/Info) And FieldFilled(Rows/N)").toOption
  let authored ← (lowerHaving parsed.body).toOption
  let path ← (elaborateStarFieldPath candidateModel ["Form"] {
    base := .relative 0, groups := [{ name := "Rows", starred := true }], field := "N" }).toOption
  let checked ← (elaborateStarHavingCore candidateModel ["Form"] path authored).toOption
  let .and (.leaf (.groupFill _ (.group origin source) [])) _ := checked.condition | none
  let test (source : ComputationGroupOperand) (operator := GroupFillQuantifier.atLeastOneGroupFilled) :=
    (CorrelatedHavingLeaf.groupFill operator (.group origin source) []).wellFormedForEnvironments candidateModel [10] []
  pure [test source, test { source with members := [] },
    test { source with content := { source.content with rowLevels := [10] } },
    test { source with starPath := some { axes := [{ level := 10, repeatability := some 4 }], firstStar := 0 } },
    test { source with dependencyKind := .conditionalPresence },
    [GroupFillQuantifier.allGroupsFilled, .notAllGroupsFilled, .groupsNotCollectivelyFilled].all (fun operator =>
      let second := HavingGroupOperand.field { origin := .inner, field := 6 }
      let checked (first : ComputationGroupOperand) :=
        (CorrelatedHavingLeaf.groupFill operator (.group origin first) [second]).wellFormedForEnvironments candidateModel [10] []
      checked { source with starPath := none } && !checked source),
    (CorrelatedHavingLeaf.groupPresence .filled origin { source with dependencyKind := .conditionalPresence }).wellFormedForEnvironments candidateModel [10] []]

example : groupStarCertificate = some [true, false, false, false, false, true, false] := by native_decide

end A12Kernel.Dm.HavingGroupLocks
