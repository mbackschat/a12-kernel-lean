import A12Kernel.Reference.Dm.HavingFixture
import A12Kernel.Reference.Dm.Validate

namespace A12Kernel.Dm.BooleanCountHavingLocks
open A12Kernel A12Kernel.Dm Lean

private def model (kind : FieldKind) : FlatModel := {
  HavingFixture.model with
  fields := HavingFixture.model.fields.map (fun field =>
    if field.id == 3 then { field with policy := { kind } }
    else if field.id == 5 then { field with groupPath := ["Form", "Rows"], repeatableScope := [10] }
    else field) ++ [
      { id := 6, name := "N", groupPath := ["Form"],
        policy := { kind := .number { scale := 0, signed := true } } }] }

private structure Scenario where
  kind : FieldKind := .boolean
  tags : List String := ["true", "true", "false"]
  localGroup : Bool := false
  repeated : Bool := true

private inductive RunError where
  | input | inputRefusal | preparation | document | rule | validation | computation | execution
  deriving Repr, BEq, DecidableEq

private inductive Result where
  | validation (verdicts : List Verdict) (pointers : List String)
  | computation (outcomes : List String)
  deriving Repr, BEq, DecidableEq

private def executeCore (expression : String) (computation : Bool)
    (scenario : Scenario := {}) : Except RunError Result := do
  let model := model scenario.kind
  let dm : DmModel := {
    flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let rows := (scenario.tags.zip ["2", "5", "7"]).map fun (tag, n) =>
    Json.mkObj [("Tag", .str tag), ("N", .str n), ("Out", .str "99")]
  let input ← (readDocument dm (Json.mkObj [("Form", Json.mkObj [
    ("N", .str "4"), ("Rows", .arr rows.toArray)])])).mapError fun _ => .input
  if !input.refusals.isEmpty then throw .inputRefusal
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).mapError fun _ => .preparation
  let document ← (checkDocument prepared "en_US" input.data).mapError fun _ => .document
  let group := if scenario.localGroup then ["Form", "Rows"] else ["Form"]
  if computation then
    let (_, step) ← (lowerComputation model .english {
      group, name := "Count", targetRelPath := if scenario.repeated then
        (if scenario.localGroup then "../Out" else "../Rows/Out") else "../N",
      commonPrecondition := none, alternatives := [{ precondition := none, operation := expression }],
      errorCodesToSuppress := [] }).mapError fun _ => .computation
    let outcomes ← (runComputations world prepared document [step]).mapError fun _ => .execution
    pure (.computation (outcomes.map (·.outcome)))
  else
    let checked ← (checkRule dm .english {
      group, name := "Count", errorCode := "COUNT",
      errorEntityRelPath := if scenario.repeated then
        (if scenario.localGroup then "../N" else "../Rows/N") else "../N",
      condition := "FieldFilled(" ++ (if scenario.localGroup || !scenario.repeated then "N" else "Rows/N") ++
        ") And " ++ expression ++ " > 0", severity := "ERROR" }).mapError fun _ => .rule
    let rows ← (checked.evalOrdinaryRepeatableFull document (some world)).mapError fun _ => .validation
    let messages ← (runRule world document checked).mapError fun _ => .validation
    pure (.validation (rows.map (·.2.verdict)) (messages.map fun message => (observe model message).pointer))

private def execute (expression : String) (computation : Bool)
    (scenario : Scenario := {}) : Sum RunError Result :=
  match executeCore expression computation scenario with
  | .error error => .inl error
  | .ok result => .inr result

private def count (expected : Bool) (filter : String := "") : String :=
  "NumberOfValueInFields(" ++ (if expected then "True" else "False") ++ " In Rows*/Tag" ++
    (if filter.isEmpty then "" else " Having " ++ filter) ++ ")"

private def capturedField := "[Rows/N] > [$Rows/N]"
private def capturedRepetition := "CurrentRepetition(Rows) > CurrentRepetition($Rows)"
private def firstPointer := "Form/Rows/N"
private def secondPointer := "Form/Rows[2]/N"

example : execute (count true) true = .inr (.computation ["value 2", "value 2", "value 2"]) ∧
    execute (count false) true = .inr (.computation ["value 1", "value 1", "value 1"]) ∧
    execute (count true) false = .inr (.validation
      [.fired .value, .fired .value, .fired .value] [firstPointer, secondPointer, "Form/Rows[3]/N"]) := by native_decide

example : execute "NumberOfValueInFields(True In /Form/Rows*/Tag Having [N] > [$N])" true
      { localGroup := true } = .inr (.computation ["value 1", "value 0", "value 0"]) ∧
    execute "NumberOfValueInFields(True In /Form/Rows*/Tag Having [N] > [$N])" false
      { localGroup := true } = .inr (.validation [.fired .omission, .notFired, .notFired] [firstPointer]) := by native_decide

example : execute (count true capturedField) true =
    .inr (.computation ["value 1", "value 0", "value 0"]) := by native_decide

example : execute (count true capturedField) false =
    .inr (.validation [.fired .omission, .notFired, .notFired] [firstPointer]) := by native_decide

example : execute (count true capturedRepetition) true =
    .inr (.computation ["value 1", "value 0", "value 0"]) := by native_decide

example : execute (count true capturedRepetition) false =
    .inr (.validation [.fired .omission, .notFired, .notFired] [firstPointer]) := by native_decide

example : [capturedField, capturedRepetition].all (fun filter =>
    execute (count false filter) true == .inr (.computation ["value 1", "value 1", "value 0"]) &&
    execute (count false filter) false == .inr (.validation
      [.fired .omission, .fired .omission, .notFired] [firstPointer, secondPointer])) = true := by native_decide

example : execute (count true "[Rows/N] > [N] And CurrentRepetition(Rows) != CurrentRepetition($Rows)") true =
    .inr (.computation ["value 1", "value 0", "value 1"]) ∧
    execute (count true "[Rows/N] > [N] And CurrentRepetition(Rows) != CurrentRepetition($Rows)") false =
    .inr (.validation [.fired .omission, .notFired, .fired .omission] [firstPointer, "Form/Rows[3]/N"]) := by native_decide

example : execute (count true capturedField) true { kind := .confirm, tags := ["true", "true", ""] } =
    .inr (.computation ["value 1", "value 0", "value 0"]) ∧
    execute (count true capturedField) false { kind := .confirm, tags := ["true", "true", ""] } =
    .inr (.validation [.fired .omission, .notFired, .notFired] [firstPointer]) ∧
    execute (count false capturedField) true { kind := .confirm } = .inl .computation ∧
    execute (count false capturedField) false { kind := .confirm } = .inl .rule := by native_decide

example : execute (count true capturedField) true { tags := ["true", "bad", "false"] } =
    .inr (.computation ["cleared", "value 0", "value 0"]) ∧
    execute (count true capturedField) false { tags := ["true", "bad", "false"] } =
    .inr (.validation [.unknown, .notFired, .notFired] []) := by native_decide

example : [capturedField, capturedRepetition].all (fun filter =>
    execute (count true filter) true { repeated := false } == .inl .computation &&
    execute (count true filter) false { repeated := false } == .inl .rule) = true := by native_decide

example : execute "NumberOfValueInFields(True In Rows/Tag, Rows*/Tag)" false =
    .inr (.validation [.fired .value, .fired .value, .fired .value]
      [firstPointer, secondPointer, "Form/Rows[3]/N"]) ∧
    execute "NumberOfValueInFields(True In Rows*/Tag, Rows/Tag)" false =
    .inr (.validation [.fired .value, .fired .value, .fired .value]
      [firstPointer, secondPointer, "Form/Rows[3]/N"]) := by native_decide

example : execute ("NumberOfValueInFields(True In Rows/Tag, Rows*/Tag Having " ++ capturedRepetition ++ ")") false =
    .inr (.validation [.fired .omission, .fired .value, .notFired] [firstPointer, secondPointer]) ∧
    execute ("NumberOfValueInFields(True In Rows/Tag, Rows*/Tag Having " ++ capturedRepetition ++ ")") true =
    .inr (.computation ["value 2", "value 1", "value 0"]) := by native_decide

end A12Kernel.Dm.BooleanCountHavingLocks
