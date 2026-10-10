import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document

namespace A12Kernel.Dm.EmptyPatternLocks
open Lean A12Kernel

private def model : FlatModel := {
  fields := [
    { id := 0, name := "Gate", groupPath := ["Form"], policy := { kind := .string } },
    { id := 1, name := "Text", groupPath := ["Form"], policy := { kind := .string },
      stringPolicy := { maxLength := some 3 } },
    { id := 2, name := "Out", groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 3, name := "Alternative", groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 4, name := "Independent", groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 5, name := "Tail", groupPath := ["Form"], policy := { kind := .string } }] }

private def dm : DmModel := {
  flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
private def world : World := { now := { epochMillis := 0 } }
private def input (text : Option String := some "123") : Except String DmDocument :=
  readDocument dm (Json.mkObj [("Form", Json.mkObj
    ([("Gate", .str "ready"), ("Tail", .str "ready"), ("Out", .str "9"), ("Alternative", .str "9"), ("Independent", .str "9")] ++
      text.toList.map ("Text", Json.str ·)))])

private def checked (text : Option String := some "123") : Option (CheckedDocument model) := do
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let raw ← (input text).toOption
  if !raw.refusals.isEmpty then none
  (checkDocument prepared "en_US" raw.data).toOption

private def pattern (op : String) (source : String := "") : String :=
  s!"[Text] {op} \"{source}\""
private def rule (condition : String) (errorField : String := "Gate") :
    Lowering (CheckedResolvedValidationRule model) :=
  checkRule dm .english {
    name := "Pattern", group := ["Form"], errorCode := "PATTERN", errorEntityRelPath := "../" ++ errorField,
    condition, severity := "ERROR" } world

private def full (condition : String) : Option (List String) := do
  let document ← checked
  let rule ← (rule condition).toOption
  pure ((← (runRule world document rule).toOption).map fun message => (observe model message).messageType)

private def leafResult (condition : String) : Option (Sum CheckedAddressingError Verdict) := do
  let document ← checked
  let parsed ← (parseText .english condition).toOption
  let condition ← (lowerCondition model ["Form"] false parsed.body (world := world)).toOption
  let .leaf leaf := condition.core | none
  pure (match leaf.evalAddressed {
    scalar := { fields := document.flatContext.withWorld world, groups := GroupPresenceContext.unavailable },
    outer := [], input := .checked document } with
      | .error error => .inl error
      | .ok verdict => .inr verdict)

private def part (condition errorField : String) (relevant : List String) : Option (Option Verdict) := do
  let raw ← (input).toOption
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let rule ← (rule condition errorField).toOption
  let fields : RawFlatContext := { read := fun field =>
    ((raw.data.cells.find? fun cell => cell.address.field == field).map (·.raw)).getD .empty }
  let result ← (rule.evalPartial prepared "en_US" fields GroupPresenceContext.unavailable
    (.partialSet (relevant.map fun field => RelevantEntityPattern.allInstances ["Form", field]))).toOption
  pure (match result with | .skipped => none | .evaluated outcome => some outcome.verdict)

private def computations (op source : String) : List DmComputation :=
  let guard := pattern op source
  [ { name := "Common", group := ["Form"], targetRelPath := "../Out", commonPrecondition := some guard,
      alternatives := [{ precondition := none, operation := "1" }], errorCodesToSuppress := [] },
    { name := "Alternative", group := ["Form"], targetRelPath := "../Alternative", commonPrecondition := none,
      alternatives := [{ precondition := some guard, operation := "1" },
        { precondition := some "FieldFilled(Gate)", operation := "2" }], errorCodesToSuppress := [] },
    { name := "Independent", group := ["Form"], targetRelPath := "../Independent", commonPrecondition := none,
      alternatives := [{ precondition := none, operation := "7" }], errorCodesToSuppress := [] } ]

private def compute (op source : String) (text : Option String := some "123") : Option (List String) := do
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let document ← checked text
  let definitions ← (computations op source).mapM fun definition => (lowerComputation model .english definition).toOption
  pure ((← (runComputations world prepared document (definitions.map (·.2))).toOption).map
    (fun result => result.pointer ++ ":" ++ result.outcome)).mergeSort

private def targetOutcome (op : String) (text : Option String) : Option NumericTargetOutcome := do
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let document ← checked text
  let definitions ← (computations op "").mapM fun definition => (lowerComputation model .english definition).toOption
  let steps ← definitions.mapM fun (_, lowered) => match lowered with
    | .number table _ => some (MixedComputationStep.number (compilePattern := builtinStringPatternCompiler) table)
    | _ => none
  let plan ← (certifyAuthoredMixedComputationPlan steps).toOption
  let outcomes ← (plan.execute world prepared.patterns document).toOption
  outcomes.findSome? fun
    | .number entry => if entry.targetField.field == 2 then some entry.outcome else none
    | _ => none

private def formalFindings : Option (List FormalCause) := do
  let document ← checked (some "long")
  pure (← (document.read { field := 1, path := [] }).toOption).findings

example : ["PatternMatched", "PatternViolated"].all (fun op => decide (
    leafResult (pattern op) = some (.inl (.stringExpression .emptyPattern)) ∧
    leafResult (pattern op "[0-9]+") = some (.inr (if op == "PatternMatched" then .fired .value else .notFired)) ∧
    full ("FieldFilled(Gate) And " ++ pattern op) = some ["VALUE_ERROR"] ∧
    full ("FieldFilled(Gate) And FieldNotFilled(Tail) And " ++ pattern op) = some [] ∧
    full ("FieldFilled(Gate) And " ++ pattern op ++ " And FieldNotFilled(Tail)") = some ["VALUE_ERROR"] ∧
    full ("FieldFilled(Gate) And " ++ pattern op "[0-9]+" ++ " And FieldNotFilled(Tail)") = some [] ∧
    part (pattern op ++ " And FieldFilled(Gate)") "Gate" ["Gate"] = some (some (.fired .value)) ∧
    part (pattern op "[0-9]+" ++ " And FieldFilled(Gate)") "Gate" ["Gate"] = some (some .unknown) ∧
    part (pattern op ++ " And FieldFilled(Gate)") "Gate" ["Text"] = some none ∧
    part ("FieldFilled(Gate) Or " ++ pattern op) "Text" ["Text"] = some (some (.fired .value)) ∧
    part ("FieldFilled(Gate) Or " ++ pattern op "[0-9]+") "Text" ["Text"] =
      some (some (if op == "PatternMatched" then .fired .value else .unknown)) ∧
    compute op "" = some ["Form/Alternative:cleared", "Form/Independent:value 7", "Form/Out:cleared"] ∧
    compute op "[0-9]+" = some (if op == "PatternMatched" then
      ["Form/Alternative:value 1", "Form/Independent:value 7", "Form/Out:value 1"] else
      ["Form/Alternative:value 2", "Form/Independent:value 7", "Form/Out:cleared"]) ∧
    compute op "" (some "long") = some ["Form/Alternative:cleared", "Form/Independent:value 7", "Form/Out:cleared"] ∧
    targetOutcome op (some "123") = some (.invalidNoValue .calculationValue) ∧
    targetOutcome op (some "long") = some (.inheritedPoison .declaredConstraint))) = true := by
  native_decide

example : formalFindings = some [.declaredConstraint] := by native_decide

end A12Kernel.Dm.EmptyPatternLocks
