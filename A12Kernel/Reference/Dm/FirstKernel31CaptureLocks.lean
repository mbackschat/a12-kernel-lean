import A12Kernel.Reference.Dm.Validate
import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.Replay

/-! # The first kernel 31.1.1 runtime capture

The [retained capture](../../../evidence/kernel-31.1.1/captures/first-calibration-2026-11-04/request.json)
runs one claims model on both kernel strategies, which agree on every row. It settles two clauses the
31.1.1 migration had derived. A "SumOfTerms" computation whose term divides by zero in a row adds
nothing for that row and is not poison
([spec/07 §3.10](../../../spec/07-repetition-and-iteration.md#310-sumofterms)). Partial validation
skips a filtered "Sum", a filtered "NumberOfFilledFields" and a filtered value list, while each
unfiltered twin fires
([spec/10 §5.2](../../../spec/10-validation-and-polarity.md#52-which-rules-run-and-where)).
Each document is the capture's own JSON text.
-/

namespace A12Kernel.Dm.FirstKernel31CaptureLocks

private def number (id : Nat) (name : String) (groupPath : GroupPath) (scope : List Nat := []) : FlatFieldDecl :=
  { id, name, groupPath, repeatableScope := scope, policy := { kind := .number { scale := 0, signed := true } } }

private def text (id : Nat) (name : String) (groupPath : GroupPath) (scope : List Nat := []) : FlatFieldDecl :=
  { id, name, groupPath, repeatableScope := scope, policy := { kind := .string } }

/-- The capture's "Claims31_DM": a policy with a claim list of four, every Number of scale 0. -/
private def model : FlatModel :=
  { fields := [text 1 "Holder" ["Policy"], number 2 "Cap" ["Policy"], number 3 "Total" ["Policy"],
      text 4 "Status" ["Policy", "Claims"] [10], number 5 "Amount" ["Policy", "Claims"] [10],
      number 6 "Reserve" ["Policy", "Claims"] [10]]
    repeatableGroups := [{ level := 10, path := ["Policy", "Claims"], repeatability := some 4 }] }

example : model.validate.isOk = true := by native_decide

private def world : World := { now := { epochMillis := 0 } }

private def dm : DmModel :=
  { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }

private def checked (document : String) := do
  let json ← (Lean.Json.parse document).toOption
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let data ← (readDocument dm json).toOption
  let checked ← (checkDocument prepared "en_US" data.data).toOption
  pure (prepared, checked)

private def dmRule (code errorPath condition : String) : DmRule :=
  { group := ["Policy"], name := code, errorCode := code,
    errorEntityRelPath := "../" ++ errorPath, condition := condition, severity := "ERROR" }

/-- The capture's rules in its rule order: each filtered operand beside its unfiltered twin. -/
private def rules : List (String × String × String) := [
  ("PS", "Cap", "FieldFilled(Cap) And Sum(Claims*/Amount Having [Claims/Status] == \"open\") > [Cap]"),
  ("PS0", "Cap", "FieldFilled(Cap) And Sum(Claims*/Amount) > [Cap]"),
  ("PC", "Cap", "FieldFilled(Cap) And NumberOfFilledFields(Claims*/Amount Having [Claims/Status] == \"open\") > [Cap]"),
  ("PC0", "Cap", "FieldFilled(Cap) And NumberOfFilledFields(Claims*/Amount) > [Cap]"),
  ("PV", "Holder", "FieldFilled(Holder) And NoFieldValueIncludedInValueList(Claims*/Status Having [Claims/Amount] > 5 In \"open\")"),
  ("PV0", "Holder", "FieldFilled(Holder) And NoFieldValueIncludedInValueList(Claims*/Status In \"open\")")]

private def messageType (message : FlatRuleMessage) : String :=
  match message.messageType with | .value => "V" | .omission => "O"

/-- The rules full validation fires, as "code|type" in rule order. -/
private def fullFired (document : String) : List String :=
  match checked document with
  | none => ["no document"]
  | some (_, checked) => rules.flatMap fun (code, errorPath, condition) =>
    match checkRule dm .english (dmRule code errorPath condition) with
    | .error _ => [code ++ " refused"]
    | .ok rule =>
      match runRuleAt world checked rule with
      | .error _ => [code ++ " failed"]
      | .ok rows => rows.map fun (_, message) => code ++ "|" ++ messageType message

private def relevant (path : List String) (reps : List Nat) : RelevantEntityPattern :=
  { path := "Policy" :: path, indices := reps.map fun n => if n == 0 then .all else .concrete n }

/-- The capture's relevance set: every field and the claim group, at every instance. -/
private def coverage : List RelevantEntityPattern :=
  [relevant ["Holder"] [1, 1], relevant ["Cap"] [1, 1], relevant ["Total"] [1, 1],
   relevant ["Claims"] [1, 0], relevant ["Claims", "Status"] [1, 0, 1],
   relevant ["Claims", "Amount"] [1, 0, 1], relevant ["Claims", "Reserve"] [1, 0, 1]]

/-- The rules partial validation fires over "coverage", as "code|type", sorted as the capture sorts them. -/
private def partialFired (document : String) : List String :=
  match checked document with
  | none => ["no document"]
  | some (_, checked) => (rules.flatMap fun (code, errorPath, condition) =>
    match checkValidationRule dm .english (dmRule code errorPath condition) world with
    | .error _ => [code ++ " refused"]
    | .ok rule =>
      match runRulePartial world checked coverage rule with
      | .error _ => [code ++ " failed"]
      | .ok messages => messages.map fun message => code ++ "|" ++ messageType message).mergeSort

/-- The value the capture's computation of "Total" leaves. -/
private def computed (document : String) : List String :=
  match checked document with
  | none => ["no document"]
  | some (prepared, checked) =>
    let operation := "RoundDown(SumOfTerms(Claims*, [Claims/Amount] / [Claims/Reserve]), 0)"
    let computation : DmComputation := {
      name := "TotalComp", group := ["Policy"], targetRelPath := "../Total", commonPrecondition := none,
      alternatives := [{ precondition := none, operation }], errorCodesToSuppress := [] }
    match lowerComputation model .english computation with
    | .error _ => ["refused"]
    | .ok step =>
      match runComputations world prepared checked [step.2] with
      | .error _ => ["failed"]
      | .ok outcomes => outcomes.map (·.outcome)

/-- The capture's rows: document, full firings, partial firings and computed outcome. -/
private def rows : List (String × List String × List String × List String) := [
  ("{\"Policy\":{\"Claims\":[{\"Status\":\"open\",\"Amount\":10,\"Reserve\":2},{\"Status\":\"open\",\"Amount\":6,\"Reserve\":0}]}}",
    [], [], ["value 5"]),
  ("{\"Policy\":{\"Claims\":[{\"Status\":\"open\",\"Amount\":10,\"Reserve\":2},{\"Status\":\"open\",\"Amount\":6,\"Reserve\":3}]}}",
    [], [], ["value 7"]),
  ("{\"Policy\":{\"Claims\":[{\"Status\":\"open\",\"Amount\":6,\"Reserve\":0}]}}",
    [], [], ["value 0"]),
  ("{\"Policy\":{\"Claims\":[{\"Status\":\"open\",\"Amount\":10,\"Reserve\":2},{\"Status\":\"open\",\"Amount\":6}]}}",
    [], [], ["value 5"]),
  ("{\"Policy\":{\"Holder\":\"h\",\"Cap\":1,\"Claims\":[{\"Status\":\"open\",\"Amount\":3,\"Reserve\":1},{\"Status\":\"open\",\"Amount\":4,\"Reserve\":1},{\"Status\":\"closed\",\"Amount\":10,\"Reserve\":1}]}}",
    ["PS|O", "PS0|O", "PC|O", "PC0|V", "PV|O"], ["PC0|V", "PS0|O"], ["value 17"]),
  ("{\"Policy\":{\"Holder\":\"h\",\"Cap\":100,\"Claims\":[{\"Status\":\"closed\",\"Amount\":10,\"Reserve\":1},{\"Status\":\"closed\",\"Amount\":8,\"Reserve\":1}]}}",
    ["PV|O", "PV0|O"], ["PV0|O"], ["value 18"])]

-- Locked: the capture's computation outcomes, both strategies. The first and fourth rows are the
-- separating ones: a row dividing by zero, or by an empty divisor, adds nothing, where a poison
-- account would clear the target; a sum whose only row divides by zero is 0, not cleared.
example : rows.all (fun (document, _, _, outcome) => computed document == outcome) = true := by
  native_decide

-- Locked: the capture's full-validation firings, both strategies. Every filtered rule fires here, so
-- its silence in partial validation below is the filter skip, not a false condition.
example : rows.all (fun (document, full, _, _) => fullFired document == full) = true := by
  native_decide

-- Locked: the capture's partial-validation firings over every field and the claim group, both
-- strategies. "PS", "PC" and "PV" are skipped; their unfiltered twins "PS0", "PC0" and "PV0" fire.
example : rows.all (fun (document, _, part, _) => partialFired document == part) = true := by
  native_decide

end A12Kernel.Dm.FirstKernel31CaptureLocks
