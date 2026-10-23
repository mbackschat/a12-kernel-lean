import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.ParallelValidation

/-! # Custom-condition callbacks against the retained call capture

Each lock runs one rule of the capture's model through the evaluator of its iteration plan, with a
factory whose callback answers true only when it receives the payload the Kernel recorded for that
call: the relevance it passed, the formally incorrect cells and the row-indexed error entity. A
payload this theory constructs differently silences the rule, so the expected findings settle the
payload too. Kernel oracle: the
[custom-condition capture](../../../docs/sources/model-structure-and-declaration-probes.md#src-custom-condition-calls),
whose full-validation messages the population replay also compares.
-/

namespace A12Kernel.Dm.CustomConditionCaptureLocks

private def model : FlatModel :=
  let text (id : Nat) (groupPath : GroupPath) (name : String) (scope : List Nat := []) : FlatFieldDecl :=
    { id, name, groupPath, repeatableScope := scope, policy := { kind := .string } }
  let number (id : Nat) (groupPath : GroupPath) (name : String) (scope : List Nat := []) : FlatFieldDecl :=
    { id, name, groupPath, repeatableScope := scope, policy := { kind := .number { scale := 0, signed := true } } }
  { fields := [text 1 ["Claim"] "Note", number 2 ["Claim"] "Amount", text 3 ["Claim"] "Stage",
      text 4 ["Claim", "Items"] "Name" [10], number 5 ["Claim", "Items"] "Qty" [10]]
    repeatableGroups := [{ level := 10, path := ["Claim", "Items"], repeatability := some 5 }] }

private def item (name qty : String) : Lean.Json :=
  Lean.Json.mkObj [("Name", .str name), ("Qty", .str qty)]

/-- The capture's `doc-full` and `doc-bad`, without the parallel groups this model leaves out. -/
private def document (bad : Bool) : Lean.Json :=
  Lean.Json.mkObj [("Claim", if bad then
      Lean.Json.mkObj [("Note", .str ""), ("Amount", .str "abc"), ("Items", .arr #[item "a" "x", item "b" "2"])]
    else
      Lean.Json.mkObj [("Note", .str "n"), ("Amount", .str "7"), ("Stage", .str "s"),
        ("Items", .arr #[item "a" "1", item "b" "2", item "c" "3"])])]

private def qty (row : Nat) : CellAddr := { field := 5, path := [row] }

private def entity (field : Nat) (path : List Nat := []) : MessagePointer :=
  MessagePointer.ofCellAddr { field, path }

/-- Every error entity the Kernel passed to each name across the capture's three batches. A name
outside this table is unregistered, so a call with an entity the Kernel never passed silences its
rule instead of passing by default. -/
private def recorded : List (String × List MessagePointer) :=
  [("K01", [entity 1]), ("K02", [entity 1]), ("K03", [entity 1]), ("K14", [entity 1]),
    ("K04", [entity 2]), ("K05", [entity 2]), ("K06", [entity 2]), ("K07", [entity 3]), ("K08", [entity 3]),
    ("K11", [entity 4 [1], entity 4 [2], entity 4 [3]]),
    ("K12", [entity 5 [2], entity 5 [3]]), ("K13", [entity 5 [2], entity 5 [3]])]

/-- The Kernel's recorded payload of every true answer, given the `formallyIncorrect` cells it passed. `K02` answers false; `K03` asks whether
`Claim/Amount` is filled, which it is in every document reaching it. `pointers` narrows a name to the
single entity one row passed. -/
private def registry (formal : List CellAddr) (relevance : CustomConditionRelevance ValidationRelevanceScope)
    (pointers : List (String × MessagePointer)) : CustomValidationRegistry model :=
  { configured := some fun name => (recorded.lookup name).map fun entities input =>
      name != "K02" &&
      (match input.relevance, relevance with
        | .all, .all => true
        | .partialEntities actual, .partialEntities expected => actual == expected
        | _, _ => false) &&
      input.formallyIncorrect.length == formal.length && formal.all input.formallyIncorrect.contains &&
      entities.contains input.errorPointer && (pointers.lookup name).all (· == input.errorPointer) }

/-- Full validation runs on the document carrying its generated findings, as the replay does; a
partial call derives its own from `checked`. -/
private def run (world : World) (checked validated : CheckedDocument model) (scope : ValidationRelevanceScope)
    (registry : CustomValidationRegistry model)
    (rule : CheckedResolvedValidationRule model) : Option (List FlatRuleMessage) :=
  match scope with
  | .full => (runRule world validated rule registry).toOption
  | .partialSet _ =>
      match rule.ordinaryIterationPlan with
      | .rows _ => (rule.evalOrdinaryRepeatablePartial checked scope (some world) registry).toOption.map fun
          | .skipped => []
          | .evaluated rows => rows.filterMap fun
              | (_, .evaluated outcome) => outcome.message?
              | (_, .skipped) => none
      | .once _ => (rule.evalOrdinaryOncePartial checked scope (some world) registry).toOption.map fun
          | .skipped => []
          | .evaluated _ outcome => outcome.message?.toList
      | .scalar => (rule.evalAddressedPartial checked scope (some world) registry).toOption.map fun
          | .skipped => []
          | .evaluated outcome => outcome.message?.toList

/-- Each finding as `code type pointer`, a caught failure marked `!`, or `none` when the rule, the
document or the run is refused. `formal` is the call's recorded `formallyIncorrect`: in `doc-bad`,
`Claim/Amount` and the first row's `Qty`. -/
private def fired (group : GroupPath) (errorField condition : String) (scope : ValidationRelevanceScope := .full)
    (bad : Bool := false) (pointers : List (String × MessagePointer) := []) (json : Lean.Json := document bad)
    (formal : List CellAddr := if bad then [{ field := 2, path := [] }, qty 1] else []) : Option (List String) := do
  let dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let world : World := { now := { epochMillis := 0 }, modelZoneRules := ModelZone.concreteRules }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let read ← (readDocument dm json).toOption
  let checked ← (checkDocument prepared "en_US" read.data).toOption
  let validated ← checked.fullValidationDocument.toOption
  let .ok (.ordinary rule) := checkValidationRule dm .english {
      name := "Rule", group, errorCode := "R", errorEntityRelPath := "../" ++ errorField,
      condition, severity := "ERROR" } world | none
  let relevance := match scope with
    | .full => .all
    | .partialSet _ => .partialEntities scope
  let messages ← run world checked validated scope (registry formal relevance pointers) rule
  pure (messages.map fun message =>
    let observed := observe model message
    s!"{observed.messageType} {observed.pointer}{if message.origin == .runtimeFailure then "!" else ""}")

private def claim := ["Claim"]
private def items := ["Claim", "Items"]
private def pointer (row : Nat) : MessagePointer := MessagePointer.ofCellAddr (qty row)
private def relevant (path : List String) (indices : List RelevanceIndex) : ValidationRelevanceScope :=
  .partialSet [{ path := "Claim" :: path, indices }]

/-- A reached unregistered name reports the rule as a caught value failure; a bypassed one reports
nothing. Rules `C09`, `C10` in `f-full` and `f-bad`, whose `Stage` is absent. -/
example :
    fired claim "Note" "FieldFilled(Note) And CustomCondition Ghost" = some ["VALUE_ERROR Claim/Note!"] ∧
    fired claim "Stage" "FieldFilled(Stage) And CustomCondition Ghost" = some ["VALUE_ERROR Claim/Stage!"] ∧
    fired claim "Stage" "FieldFilled(Stage) And CustomCondition Ghost" (bad := true) = some [] ∧
    fired claim "Note" "FieldFilled(Note) And CustomCondition K01" = some ["VALUE_ERROR Claim/Note"] ∧
    fired claim "Note" "FieldFilled(Note) And CustomCondition K02" = some [] := by
  native_decide

/-- The capture's `doc-keep`, whose second row has no `Name`, and the review batch's `doc-r1` and
`doc-r4`, without their undeclared parallel groups. -/
private def keep : Lean.Json :=
  Lean.Json.mkObj [("Claim", Lean.Json.mkObj [("Note", .str "n"),
    ("Items", .arr #[item "a" "1", Lean.Json.mkObj [("Qty", .str "2")], item "c" "3"])])]
private def r1 : Lean.Json :=
  Lean.Json.mkObj [("Claim", Lean.Json.mkObj [("Note", .str "n"),
    ("Items", .arr #[item "a" "1", item "b" "1", item "c" "3"])])]
private def r4 : Lean.Json :=
  Lean.Json.mkObj [("Claim", Lean.Json.mkObj [("Note", .str "n"), ("Stage", .str "s"), ("Amount", .str "abc")])]

private def e01 := "FieldFilled(Name) Or (FieldFilled(Qty) And CustomCondition Ghost)"
private def rows23 : ValidationRelevanceScope :=
  .partialSet [{ path := ["Claim", "Items", "Qty"], indices := [.concrete 1, .concrete 2, .concrete 1] },
    { path := ["Claim", "Items", "Qty"], indices := [.concrete 1, .concrete 3, .concrete 1] }]

/-- A repeatable rule's handler reports once, at its iterator's first error address, whichever row
reached the name, and stops. A partial call's iterator starts where the relevant set's compressed
error-field selector does: at its one concrete row, or at row 1 when the rows differ. Rules
`M01`–`M03` and `E01` of `request-missing` rows `m-claim` and `m-row3`, whose first row's `Qty` of `1`
does not reach the name, and of `request-review` row `r1-rows23`. A relevant set without `Name` leaves
it unknown, so `E01` reaches the name in `m-row3` and `r1-rows23`. -/
example :
    fired items "Name" "FieldFilled(Name) And CustomCondition Ghost" = some ["VALUE_ERROR Claim/Items/Name!"] ∧
    fired items "Qty" "[Qty] > 1 And CustomCondition Ghost" = some ["VALUE_ERROR Claim/Items/Qty!"] ∧
    fired claim "Items/Qty" "[Items/Qty] > 1 And CustomCondition Ghost" = some ["VALUE_ERROR Claim/Items/Qty!"] ∧
    fired items "Name" "FieldFilled(Name) And CustomCondition Ghost" (relevant [] [.all]) =
      some ["VALUE_ERROR Claim/Items/Name!"] ∧
    fired items "Qty" "[Qty] > 1 And CustomCondition Ghost" (relevant [] [.all]) =
      some ["VALUE_ERROR Claim/Items/Qty!"] ∧
    fired claim "Items/Qty" "[Items/Qty] > 1 And CustomCondition Ghost" (relevant [] [.all]) =
      some ["VALUE_ERROR Claim/Items/Qty!"] ∧
    fired items "Qty" e01 (relevant [] [.all]) =
      some ["VALUE_ERROR Claim/Items/Qty", "VALUE_ERROR Claim/Items[2]/Qty", "VALUE_ERROR Claim/Items[3]/Qty"] ∧
    fired items "Qty" "[Qty] > 1 And CustomCondition Ghost"
        (relevant ["Items", "Qty"] [.concrete 1, .concrete 3, .concrete 1]) =
      some ["VALUE_ERROR Claim/Items[3]/Qty!"] ∧
    fired claim "Items/Qty" "[Items/Qty] > 1 And CustomCondition Ghost"
        (relevant ["Items", "Qty"] [.concrete 1, .concrete 3, .concrete 1]) =
      some ["VALUE_ERROR Claim/Items[3]/Qty!"] ∧
    fired items "Qty" e01 (relevant ["Items", "Qty"] [.concrete 1, .concrete 3, .concrete 1]) =
      some ["VALUE_ERROR Claim/Items[3]/Qty!"] ∧
    fired items "Name" "FieldFilled(Name) And CustomCondition Ghost"
        (relevant ["Items", "Qty"] [.concrete 1, .concrete 3, .concrete 1]) = some [] ∧
    fired items "Qty" e01 rows23 (json := r1) = some ["VALUE_ERROR Claim/Items/Qty!"] ∧
    fired items "Qty" "[Qty] > 1 And CustomCondition Ghost" rows23 (json := r1) =
      some ["VALUE_ERROR Claim/Items/Qty!"] ∧
    fired claim "Items/Qty" "[Items/Qty] > 1 And CustomCondition Ghost" rows23 (json := r1) =
      some ["VALUE_ERROR Claim/Items/Qty!"] ∧
    fired items "Name" "FieldFilled(Name) And CustomCondition Ghost" rows23 (json := r1) = some [] := by
  native_decide

/-- Messages fired before the failing row stand beside the handler's report at the same first
address, and later rows are not evaluated. Rule `E01` in `m-keep`, full and partial. -/
example :
    fired items "Qty" e01 (json := keep) = some ["VALUE_ERROR Claim/Items/Qty", "VALUE_ERROR Claim/Items/Qty!"] ∧
    fired items "Qty" e01 (relevant [] [.all]) (json := keep) =
      some ["VALUE_ERROR Claim/Items/Qty", "VALUE_ERROR Claim/Items/Qty!"] := by
  native_decide

/-- A tree whose classification pass runs reaches the name behind a disjunct already true. Rule `M06`
of `request-review`, in `r1-rows23` with `Stage` absent and `r4-formal` with it filled. -/
example :
    fired claim "Stage" "FieldNotFilled(Stage) Or CustomCondition Ghost" (json := r1) =
      some ["VALUE_ERROR Claim/Stage!"] ∧
    fired claim "Stage" "FieldNotFilled(Stage) Or CustomCondition Ghost" (json := r4) =
      some ["VALUE_ERROR Claim/Stage!"] := by
  native_decide

/-- Full validation passes no relevance, the formally incorrect cells of the whole document and the
iterated row's error entity: a callback expecting another row's pointer silences that row. Rules
`R01`–`R03` in `f-full` and `f-bad`; `R03` iterates from the root group through its error field.
Rule `M05` in `r4-formal` passes the invalid `Amount`. -/
example :
    fired items "Qty" "[Qty] > 1 And CustomCondition K12" (pointers := [("K12", pointer 2)]) =
      some ["VALUE_ERROR Claim/Items[2]/Qty"] ∧
    fired items "Qty" "[Qty] > 1 And CustomCondition K12" (pointers := [("K12", pointer 3)]) =
      some ["VALUE_ERROR Claim/Items[3]/Qty"] ∧
    fired items "Qty" "[Qty] > 1 And CustomCondition K12" (bad := true) =
      some ["VALUE_ERROR Claim/Items[2]/Qty"] ∧
    fired claim "Items/Qty" "[Items/Qty] > 1 And CustomCondition K13" (bad := true) (pointers := [("K13", pointer 2)]) =
      some ["VALUE_ERROR Claim/Items[2]/Qty"] ∧
    fired items "Name" "FieldFilled(Name) And CustomCondition K11" (bad := true) =
      some ["VALUE_ERROR Claim/Items/Name", "VALUE_ERROR Claim/Items[2]/Name"] ∧
    fired claim "Note" "FieldFilled(Note) And CustomCondition K01" (json := r4) (formal := [{ field := 2, path := [] }]) =
      some ["VALUE_ERROR Claim/Note"] := by
  native_decide

/-- Partial validation passes the caller's relevant set unchanged, and only the formally incorrect
cells it covers, and reaches only rules whose error field it covers. Rows `p-note`, `p-none`,
`p-row2`, `p-claim-bad`, `m-claim` and `r4-formal`. -/
example :
    fired claim "Note" "FieldFilled(Note) And CustomCondition K01" (relevant ["Note"] [.all, .all]) =
      some ["VALUE_ERROR Claim/Note"] ∧
    fired claim "Note" "FieldFilled(Note) And CustomCondition K02" (relevant ["Note"] [.all, .all]) = some [] ∧
    fired claim "Note" "FieldFilled(Note) And CustomCondition K03" (relevant ["Note"] [.all, .all]) =
      some ["VALUE_ERROR Claim/Note"] ∧
    fired claim "Note" "FieldFilled(Note) And CustomCondition Ghost" (relevant ["Note"] [.all, .all]) =
      some ["VALUE_ERROR Claim/Note!"] ∧
    fired claim "Note" "FieldFilled(Note) And Sum(Items*/Qty) > 1 And CustomCondition K14"
      (relevant ["Note"] [.all, .all]) = some [] ∧
    fired claim "Stage" "FieldFilled(Stage) And CustomCondition Ghost" (relevant ["Note"] [.all, .all]) = some [] ∧
    fired claim "Amount" "FieldFilled(Amount) And CustomCondition K04" (relevant ["Note"] [.all, .all]) = some [] ∧
    fired claim "Note" "FieldFilled(Note) And CustomCondition K01" (.partialSet []) = some [] ∧
    fired items "Qty" "[Qty] > 1 And CustomCondition K12"
        (relevant ["Items", "Qty"] [.concrete 1, .concrete 2, .concrete 1]) (pointers := [("K12", pointer 2)]) =
      some ["VALUE_ERROR Claim/Items[2]/Qty"] ∧
    fired claim "Items/Qty" "[Items/Qty] > 1 And CustomCondition K13"
        (relevant ["Items", "Qty"] [.concrete 1, .concrete 2, .concrete 1]) (pointers := [("K13", pointer 2)]) =
      some ["VALUE_ERROR Claim/Items[2]/Qty"] ∧
    fired items "Name" "FieldFilled(Name) And CustomCondition K11"
        (relevant ["Items", "Qty"] [.concrete 1, .concrete 2, .concrete 1]) = some [] ∧
    fired items "Qty" "[Qty] > 1 And CustomCondition K12" (relevant [] [.all]) (bad := true) =
      some ["VALUE_ERROR Claim/Items[2]/Qty"] ∧
    fired claim "Items/Qty" "[Items/Qty] > 1 And CustomCondition K13" (relevant [] [.all]) (bad := true) =
      some ["VALUE_ERROR Claim/Items[2]/Qty"] ∧
    fired items "Name" "FieldFilled(Name) And CustomCondition K11" (relevant [] [.all]) (bad := true) =
      some ["VALUE_ERROR Claim/Items/Name", "VALUE_ERROR Claim/Items[2]/Name"] ∧
    fired claim "Amount" "FieldFilled(Amount) And CustomCondition K04" (relevant [] [.all]) (bad := true) = some [] ∧
    fired claim "Amount" "CustomCondition K05 And FieldFilled(Amount)" (relevant [] [.all]) (bad := true) = some [] ∧
    fired claim "Amount" "FieldFilled(Amount) Or CustomCondition K06" (relevant [] [.all]) (bad := true) =
      some ["VALUE_ERROR Claim/Amount"] ∧
    fired claim "Stage" "FieldNotFilled(Stage) And CustomCondition K07" (relevant [] [.all]) (bad := true) =
      some ["OMISSION_ERROR Claim/Stage"] ∧
    fired claim "Stage" "CustomCondition K08 And FieldNotFilled(Stage)" (relevant [] [.all]) (bad := true) =
      some ["OMISSION_ERROR Claim/Stage"] ∧
    fired claim "Note" "FieldFilled(Note) And CustomCondition K01" (relevant [] [.all]) =
      some ["VALUE_ERROR Claim/Note"] ∧
    fired claim "Note" "FieldFilled(Note) And CustomCondition K01" (relevant ["Note"] [.all, .all]) (json := r4)
      (formal := []) = some ["VALUE_ERROR Claim/Note"] := by
  native_decide

private def classifies (group : GroupPath) (errorField condition : String) : Option Bool := do
  let dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let .ok (.ordinary rule) := checkValidationRule dm .english {
      name := "Rule", group, errorCode := "R", errorEntityRelPath := "../" ++ errorField,
      condition, severity := "ERROR" } { now := { epochMillis := 0 } } | none
  pure (rule.condition.core.anyLeaf ValidationConditionLeaf.requiresClassificationPass)

/-- A holding rule calls each reached callback a second time exactly when its tree needs the
classification pass (`ConditionTree.evalObservedM`). The Kernel called `K07`, `K08`, `K12`, `K13` and
`K14` twice and `K01`, `K04`, `K05`, `K06` and `K11` once, and every callback of a rule that did not
hold once. -/
example :
    classifies claim "Stage" "FieldNotFilled(Stage) And CustomCondition K07" = some true ∧
    classifies claim "Stage" "CustomCondition K08 And FieldNotFilled(Stage)" = some true ∧
    classifies items "Qty" "[Qty] > 1 And CustomCondition K12" = some true ∧
    classifies claim "Items/Qty" "[Items/Qty] > 1 And CustomCondition K13" = some true ∧
    classifies claim "Note" "FieldFilled(Note) And Sum(Items*/Qty) > 1 And CustomCondition K14" = some true ∧
    classifies claim "Note" "FieldFilled(Note) And CustomCondition K01" = some false ∧
    classifies claim "Amount" "FieldFilled(Amount) And CustomCondition K04" = some false ∧
    classifies claim "Amount" "CustomCondition K05 And FieldFilled(Amount)" = some false ∧
    classifies claim "Amount" "FieldFilled(Amount) Or CustomCondition K06" = some false ∧
    classifies items "Name" "FieldFilled(Name) And CustomCondition K11" = some false := by
  native_decide

/-- A negative beside a callback in an `Or` classifies on either side, so a holding rule reaches the
callback once more in that pass: the Kernel called `EnablingOr` once where its truth pass stopped at
the negative and twice where that pass reached a holding callback, and `LeftOr` twice wherever the
rule held
([KF604](../../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf604)). -/
example :
    classifies claim "Note" "FieldNotFilled(Note) Or CustomCondition EnablingOr" = some true ∧
    classifies claim "Note" "CustomCondition LeftOr Or FieldNotFilled(Note)" = some true := by
  native_decide

/-- The undeclared members of `doc-extra`, a string and an object beside the declared fields and a
string inside a row, are dropped: the document reads exactly as `doc-full`. -/
example :
    (readDocument { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
      (Lean.Json.mkObj [("Claim", Lean.Json.mkObj [("Note", .str "n"), ("Amount", .str "7"), ("Stage", .str "s"),
        ("Items", .arr #[Lean.Json.mkObj [("Name", .str "a"), ("Qty", .str "1"), ("Extra", .str "e")],
          item "b" "2", item "c" "3"]),
        ("Ghost", .str "g"), ("Phantom", Lean.Json.mkObj [("F", .str "1")])])])).toOption.map
      (fun read => (read.refusals.isEmpty, read.data)) =
    (readDocument { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
      (document false)).toOption.map (fun read => (read.refusals.isEmpty, read.data)) := by
  native_decide

end A12Kernel.Dm.CustomConditionCaptureLocks
