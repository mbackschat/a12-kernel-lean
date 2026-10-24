import A12Kernel.Reference.Dm.ComputationCheck
import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.ParallelValidation
import A12Kernel.Reference.Dm.Validate

/-! # Rules reporting on a group against the retained group-target capture

Each row is one rule of the
[group-target capture](../../../docs/sources/model-structure-and-declaration-probes.md#src-group-target-nested-join),
checked through the DM reader on a model with the capture's shape; the expected class is the
Kernel's `rule add --dry-run` verdict, or its admission of a rule `model check` confirmed. The rows
separate a group's own or a containing group's presence, which references the target, from a field
inside it, which does not, and the group's own level, which no reference needs to bind, from the
levels above it. The population replay compares the same rules' firings and references.
-/

namespace A12Kernel.Dm.GroupTargetLocks

open A12Kernel

private def text (id : Nat) (groupPath : GroupPath) (name : String) (scope : List Nat) : FlatFieldDecl :=
  { id, name, groupPath, repeatableScope := scope, policy := { kind := .string } }

private def number (id : Nat) (groupPath : GroupPath) (name : String) (scope : List Nat) : FlatFieldDecl :=
  { text id groupPath name scope with policy := { kind := .number { scale := 0, signed := true } } }

private def O : GroupPath := ["Order"]
private def L : GroupPath := ["Order", "Lines"]
private def W : GroupPath := ["Order", "Wraps"]

/-- The rows' part of the capture's [order model](../../../evidence/kernel-30.8.1/captures/group-target-nested-join-2026-10-23/Order23u_DM.json):
`Lines` (50, keyed) holds `Parts` (5) and keyed `Slots` (2) with a fixed `Tagged`; `Picks` (10, keyed
by `LineNo`), `Gifts` (2, keyed) with a fixed `Card`, and `Wraps` (2, unkeyed) with fixed `Ribbon` and
`Tag` and keyed `Bows` (3); and the roots `Other`, `Reps` (3, keyed) and `Bins` (2, unkeyed) and the
`Mark` of `Slots` of the
[blank-root capture](../../../evidence/kernel-30.8.1/captures/blank-root-dispatch-2026-10-23/K0607_DM.json). -/
private def model : FlatModel :=
  { fields := [text 1 O "Email" [],
      text 10 L "LineNo" [10], text 11 L "Sku" [10],
      text 20 (L ++ ["Parts"]) "PartNo" [10, 11], number 21 (L ++ ["Parts"]) "Count" [10, 11],
      text 30 (O ++ ["Picks"]) "LineNo" [13], text 31 (O ++ ["Picks"]) "Ref" [13],
      text 40 (O ++ ["Gifts"]) "GiftNo" [14], text 41 (O ++ ["Gifts"]) "Note" [14],
      text 42 (O ++ ["Gifts", "Card"]) "Text" [14],
      text 50 W "Style" [15], text 51 (W ++ ["Ribbon"]) "Color" [15], text 52 (W ++ ["Tag"]) "Label" [15],
      text 53 (W ++ ["Bows"]) "BowNo" [15, 16], text 54 (W ++ ["Bows"]) "Shade" [15, 16],
      text 60 (L ++ ["Slots"]) "SlotNo" [10, 12], text 61 (L ++ ["Slots", "Tagged"]) "Flag" [10, 12],
      text 62 (L ++ ["Slots"]) "Mark" [10, 12],
      number 70 ["Other"] "O" [], text 80 ["Reps"] "RepNo" [17], text 81 ["Reps"] "Mark" [17],
      text 90 ["Bins"] "Item" [18]]
    repeatableGroups := [
      { level := 10, path := L, repeatability := some 50, indexField := some 10 },
      { level := 11, path := L ++ ["Parts"], repeatability := some 5 },
      { level := 12, path := L ++ ["Slots"], repeatability := some 2, indexField := some 60 },
      { level := 13, path := O ++ ["Picks"], repeatability := some 10, indexField := some 30 },
      { level := 14, path := O ++ ["Gifts"], repeatability := some 2, indexField := some 40 },
      { level := 15, path := W, repeatability := some 2 },
      { level := 16, path := W ++ ["Bows"], repeatability := some 3, indexField := some 53 },
      { level := 17, path := ["Reps"], repeatability := some 3, indexField := some 80 },
      { level := 18, path := ["Bins"], repeatability := some 2 }] }

example : model.validate.isOk = true := by native_decide

private def dm : DmModel :=
  { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }

/-- The class this reader answers, `admitted`, or the refusal's detail when it carries no class, so
a refusal without a class fails a row rather than passing as any expected class. -/
private def verdict (errorEntity condition : String) (group : GroupPath := O) : String :=
  let rule : DmRule :=
    { group, name := "GroupProbe", errorCode := "P", errorEntityRelPath := "../" ++ errorEntity,
      condition, severity := "ERROR" }
  match checkValidationRule dm .english rule with
  | .ok _ => "admitted"
  | .error refusal => refusal.kernelClass?.getD refusal.detail

private def UNREFERENCED := "MVK_ERROR_FIELD_NOT_REFERENCED"

/-- `(capture row, error entity, condition, Kernel class)`. Row `t8` reports on a group beside the
joined `Picks`. -/
private def rows : List (String × String × String × String) := [
  ("t0", "Lines/Parts", "GroupFilled(Lines/Parts)", "admitted"),
  ("t1", "Lines/Parts", "FieldFilled(Lines/Parts/Count) And GroupFilled(Lines/Parts)", "admitted"),
  ("t2", "Lines/Parts", "FieldNotFilled(Lines/Parts/PartNo) And GroupFilled(Lines/Parts)", "admitted"),
  ("t3", "Lines/Parts", "FieldFilled(Lines/Parts/Count)", UNREFERENCED),
  ("t4", "Lines/Parts", "GroupFilled(Lines)", "admitted"),
  ("t5", "Lines/Parts", "FieldFilled(Lines/Sku)", UNREFERENCED),
  -- Only `Lines` is checked: the reference to the containing group need not bind `Parts`.
  ("t6", "Lines/Parts", "GroupFilled(Lines) And FieldFilled(Lines/Parts/Count)", "admitted"),
  ("t7", "Lines/Parts", "Sum(Lines/Parts*/Count) > 0 And GroupFilled(Lines/Parts)", "admitted"),
  ("t8", "Lines/Parts", "GroupFilled(Lines/Parts) And FieldFilled(Picks/Ref)", "admitted"),
  ("E2", "Wraps/Ribbon", "GroupFilled(Wraps/Ribbon)", "admitted"),
  ("E3", "Gifts/Card", "GroupNotFilled(Gifts/Card)", "admitted"),
  ("E4", "Lines/Parts", "FieldFilled(Lines/Sku) And GroupFilled(Lines/Parts)", "admitted"),
  ("v3", "Wraps", "GroupFilled(Wraps) And GroupFilled(Wraps/Ribbon)", "admitted"),
  ("v4", "Wraps", "GroupFilled(Wraps) And FieldFilled(Wraps/Style)", "admitted"),
  ("v5", "Gifts", "GroupNotFilled(Gifts)", "admitted")]

/-- The rows this reader answers otherwise, each named by its capture row. -/
private def mismatches : List (String × String × String) :=
  rows.filterMap fun (id, entity, condition, expected) =>
    let actual := verdict entity condition
    if actual == expected then none else some (id, expected, actual)

example : mismatches = [] := by native_decide

/-- `(row, error entity, condition, Kernel class)` of the
[blank-root batch](../../../docs/sources/model-structure-and-declaration-probes.md#src-blank-root-dispatch-k06):
beside the joined `Picks` a group target draws its field twin's class, a group read reaching the
join as a field read does, and a read ahead of the target's own presence answers first. -/
private def twinRows : List (String × String × String × String) := [
  ("p1", "Lines/Slots/Tagged", "GroupFilled(Lines/Slots/Tagged) And FieldFilled(Picks/Ref)", "MVK_MULTIPLE_INDEX_FIELDS"),
  ("p2", "Lines/Slots/Tagged/Flag", "FieldFilled(Lines/Slots/Tagged/Flag) And FieldFilled(Picks/Ref)", "MVK_MULTIPLE_INDEX_FIELDS"),
  ("p3", "Wraps/Ribbon", "GroupFilled(Wraps/Ribbon) And FieldFilled(Picks/Ref)", "MVK_ERROR_FIELD_NO_INDEX"),
  ("p4", "Wraps/Ribbon/Color", "FieldFilled(Wraps/Ribbon/Color) And FieldFilled(Picks/Ref)", "MVK_ERROR_FIELD_NO_INDEX"),
  ("p5", "Lines/Parts", "GroupFilled(Lines/Parts) And FieldFilled(Picks/Ref) And FieldFilled(Wraps/Style)", "MVK_NO_WILDCARD"),
  ("p6", "Lines/Parts/Count", "FieldFilled(Lines/Parts/Count) And FieldFilled(Picks/Ref) And FieldFilled(Wraps/Style)", "MVK_NO_WILDCARD"),
  ("p7", "Lines/Parts", "GroupFilled(Lines/Parts) And FieldFilled(Picks/Ref) And RepetitionNotUnique(Lines/Sku)",
    "MVK_PARALLEL_ITERATION_NOT_ALLOWED"),
  ("p8", "Lines/Parts/Count", "FieldFilled(Lines/Parts/Count) And FieldFilled(Picks/Ref) And RepetitionNotUnique(Lines/Sku)",
    "MVK_PARALLEL_ITERATION_NOT_ALLOWED"),
  ("p9", "Lines/Parts/Count", "FieldFilled(Lines/Sku) And FieldFilled(Picks/Ref)", UNREFERENCED),
  ("p10", "Lines/Parts/Count", "[Lines/Parts/Count] > 1 And FieldFilled(Picks/Ref)", "admitted"),
  -- The group's own level is unindexed, so a keyed group without a keyed ancestor has none.
  ("q1", "Wraps/Bows", "GroupFilled(Wraps/Bows) And FieldFilled(Picks/Ref)", "MVK_ERROR_FIELD_NO_INDEX"),
  ("q1f", "Wraps/Bows/Shade", "FieldFilled(Wraps/Bows/Shade) And FieldFilled(Picks/Ref)", "MVK_ERROR_FIELD_INVALID_INDEX"),
  ("q2", "Wraps", "GroupFilled(Wraps) And FieldFilled(Picks/Ref)", "MVK_ERROR_FIELD_NO_INDEX"),
  ("q2f", "Wraps/Style", "FieldFilled(Wraps/Style) And FieldFilled(Picks/Ref)", "MVK_ERROR_FIELD_NO_INDEX"),
  ("q3", "Lines", "GroupFilled(Lines) And FieldFilled(Picks/Ref)", "MVK_ERROR_FIELD_NO_INDEX"),
  ("m1", "Wraps", "GroupFilled(Wraps) And GroupFilled(Picks)", "MVK_ERROR_FIELD_NO_INDEX"),
  ("m1f", "Wraps/Style", "FieldFilled(Wraps/Style) And GroupFilled(Picks)", "MVK_ERROR_FIELD_NO_INDEX"),
  ("m2", "Lines/Slots/Tagged", "GroupFilled(Lines/Slots/Tagged) And GroupFilled(Picks)", "MVK_MULTIPLE_INDEX_FIELDS"),
  ("m2f", "Lines/Slots/Tagged/Flag", "FieldFilled(Lines/Slots/Tagged/Flag) And GroupFilled(Picks)",
    "MVK_MULTIPLE_INDEX_FIELDS"),
  ("m3", "Lines/Slots/Tagged",
    "FieldFilled(Lines/Parts/Count) And GroupFilled(Lines/Slots/Tagged) And FieldFilled(Picks/Ref)", "MVK_NO_WILDCARD"),
  ("m3f", "Lines/Slots/Tagged/Flag",
    "FieldFilled(Lines/Parts/Count) And GroupFilled(Lines/Slots/Tagged) And FieldFilled(Picks/Ref)", "MVK_NO_WILDCARD"),
  ("m4", "Lines/Slots/Tagged",
    "FieldFilled(Wraps/Style) And GroupFilled(Lines/Slots/Tagged) And FieldFilled(Picks/Ref)", "MVK_NO_WILDCARD"),
  ("m4f", "Lines/Slots/Tagged/Flag",
    "FieldFilled(Wraps/Style) And GroupFilled(Lines/Slots/Tagged) And FieldFilled(Picks/Ref)", "MVK_NO_WILDCARD"),
  ("m5", "Lines/Slots/Tagged",
    "GroupFilled(Lines/Slots/Tagged) And FieldFilled(Picks/Ref) And FieldFilled(Lines/Parts/Count)",
    "MVK_MULTIPLE_INDEX_FIELDS"),
  ("m5f", "Lines/Slots/Tagged/Flag",
    "GroupFilled(Lines/Slots/Tagged) And FieldFilled(Picks/Ref) And FieldFilled(Lines/Parts/Count)",
    "MVK_MULTIPLE_INDEX_FIELDS")]

example : (twinRows.filter fun (_, entity, condition, expected) => verdict entity condition != expected).map (·.1) = [] := by
  native_decide

/-- This reader's account of a group target beside a join where no capture measures the composition:
the ordinary carrier's gates, so a field inside the group does not reference it (`t3`) and a negative
presence of the group leaves its own level unguarded (`g03`), while a field inside it is read at its
first row (`t2`). A field-fill list across the join is admitted (`q5`), and so is a custom condition,
as `model check` admits `g4` of the
[joined group-target checkpoint](../../../docs/sources/model-structure-and-declaration-probes.md#src-k22-joined-group-target-leaves). -/
example :
    verdict "Lines/Parts" "FieldFilled(Lines/Parts/Count) And FieldFilled(Picks/Ref)" = UNREFERENCED ∧
    verdict "Lines/Parts" "GroupNotFilled(Lines/Parts) And FieldFilled(Picks/Ref)" =
      "MVK_NEG_CONDITION_IN_ITERATION" ∧
    verdict "Lines/Parts" "GroupFilled(Lines/Parts) And FieldNotFilled(Lines/Parts/PartNo) And FieldFilled(Picks/Ref)" =
      "admitted" ∧
    verdict "Lines/Parts" "GroupFilled(Lines) And FieldFilled(Picks/Ref)" = "admitted" ∧
    verdict "Lines/Parts" "GroupFilled(Lines/Parts) And AtLeastOneFieldFilled(Lines/Sku, Picks/Ref)" = "admitted" ∧
    verdict "Lines/Parts" "GroupFilled(Lines/Parts) And CustomCondition X And FieldFilled(Picks/Ref)" = "admitted" := by
  native_decide

open Lean in
/-- The pointers a rule reporting on `Lines/Parts` fires at over `Lines` rows of `(LineNo, parts)`,
each part a `PartNo`, empty for a part holding no field, beside `Picks` rows of `(LineNo, Ref)`. -/
private def fired (condition : String) (lines : List (String × List String)) (picks : List (String × String)) :
    Option (List String) := do
  let world : World := { now := { epochMillis := 0 } }
  let part := fun (partNo : String) =>
    if partNo.isEmpty then Json.mkObj [("Count", Json.str "1")] else Json.mkObj [("PartNo", Json.str partNo)]
  let lineRows := lines.map fun (no, parts) =>
    Json.mkObj [("LineNo", Json.str no), ("Parts", Json.arr (parts.map part).toArray)]
  let pickRows := picks.map fun (no, ref) => Json.mkObj [("LineNo", Json.str no), ("Ref", Json.str ref)]
  let input ← (readDocument dm (Json.mkObj [("Order", Json.mkObj [
    ("Lines", Json.arr lineRows.toArray), ("Picks", Json.arr pickRows.toArray)])])).toOption
  if !input.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  let checked ← (checkValidationRule dm .english
    { group := O, name := "GroupProbe", errorCode := "P", errorEntityRelPath := "../Lines/Parts", condition,
      severity := "ERROR" }).toOption
  pure ((← (runValidationRule world document checked).toOption).map fun message => (observe model message).pointer)

/-- Internal witnesses, `external evidence pending` beyond `t8`'s capture: the group's own presence
reads every part of the joined line, so the first line, whose second part alone holds `PartNo`, fires
there, while a field inside the group reads only the first part and so does not; the third line's
missing pick keeps it silent. -/
example :
    fired "GroupFilled(Lines/Parts) And FieldFilled(Picks/Ref)"
      [("1", ["", "x"]), ("2", ["y"]), ("3", ["z"])] [("1", "r"), ("2", "q")] =
      some ["Order/Lines/Parts", "Order/Lines[2]/Parts"] ∧
    fired "GroupFilled(Lines/Parts) And FieldFilled(Lines/Parts/PartNo) And FieldFilled(Picks/Ref)"
      [("1", ["", "x"]), ("2", ["y"]), ("3", ["z"])] [("1", "r"), ("2", "q")] =
      some ["Order/Lines[2]/Parts"] := by native_decide

open Lean in
/-- The pointers a rule reporting on `entity` fires at under a partial call with only `/Order[1]`
relevant, over line `A` with parts `[{}, {Count}]`, line `B` with a part holding `Count` and their
picks, or `none` when the rule or document is refused. -/
private def firedPartially (entity condition : String) : Option (List String) := do
  let world : World := { now := { epochMillis := 0 } }
  let count := fun (value : String) => Json.mkObj [("Count", Json.str value)]
  let document := Json.mkObj [("Order", Json.mkObj [
    ("Lines", Json.arr #[Json.mkObj [("LineNo", Json.str "A"), ("Parts", Json.arr #[Json.mkObj [], count "5"])],
      Json.mkObj [("LineNo", Json.str "B"), ("Parts", Json.arr #[count "6"])]]),
    ("Picks", Json.arr #[Json.mkObj [("LineNo", Json.str "A"), ("Ref", Json.str "r")],
      Json.mkObj [("LineNo", Json.str "B"), ("Ref", Json.str "r")]])])]
  let input ← (readDocument dm document).toOption
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let relevant : List RelevantEntityPattern := [{ path := O, indices := [.concrete 1] }]
  let messages ← match ← (checkValidationRule dm .english
      { group := O, name := "PartialProbe", errorCode := "P", errorEntityRelPath := "../" ++ entity, condition,
        severity := "ERROR" }).toOption with
    | .parallel rule => (runPartialParallelRule checked rule relevant (world := some world)).toOption
    | .ordinary rule => match rule.ordinaryIterationPlan with
      | .rows _ => (rule.evalOrdinaryRepeatablePartial checked (.partialSet relevant) (some world)).toOption.map fun
          | .skipped => []
          | .evaluated rows => rows.filterMap fun
              | (_, .evaluated outcome) => outcome.message?
              | (_, .skipped) => none
      | .once _ => (rule.evalOrdinaryOncePartial checked (.partialSet relevant) (some world)).toOption.map fun
          | .skipped => []
          | .evaluated _ outcome => outcome.message?.toList
      | .scalar => (rule.evalAddressedPartial checked (.partialSet relevant) (some world)).toOption.map fun
          | .skipped => []
          | .evaluated outcome => outcome.message?.toList
  pure (messages.map fun message => (observe model message).pointer)

/-- A partial call reports no rule whose error entity is a group, ordinary or beside a join, while
each rule's field twin reports in the same call
([KF603](../../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf603), peer-reported; the
[inbound record](../../../docs/sources/inbound-handbacks.md#src-inbound-2026-10-23)). -/
example :
    firedPartially "Lines/Parts" "GroupFilled(Lines/Parts)" = some [] ∧
    ((firedPartially "Lines/Parts/Count" "FieldFilled(Lines/Parts/Count)").getD []).length > 0 ∧
    firedPartially "Lines/Parts" "GroupFilled(Lines/Parts) And FieldFilled(Picks/Ref)" = some [] ∧
    ((firedPartially "Lines/LineNo" "FieldFilled(Lines/LineNo) And FieldFilled(Picks/Ref)").getD []).length > 0 := by
  native_decide

/-- `(row, rule group, error entity, condition, Kernel verdict)` of the blank-root batch's static rows:
a condition able to fire on empty over a nested keyed level, a repeatable root or an unkeyed one
draws the negative-iteration class or its own, while a second root's read beside a positive guard is
admitted. These rows carry the restriction of the blank-root dispatch to a nonrepeatable root. -/
private def rootRows : List (String × GroupPath × String × String × String) := [
  ("d4", O, "Lines/Slots/Mark", "FieldNotFilled(Lines/Slots/Mark)", "MVK_NEG_CONDITION_IN_ITERATION"),
  ("d6", ["Reps"], "Mark", "FieldNotFilled(Mark)", "MVK_NEG_CONDITION_IN_ITERATION"),
  ("d7", ["Bins"], "Item", "FieldNotFilled(Item)", "MVK_NEG_CONDITION_IN_ITERATION"),
  ("d9", ["Reps"], "Mark", "NumberOfFilledFields(Mark, RepNo) < 1", "MVK_NEG_CONDITION_IN_ITERATION"),
  ("d10", O, "Lines/Slots/Mark", "NumberOfFilledFields(Lines/Slots/Mark, Lines/Slots/SlotNo) < 1",
    "MVK_NEG_CONDITION_IN_ITERATION"),
  ("d11", ["Bins"], "Item", "NumberOfFilledFields(Item) < 1", "MVK_PARAMSIZE_INVALIDN"),
  ("d13", ["Reps"], "Mark", "[/Other/O] < 5 And FieldFilled(RepNo) And FieldNotFilled(Mark)", "admitted")]

example : (rootRows.filter fun (_, group, entity, condition, expected) =>
    verdict entity condition group != expected).map (·.1) = [] := by
  native_decide

open Lean in
/-- The pointers a rule in `/Order` reporting on `entity` fires at over `document`. -/
private def firedOn (entity condition : String) (document : Json) (dm : DmModel := dm) : Option (List String) := do
  let world : World := { now := { epochMillis := 0 } }
  let input ← (readDocument dm document).toOption
  if !input.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler dm.flat).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let rule ← (checkValidationRule dm .english
    { group := O, name := "BlankProbe", errorCode := "P", errorEntityRelPath := "../" ++ entity, condition,
      severity := "ERROR" }).toOption
  pure ((← (runValidationRule world checked rule).toOption).map fun message => (observe dm.flat message).pointer)

open Lean in
/- The blank-root batch's runtime rows: a rule evaluated without admitted content, by a negative, a
   small-side count, an `Or` beside a negative or a second root's read, fires at both declared rows
   of the keyed `Gifts` on a blank and an empty root, and on one holding only `Other`, while a
   condition gated on `Email` waits for it and the second-root read waits for `O` below five. A
   second root's read beside no negative, `r1`, fires under a blank root once `O` exceeds five. -/
example :
    let both := some ["Order/Gifts/Note", "Order/Gifts[2]/Note"]
    let blank := [Json.mkObj [], Json.mkObj [("Order", Json.mkObj [])],
      Json.mkObj [("Other", Json.mkObj [("O", "1")])]]
    blank.all (fun document =>
      ["FieldNotFilled(Gifts/Note)", "NumberOfFilledFields(Gifts/Note, Gifts/GiftNo) < 1",
        "FieldNotFilled(Gifts/Note) Or FieldFilled(Gifts/GiftNo)", "[/Other/O] < 5 And FieldNotFilled(Gifts/Note)"].all
        (firedOn "Gifts/Note" · document == both) &&
      firedOn "Gifts/Note" "[Email] == \"e\" And FieldNotFilled(Gifts/Note)" document == some []) ∧
    firedOn "Gifts/Note" "[/Other/O] < 5 And FieldNotFilled(Gifts/Note)" (Json.mkObj [("Other", Json.mkObj [("O", "9")])]) =
      some [] ∧
    firedOn "Gifts/Note" "[Email] == \"e\" And FieldNotFilled(Gifts/Note)" (Json.mkObj [("Order", Json.mkObj [("Email", "e")])]) =
      both ∧
    [Json.mkObj [("Other", Json.mkObj [("O", "9")])], Json.mkObj [("Order", Json.mkObj []), ("Other", Json.mkObj [("O", "9")])]].all
      (firedOn "Gifts/Note" "[/Other/O] > 5 Or FieldFilled(Gifts/Note)" · == both) ∧
    firedOn "Gifts/Note" "[/Other/O] > 5 Or FieldFilled(Gifts/Note)" (Json.mkObj [("Other", Json.mkObj [("O", "1")])]) =
      some [] := by
  native_decide

open Lean in
/- The nested-capacity batch's rows: beside the `Lines`–`Picks` join, the error field's `Parts` rows
follow the ordinary capacity rule with the joined level counted once, so five declared parts are all
visited and six only where some line's parts or slots occupy them, and an unmatched line visits them
too ([checkpoint](../../../docs/sources/model-structure-and-declaration-probes.md#src-nested-join-capacity)). -/
example :
    let six : DmModel := { dm with flat := { model with repeatableGroups := model.repeatableGroups.map fun group =>
      if group.path == L ++ ["Parts"] then { group with repeatability := some 6 } else group } }
    let order := fun (lines picks : List Json) => Json.mkObj [("Order", Json.mkObj
      [("Lines", Json.arr lines.toArray), ("Picks", Json.arr picks.toArray)])]
    let pick := fun (key : String) => Json.mkObj [("LineNo", Json.str key), ("Ref", Json.str "r")]
    let line := fun (key : String) (members : List (String × Json)) => Json.mkObj ((("LineNo", Json.str key)) :: members)
    let rows := fun (n : Nat) => Json.arr ((List.replicate n (Json.mkObj [])).toArray)
    let parts := fun (owner : String) (n : Nat) => (List.range n).map fun i =>
      owner ++ "/Parts" ++ (if i == 0 then "" else s!"[{i + 1}]") ++ "/Count"
    let unmatched := fun (n : Nat) => (List.range n).map fun i => s!"/Order[1]/Lines[-5]/Parts[{i + 1}]/Count"
    let oneEach := order [line "A" [("Parts", Json.arr #[Json.mkObj [("Count", Json.str "1")]])], line "B" []]
      [pick "A", pick "B", pick "D"]
    let condition := "[Lines/Parts/Count] < 5 And FieldFilled(Picks/Ref)"
    firedOn "Lines/Parts/Count" condition oneEach =
      some (parts "Order/Lines" 5 ++ parts "Order/Lines[2]" 5 ++ unmatched 5) ∧
    firedOn "Lines/Parts/Count" condition oneEach six =
      some (parts "Order/Lines" 1 ++ parts "Order/Lines[2]" 1 ++ unmatched 1) ∧
    firedOn "Lines/Parts/Count" condition (order [line "A" [("Parts", rows 2)], line "B" []]
      [pick "A", pick "B", pick "D"]) six =
      some (parts "Order/Lines" 2 ++ parts "Order/Lines[2]" 2 ++ unmatched 2) ∧
    firedOn "Lines/Parts/Count" condition (order [line "A" [("Slots", Json.arr #[Json.mkObj [("SlotNo", Json.str "s1")],
      Json.mkObj [("SlotNo", Json.str "s2")]])]] [pick "A"]) six = some (parts "Order/Lines" 2) ∧
    firedOn "Lines/Parts/Count" condition (order [line "A" [], line "B" []]
      [Json.mkObj [("LineNo", Json.str "A")], pick "B"]) = some (parts "Order/Lines[2]" 5) := by
  native_decide

open Lean in
/-- Each message the unmatched `Picks` row fires names its own visited part in its references and
fill-to-fix, as `/Order[1]/Lines[-5]/Parts[2]/Count` beside `Order/Picks[2]/Ref`, not the wildcard
row: the channels the Kernel gives the `D` pick of `oneEach`
([checkpoint](../../../docs/sources/model-structure-and-declaration-probes.md#src-nested-join-capacity),
`capacity-five`), with this document's pick at row 2. -/
example :
    (do
      let world : World := { now := { epochMillis := 0 } }
      let pick := fun (key : String) => Json.mkObj [("LineNo", Json.str key), ("Ref", Json.str "r")]
      let document := Json.mkObj [("Order", Json.mkObj [("Lines", Json.arr #[Json.mkObj [("LineNo", Json.str "A")]]),
        ("Picks", Json.arr #[pick "A", pick "D"])])]
      let input ← (readDocument dm document).toOption
      let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler dm.flat).toOption
      let checked ← (checkDocument prepared "en_US" input.data).toOption
      let .parallel rule ← (checkValidationRule dm .english
        { group := O, name := "UnmatchedProbe", errorCode := "P", errorEntityRelPath := "../Lines/Parts/Count",
          condition := "[Lines/Parts/Count] < 5 And FieldFilled(Picks/Ref)", severity := "ERROR" }).toOption | none
      let rows ← (runParallelRuleReferences checked rule (some world)).toOption
      rows.filterMapM fun (message, references) => do
        let pointer := renderPointer dm.flat message.errorAddress
        if !pointer.startsWith "/Order[1]/Lines[-5]" then return none
        let references ← references.toOption
        let render := fun (channel : List MessagePointer) => (channel.map (renderFieldPointer dm.flat)).mergeSort
        pure (some (pointer, render references.referenced, render references.fillToFix))) =
      some ((List.range 5).map fun i =>
        let part := s!"/Order[1]/Lines[-5]/Parts[{i + 1}]/Count"
        (part, ["/Order[1]/Lines[-5]/LineNo", part, "Order/Picks[2]/LineNo", "Order/Picks[2]/Ref"].mergeSort,
          ["/Order[1]/Lines[-5]/LineNo", part].mergeSort)) := by
  native_decide

/-- The [inbound](../../../docs/sources/inbound-handbacks.md#inbound-2026-09-26m-error-target-paths)'s
model: `/Order` holds `Code`, the group `Meta` holds `Ref`, and `Lines` repeats. -/
private def pathModel : DmModel :=
  { flat := { fields := [text 1 O "Code" [], text 2 (O ++ ["Meta"]) "Ref" [], text 3 L "Sku" [10]]
              repeatableGroups := [{ level := 10, path := L, repeatability := some 5 }] }
    rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }

example : pathModel.flat.validate.isOk = true := by native_decide

/-- A refusal's expected class, or the reason a refusal without one must name. -/
private inductive Expected where
  | admitted
  | kernelClass (code : String)
  | noClass (reason : String)

private def meets (dm : DmModel) (group : GroupPath) (path condition : String) : Expected → Bool
  | expected =>
    let rule : DmRule :=
      { group, name := "PathProbe", errorCode := "P", errorEntityRelPath := path, condition,
        severity := "ERROR" }
    match checkValidationRule dm .english rule, expected with
    | .ok _, .admitted => true
    | .error refusal, .kernelClass code => refusal.kernelClass? == some code
    | .error refusal, .noClass reason =>
        refusal.kernelClass?.isNone && (refusal.detail.splitOn reason).length > 1
    | _, _ => false

/-- `(row, rule group, error entity, condition, Kernel verdict)`: a group the condition does not
name draws the reference class, the rule's own group fails the build with no class, and below the
root the root is an ordinary group. The path is read lexically, so `..` after a name drops it and
`../../Order` climbs through the top back to `/Order`, the rule's own group. -/
private def pathRows : List (String × GroupPath × String × String × Expected) := [
  ("p1", O, "../Meta", "FieldFilled(Code)", .kernelClass UNREFERENCED),
  ("p2", O, "../Meta/Ref/..", "FieldFilled(Code)", .kernelClass UNREFERENCED),
  ("p3", O, "../Code/..", "FieldFilled(Code)", .noClass "declaringGroup"),
  ("p4", O, "../Meta/../Code", "FieldFilled(Code)", .admitted),
  ("p7", O, "../../Order", "FieldFilled(Code)", .noClass "declaringGroup"),
  ("p5", O ++ ["Meta"], "../../Meta", "FieldFilled(Ref)", .noClass "declaringGroup"),
  ("p6", O ++ ["Meta"], "../..", "FieldFilled(Ref)", .kernelClass UNREFERENCED)]

example : (pathRows.filter fun (_, group, path, condition, expected) =>
    !meets pathModel group path condition expected).map (·.1) = [] := by native_decide

/-- The inbound's computations in `/Order`: into `../Code` admitted, into a group refused without a
class. -/
private def computes (target : String) : Option Bool :=
  match checkComputation pathModel .english
      { group := O, name := "C", targetRelPath := target, commonPrecondition := none,
        alternatives := [{ precondition := none, operation := "\"x\"" }], errorCodesToSuppress := [] } with
  | .ok _ => some true
  | .error refusal => if refusal.kernelClass?.isNone then some false else none

example : computes "../Code" = some true ∧ computes ".." = some false ∧ computes "../Meta" = some false := by
  native_decide

/-- A group target beside a join keeps the ordinary carrier's refusals without a class on its own
group ahead of every gate and for a root-only reference, while a read the walk cannot bind draws the
walk's class, as its field-target twin does (`p5`, `p6`). -/
example :
    meets dm (L ++ ["Parts"]) ".." "GroupFilled(/Order/Lines/Parts) And FieldFilled(/Order/Picks/Ref)"
      (.noClass "declaringGroup") ∧
    meets dm O "../Lines/Parts" "GroupFilled(/Order) And FieldFilled(Lines/Sku) And FieldFilled(Picks/Ref)"
      (.noClass "iterationScope") ∧
    meets dm O "../Lines/Parts" "GroupFilled(Lines/Parts) And FieldFilled(Picks/Ref) And FieldFilled(Wraps/Bows/Shade)"
      (.kernelClass "MVK_NO_WILDCARD") ∧
    meets dm O "../Lines/Sku" "FieldFilled(Lines/Sku) And FieldFilled(Picks/Ref) And FieldFilled(Wraps/Bows/Shade)"
      (.kernelClass "MVK_NO_WILDCARD") := by native_decide

/-- A fixed `Info` inside `Parts` beside the joined `Picks`: a fixed group at the error group's
level is read at its first row, its fields among the references. -/
private def innerModel : DmModel :=
  { flat := { fields := [text 10 L "LineNo" [10], text 20 (L ++ ["Parts"]) "PartNo" [10, 11],
                text 22 (L ++ ["Parts", "Info"]) "Text" [10, 11],
                text 30 (O ++ ["Picks"]) "LineNo" [13], text 31 (O ++ ["Picks"]) "Ref" [13]]
              repeatableGroups := [
                { level := 10, path := L, repeatability := some 50, indexField := some 10 },
                { level := 11, path := L ++ ["Parts"], repeatability := some 5 },
                { level := 13, path := O ++ ["Picks"], repeatability := some 10, indexField := some 30 }] }
    rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }

open Lean in
/-- The referenced pointers of the messages `condition` fires reporting on `entity` (by default
`Lines/Parts`, over one line `A` whose part holds `Info` and its pick). -/
private def referenced (condition : String) (dm : DmModel := innerModel) (entity := "Lines/Parts")
    (document : Json := Json.mkObj [("Order", Json.mkObj [
      ("Lines", Json.arr #[Json.mkObj [("LineNo", Json.str "A"), ("Parts", Json.arr #[Json.mkObj [
        ("PartNo", Json.str "x"), ("Info", Json.mkObj [("Text", Json.str "t")])]])]]),
      ("Picks", Json.arr #[Json.mkObj [("LineNo", Json.str "A"), ("Ref", Json.str "r")]])])]) :
    Option (List (List String)) := do
  let world : World := { now := { epochMillis := 0 } }
  let input ← (readDocument dm document).toOption
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler dm.flat).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let .parallel rule ← (checkValidationRule dm .english
    { group := O, name := "InnerProbe", errorCode := "P", errorEntityRelPath := "../" ++ entity, condition,
      severity := "ERROR" }).toOption | none
  let rows ← (runParallelRuleReferences checked rule (some world)).toOption
  rows.mapM fun (_, references) =>
    references.toOption.map fun references => references.referenced.map (renderFieldPointer dm.flat)

example :
    referenced "GroupFilled(Lines/Parts/Info) And GroupFilled(Lines/Parts) And FieldFilled(Picks/Ref)" =
      some [["Order/Lines/Parts/Info/Text", "Order/Lines/Parts/PartNo", "Order/Picks/Ref",
        "Order/Lines/LineNo", "Order/Picks/LineNo"]] := by native_decide

/-- Unkeyed `Slots` (2) inside the keyed `Lines` beside the joined `Picks`, the
[unkeyed capture](../../../evidence/kernel-30.8.1/captures/keyed-group-beside-join-2026-10-24/K22u_DM.json)'s shape. -/
private def slotsModel : DmModel :=
  { flat := { fields := [text 10 L "LineNo" [10], text 60 (L ++ ["Slots"]) "SlotNo" [10, 12],
                text 62 (L ++ ["Slots"]) "Mark" [10, 12],
                text 30 (O ++ ["Picks"]) "LineNo" [13], text 31 (O ++ ["Picks"]) "Ref" [13]]
              repeatableGroups := [
                { level := 10, path := L, repeatability := some 50, indexField := some 10 },
                { level := 12, path := L ++ ["Slots"], repeatability := some 2 },
                { level := 13, path := O ++ ["Picks"], repeatability := some 10, indexField := some 30 }] }
    rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }

open Lean in
/- An enclosing joined group's expansion keeps only its own repeatable level bound: the error group's
   `Slots` inside it is a wildcard, as `Parts` is, even though the rule reports on `Slots`
   ([checkpoint](../../../docs/sources/model-structure-and-declaration-probes.md#src-keyed-group-beside-join),
   `unkeyed`). -/
example :
    referenced "GroupFilled(Lines) And FieldFilled(Picks/Ref)" slotsModel "Lines/Slots"
        (Json.mkObj [("Order", Json.mkObj [
          ("Lines", Json.arr #[Json.mkObj [("LineNo", Json.str "A"), ("Slots", Json.arr #[
            Json.mkObj [("SlotNo", Json.str "1"), ("Mark", Json.str "m")], Json.mkObj [("SlotNo", Json.str "2")]])]]),
          ("Picks", Json.arr #[Json.mkObj [("LineNo", Json.str "A"), ("Ref", Json.str "r")]])])]) =
      some [["Order/Lines/LineNo", "/Order[1]/Lines[1]/Slots[0]/SlotNo", "/Order[1]/Lines[1]/Slots[0]/Mark",
        "Order/Picks/Ref", "Order/Picks/LineNo"]] := by native_decide


/-- The order fixture with the Number `Lines/Qty` the joined filled-count capture reads. -/
private def countDm : DmModel :=
  { dm with flat := { model with fields := model.fields ++ [number 12 L "Qty" [10]] } }

open Lean in
/- A filled count over the joined pair is the ordinary count, at every constant the guard admits
   ([checkpoint](../../../docs/sources/model-structure-and-declaration-probes.md#src-joined-filled-count),
   `runtime`): a malformed `Qty` makes `> 0` silent where the at-least-one quantifier would fire on the
   filled `Ref` (`badQty`), `== 0` fires where neither is filled, and `== 1` counts an unmatched
   partner as empty on both sides of the join (`unmatched`). -/
example :
    let order := fun (lines picks : List Json) => Json.mkObj [("Order", Json.mkObj [
      ("Lines", Json.arr lines.toArray), ("Picks", Json.arr picks.toArray)])]
    let line := fun (qty : Option String) => Json.mkObj ([("LineNo", Json.str "A")] ++
      (qty.map fun value => [("Qty", Json.str value)]).getD [])
    let pick := fun (key : String) (ref : Bool) => Json.mkObj ([("LineNo", Json.str key)] ++
      (if ref then [("Ref", Json.str "r")] else []))
    let count := fun (comparison : String) document =>
      firedOn "Lines/Qty" s!"NumberOfFilledFields(Lines/Qty, Picks/Ref) {comparison}" document countDm
    count "> 0" (order [line (some "x")] [pick "A" true]) = some [] ∧
    count "> 0" (order [line (some "1")] [pick "A" true]) = some ["Order/Lines/Qty"] ∧
    count "== 0" (order [line none] [pick "A" false]) = some ["Order/Lines/Qty"] ∧
    count "== 0" (order [line none] [pick "A" true]) = some [] ∧
    ((count "== 1" (order [line (some "1")] [pick "B" true])).map fun pointers =>
      pointers.length == 2 && pointers.contains "Order/Lines/Qty" &&
        pointers.contains "/Order[1]/Lines[-5]/Qty") = some true := by
  native_decide

open Lean in
/- A keyed error group beside the join holds the Kernel's parallel-iteration placeholder
   ([checkpoint](../../../docs/sources/model-structure-and-declaration-probes.md#src-keyed-group-beside-join),
   `runtime-keyed`): its presence is silent on a filled slot, an enclosing group's presence names
   `Lines[1]` for line `B` (`mixed`) with UNKNOWN at the group's own level, and its absence fires on
   a line without slots, referencing the group's fields at `[-6]` and the partner's index field but
   not its own side's. -/
example :
    let order := fun (lines picks : List Json) => Json.mkObj [("Order", Json.mkObj [
      ("Lines", Json.arr lines.toArray), ("Picks", Json.arr picks.toArray)])]
    let line := fun (key : String) (slots : List Json) => Json.mkObj [("LineNo", Json.str key), ("Sku", Json.str "s"),
      ("Slots", Json.arr slots.toArray)]
    let slot := Json.mkObj [("SlotNo", Json.str "1"), ("Mark", Json.str "m")]
    let pick := fun (key : String) (ref : Bool) => Json.mkObj ([("LineNo", Json.str key)] ++
      (if ref then [("Ref", Json.str "r")] else []))
    firedOn "Lines/Slots" "GroupFilled(Lines/Slots) And FieldFilled(Picks/Ref)"
        (order [line "A" [slot]] [pick "A" true]) = some [] ∧
    firedOn "Lines/Slots" "GroupFilled(Lines) And FieldFilled(Picks/Ref)"
        (order [line "A" [slot], line "B" []] [pick "B" true, pick "A" false]) = some ["/Order[1]/Lines[1]/Slots"] ∧
    firedOn "Lines/Slots" "GroupNotFilled(Lines/Slots) And FieldFilled(Picks/Ref)"
        (order [line "A" []] [pick "A" true]) = some ["/Order[1]/Lines[1]/Slots"] ∧
    ((referenced "GroupNotFilled(Lines/Slots) And FieldFilled(Picks/Ref)" dm "Lines/Slots"
        (order [line "A" []] [pick "A" true])).map (·.map (·.mergeSort))) =
      some [["/Order[1]/Lines[1]/Slots[-6]/Mark", "/Order[1]/Lines[1]/Slots[-6]/SlotNo",
        "/Order[1]/Lines[1]/Slots[-6]/Tagged[1]/Flag", "Order/Picks/LineNo", "Order/Picks/Ref"]] := by
  native_decide

end A12Kernel.Dm.GroupTargetLocks
