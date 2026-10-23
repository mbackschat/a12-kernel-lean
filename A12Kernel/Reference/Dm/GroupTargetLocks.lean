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
`Lines` (50, keyed) holds `Parts` (5); `Picks` (10, keyed by `LineNo`), `Gifts` (2, keyed) with a
fixed `Card`, and `Wraps` (2, unkeyed) with fixed `Ribbon` and `Tag` and keyed `Bows` (3). -/
private def model : FlatModel :=
  { fields := [text 1 O "Email" [],
      text 10 L "LineNo" [10], text 11 L "Sku" [10],
      text 20 (L ++ ["Parts"]) "PartNo" [10, 11], number 21 (L ++ ["Parts"]) "Count" [10, 11],
      text 30 (O ++ ["Picks"]) "LineNo" [13], text 31 (O ++ ["Picks"]) "Ref" [13],
      text 40 (O ++ ["Gifts"]) "GiftNo" [14], text 41 (O ++ ["Gifts"]) "Note" [14],
      text 42 (O ++ ["Gifts", "Card"]) "Text" [14],
      text 50 W "Style" [15], text 51 (W ++ ["Ribbon"]) "Color" [15], text 52 (W ++ ["Tag"]) "Label" [15],
      text 53 (W ++ ["Bows"]) "BowNo" [15, 16], text 54 (W ++ ["Bows"]) "Shade" [15, 16]]
    repeatableGroups := [
      { level := 10, path := L, repeatability := some 50, indexField := some 10 },
      { level := 11, path := L ++ ["Parts"], repeatability := some 5 },
      { level := 13, path := O ++ ["Picks"], repeatability := some 10, indexField := some 30 },
      { level := 14, path := O ++ ["Gifts"], repeatability := some 2, indexField := some 40 },
      { level := 15, path := W, repeatability := some 2 },
      { level := 16, path := W ++ ["Bows"], repeatability := some 3, indexField := some 53 }] }

example : model.validate.isOk = true := by native_decide

private def dm : DmModel :=
  { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }

/-- The class this reader answers, `admitted`, or the refusal's detail when it carries no class, so
a refusal without a class fails a row rather than passing as any expected class. -/
private def verdict (errorEntity condition : String) : String :=
  let rule : DmRule :=
    { group := O, name := "GroupProbe", errorCode := "P", errorEntityRelPath := "../" ++ errorEntity,
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

/-- Whether this reader refuses a rule without a Kernel class. -/
private def unclassed (errorEntity condition : String) : Bool :=
  match checkValidationRule dm .english
      { group := O, name := "GroupProbe", errorCode := "P", errorEntityRelPath := "../" ++ errorEntity,
        condition, severity := "ERROR" } with
  | .ok _ => false
  | .error refusal => refusal.kernelClass?.isNone

/-- This reader's account of a group target beside a join where no capture measures the composition:
the ordinary carrier's gates, so a field inside the group does not reference it (`t3`) and a negative
presence of the group leaves its own level unguarded (`g03`), while a field inside it is read at its
first row (`t2`). A leaf the ordinary group target refuses and the joined group itself are refused
without a class. -/
example :
    verdict "Lines/Parts" "FieldFilled(Lines/Parts/Count) And FieldFilled(Picks/Ref)" = UNREFERENCED ∧
    verdict "Lines/Parts" "GroupNotFilled(Lines/Parts) And FieldFilled(Picks/Ref)" =
      "MVK_NEG_CONDITION_IN_ITERATION" ∧
    verdict "Lines/Parts" "GroupFilled(Lines/Parts) And FieldNotFilled(Lines/Parts/PartNo) And FieldFilled(Picks/Ref)" =
      "admitted" ∧
    verdict "Lines/Parts" "GroupFilled(Lines) And FieldFilled(Picks/Ref)" = "admitted" ∧
    unclassed "Lines/Parts" "GroupFilled(Lines/Parts) And AtLeastOneFieldFilled(Lines/Sku, Picks/Ref)" ∧
    unclassed "Lines" "GroupFilled(Lines) And FieldFilled(Picks/Ref)" := by native_decide

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

/-- A group target beside a join keeps the ordinary carrier's refusals without a class: on its own
group ahead of every gate, for a root-only reference, and at a read the walk cannot bind, where the
field-target twin draws the walk's class. -/
example :
    meets dm (L ++ ["Parts"]) ".." "GroupFilled(/Order/Lines/Parts) And FieldFilled(/Order/Picks/Ref)"
      (.noClass "declaringGroup") ∧
    meets dm O "../Lines/Parts" "GroupFilled(/Order) And FieldFilled(Lines/Sku) And FieldFilled(Picks/Ref)"
      (.noClass "iterationScope") ∧
    meets dm O "../Lines/Parts" "GroupFilled(Lines/Parts) And FieldFilled(Picks/Ref) And FieldFilled(Wraps/Bows/Shade)"
      (.noClass "iterationScope") ∧
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
/-- The referenced pointers of the messages `condition` fires reporting on `Lines/Parts`, over one
line `A` whose part holds `Info` and its pick. -/
private def referenced (condition : String) : Option (List (List String)) := do
  let world : World := { now := { epochMillis := 0 } }
  let part := Json.mkObj [("PartNo", Json.str "x"), ("Info", Json.mkObj [("Text", Json.str "t")])]
  let document := Json.mkObj [("Order", Json.mkObj [
    ("Lines", Json.arr #[Json.mkObj [("LineNo", Json.str "A"), ("Parts", Json.arr #[part])]]),
    ("Picks", Json.arr #[Json.mkObj [("LineNo", Json.str "A"), ("Ref", Json.str "r")]])])]
  let input ← (readDocument innerModel document).toOption
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler innerModel.flat).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let .parallel rule ← (checkValidationRule innerModel .english
    { group := O, name := "InnerProbe", errorCode := "P", errorEntityRelPath := "../Lines/Parts", condition,
      severity := "ERROR" }).toOption | none
  let rows ← (runParallelRuleReferences checked rule (some world)).toOption
  rows.mapM fun (_, references) =>
    references.toOption.map fun references => references.referenced.map (renderFieldPointer innerModel.flat)

example :
    referenced "GroupFilled(Lines/Parts/Info) And GroupFilled(Lines/Parts) And FieldFilled(Picks/Ref)" =
      some [["Order/Lines/Parts/Info/Text", "Order/Lines/Parts/PartNo", "Order/Picks/Ref",
        "Order/Lines/LineNo", "Order/Picks/LineNo"]] := by native_decide

end A12Kernel.Dm.GroupTargetLocks
