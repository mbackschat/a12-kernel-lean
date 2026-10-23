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

/-- `(capture row, error entity, condition, Kernel class)`. Row `t8` reports on a group in a
parallel iteration, which the parallel carrier does not represent. -/
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

end A12Kernel.Dm.GroupTargetLocks
