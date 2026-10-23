import A12Kernel.Reference.Dm.ComputationCheck
import A12Kernel.Reference.Dm.Document

/-! # Selections and the parallel error-field binding against the retained binding capture

Each row is one rule or computation of the
[binding capture](../../../docs/sources/model-structure-and-declaration-probes.md#src-iteration-binding-k04),
checked through the DM reader on a model with the capture's shape; the expected class is the
Kernel's verdict for the same text and target. The selection rows separate a selection's own row,
which it fixes, from its parent's and its key's rows, which it reads at the rule's row. The binding
rows separate a parallel iteration, which needs a reference of the error field itself in the join,
from an ordinary one beside the unkeyed `Wraps`, which draws the missing-star class instead.
-/

namespace A12Kernel.Dm.IterationBindingLocks

open A12Kernel

private def text (id : Nat) (groupPath : GroupPath) (name : String) (scope : List Nat) : FlatFieldDecl :=
  { id, name, groupPath, repeatableScope := scope, policy := { kind := .string } }

private def number (id : Nat) (groupPath : GroupPath) (name : String) (scope : List Nat) : FlatFieldDecl :=
  { text id groupPath name scope with policy := { kind := .number { scale := 0, signed := true } } }

private def O : GroupPath := ["Order"]
private def L : GroupPath := ["Order", "Lines"]
private def W : GroupPath := ["Order", "Wraps"]

/-- The capture's [order model](../../../evidence/kernel-30.8.1/captures/iteration-binding-2026-10-23/Order22c_DM.json):
the part of it the rows read: `Lines` and `Picks` both keyed by `LineNo`, and `Wraps` (2, unkeyed)
holding `Bows` (3, keyed by `BowNo`). -/
private def order : FlatModel :=
  { fields := [text 1 O "Email" [], text 2 O "Phone" [], text 3 O "Tier" [], number 4 O "Budget" [],
      text 10 L "LineNo" [10], text 11 L "Sku" [10], text 12 L "Code" [10], number 13 L "Qty" [10],
      number 14 L "Price" [10],
      text 20 (L ++ ["Parts"]) "PartNo" [10, 11], number 21 (L ++ ["Parts"]) "Count" [10, 11],
      text 30 (O ++ ["Picks"]) "LineNo" [13], text 31 (O ++ ["Picks"]) "Ref" [13],
      text 50 W "Style" [15], text 53 (W ++ ["Bows"]) "BowNo" [15, 16], text 54 (W ++ ["Bows"]) "Shade" [15, 16]]
    repeatableGroups := [
      { level := 10, path := L, repeatability := some 50, indexField := some 10 },
      { level := 11, path := L ++ ["Parts"], repeatability := some 5 },
      { level := 13, path := O ++ ["Picks"], repeatability := some 10, indexField := some 30 },
      { level := 15, path := W, repeatability := some 2 },
      { level := 16, path := W ++ ["Bows"], repeatability := some 3, indexField := some 53 }] }

/-- The [staffing plan](../../../evidence/kernel-30.8.1/captures/iteration-binding-2026-10-23/Plan22c_DM.json)
with `outer` empty, and the [rota](../../../evidence/kernel-30.8.1/captures/iteration-binding-2026-10-23/Rota22c_DM.json)
nesting both sides in the unkeyed `Weeks` (4 rows) otherwise: `Demand` and `Supply` repeat six times
keyed by `Shift`. -/
private def staffing (outer : GroupPath) (outerLevel : List Nat) : FlatModel :=
  let side (offset : Nat) (name : String) : List FlatFieldDecl :=
    let path := ["Plan"] ++ outer ++ [name]
    let scope := outerLevel ++ [offset]
    [text offset path "Shift" scope, number (offset + 1) path "Headcount" scope, text (offset + 2) path "Note" scope]
  { fields := side 20 "Demand" ++ side 30 "Supply"
    repeatableGroups := (outerLevel.map fun level => { level, path := ["Plan"] ++ outer, repeatability := some 4 }) ++ [
      { level := 20, path := ["Plan"] ++ outer ++ ["Demand"], repeatability := some 6, indexField := some 20 },
      { level := 30, path := ["Plan"] ++ outer ++ ["Supply"], repeatability := some 6, indexField := some 30 }] }

example : order.validate.isOk && (staffing [] []).validate.isOk && (staffing ["Weeks"] [10]).validate.isOk :=
  by native_decide

private def dm (flat : FlatModel) : DmModel :=
  { flat, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }

/-- The class this reader answers, `admitted`, or the refusal's detail when it carries no class, so
a refusal without a class fails a row rather than passing as any expected class. -/
private def classOf : Except Refusal α → String
  | .ok _ => "admitted"
  | .error refusal => refusal.kernelClass?.getD refusal.detail

private def rule (flat : FlatModel) (group : GroupPath) (errorField condition : String) : String :=
  classOf (checkValidationRule (dm flat) .english
    { group, name := "GuardProbe", errorCode := "P", errorEntityRelPath := "../" ++ errorField,
      condition, severity := "ERROR" })

/-- A computation into `Lines/Price`, declared at the root group, under an optional common
precondition and alternatives of `(precondition, operation)`. -/
private def computation (common : Option String) (alternatives : List (Option String × String)) : String :=
  classOf (checkComputation (dm order) .english
    { group := O, name := "PriceProbe", targetRelPath := "../Lines/Price", commonPrecondition := common,
      alternatives := alternatives.map fun (precondition, operation) => { precondition, operation },
      errorCodesToSuppress := [] })

private def guarded (precondition : String) : String := computation (some precondition) [(none, "1")]

/-- The capture's `k08`: `1` into the part's `Count`, below the joined `Lines`. -/
private def nestedGuarded (precondition : String) : String :=
  classOf (checkComputation (dm order) .english
    { group := O, name := "CountProbe", targetRelPath := "../Lines/Parts/Count",
      commonPrecondition := some precondition, alternatives := [{ precondition := none, operation := "1" }],
      errorCodesToSuppress := [] })

private def NEG := "MVK_NEG_CONDITION_IN_ITERATION"
private def BIND := "MVK_ERROR_FIELD_AND_ITERATION_INVALID"
private def STAR := "MVK_NO_WILDCARD"

/-- `(capture row, reader verdict, Kernel class)`. -/
private def rows : List (String × String × String) := [
  -- A selection fixes its own row: one of `Lines` reads no `Lines` row of the rule.
  ("s1", rule order O "Lines/Qty" "FieldNotFilled(Lines/Qty) And FieldFilled(Lines/Sku For \"1\")", NEG),
  ("s2", rule order O "Lines/Qty" "FieldFilled(Lines/Qty) And FieldNotFilled(Lines/Sku For \"1\")", "admitted"),
  -- In a field-fill list a constant selection is one independent slot.
  ("s3", rule order O "Lines/Sku" "NoFieldFilled(Lines/Sku, Picks/Ref For \"1\")", NEG),
  ("s4", rule order O "Lines/Sku" "MoreThanOneFieldFilled(Lines/Qty, Picks/Ref For \"1\") And FieldNotFilled(Lines/Sku)",
    "admitted"),
  ("s5", rule order O "Lines/Sku"
    "MoreThanOneFieldFilled(Lines/Qty, Picks/Ref For \"1\", Picks/Ref For \"2\") And FieldNotFilled(Lines/Sku)", NEG),
  -- Its parent's row and its key's row are the rule's: they bind there and guard there.
  ("s6", rule order O "Wraps/Style" "FieldFilled(Wraps/Bows/Shade For \"a\") And FieldNotFilled(Wraps/Style)", "admitted"),
  ("s7", rule order O "Wraps/Style" "FieldFilled(Wraps/Style) And FieldNotFilled(Wraps/Bows/Shade For \"a\")", "admitted"),
  ("s8", rule order O "Lines/Qty" "FieldFilled(Lines/Qty) And FieldNotFilled(Picks/Ref For Lines/LineNo)", "admitted"),
  -- The guarded pair over a field below a joined side, its authored line break included.
  ("s9", rule order O "Lines/Parts/Count"
    "FieldFilled(Lines/Parts/Count) And (NoFieldFilled(Lines/Parts/PartNo, Picks/Ref)\n) And [Lines/Parts/Count] != 1",
    "admitted"),
  ("d5", rule order O "Lines/Sku" "NoFieldFilled(Lines/Sku, Picks/Ref For Lines/LineNo)", NEG),
  ("d6", rule order O "Lines/Qty" "FieldNotFilled(Lines/Qty) And FieldFilled(Picks/Ref For Lines/LineNo)", "admitted"),
  -- A negative selection alone fails the level it references, a positive guards it.
  ("v1", rule order O "Wraps/Style" "FieldFilled(Wraps/Style) Or FieldNotFilled(Wraps/Bows/Shade For \"a\")", NEG),
  ("v2", rule order O "Wraps/Bows/Shade" "FieldNotFilled(Wraps/Bows/Shade For \"a\")", NEG),
  ("v3", rule order O "Wraps/Bows/Shade" "FieldFilled(Wraps/Bows/Shade For \"a\")", "admitted"),
  -- A constant selection of the iterated group's own field is one independent slot.
  ("v4", rule order O "Lines/Qty" "AtLeastOneFieldFilled(Lines/Qty, Lines/Sku For \"1\")", NEG),
  ("v5", rule order O "Lines/Qty" "MoreThanOneFieldFilled(Lines/Qty, Lines/Sku For \"1\") And FieldNotFilled(Lines/Qty)",
    "admitted"),
  ("v6", rule order O "Lines/Qty"
    "MoreThanOneFieldFilled(Lines/Qty, Lines/Sku For \"1\", Lines/Sku For \"2\") And FieldNotFilled(Lines/Qty)", NEG),
  ("v15", rule order O "Lines/Sku" "FieldValuesNotUnique(Lines/Sku, Lines/Code For \"1\", Lines/Code For \"2\")", NEG),
  ("v16", rule order O "Lines/Sku" "FieldValuesNotUnique(Lines/Sku, Lines/Code For \"1\")", "admitted"),
  -- A group selection binds and guards as a field selection does.
  ("v7", rule order O "Wraps/Style" "GroupFilled(Wraps/Bows For \"a\") And FieldNotFilled(Wraps/Style)", "admitted"),
  ("v8", rule order O "Wraps/Style" "FieldFilled(Wraps/Style) And GroupNotFilled(Wraps/Bows For \"a\")", "admitted"),
  ("v9", rule order O "Lines/Qty" "GroupFilled(Picks For Lines/LineNo) And FieldNotFilled(Lines/Qty)", "admitted"),
  ("v10", rule order O "Lines/Qty" "FieldFilled(Lines/Qty) And GroupNotFilled(Picks For Lines/LineNo)", "admitted"),
  ("v11", rule order O "Wraps/Style" "FieldNotFilled(Wraps/Style) And GroupFilled(Wraps/Bows For \"a\")", "admitted"),
  ("v17", rule order O "Wraps/Bows/Shade" "GroupNotFilled(Wraps/Bows For \"a\")", NEG),
  ("v18", rule order O "Wraps/Bows/Shade" "GroupFilled(Wraps/Bows For \"a\")", "admitted"),
  -- An error field read only through a star: beside the unkeyed `Wraps` its row is unbound, beside
  -- the keyed `Picks` the join lacks it, until an unstarred read of it joins.
  ("d1", rule order O "Lines/Sku" "FieldsNotCollectivelyFilled(Lines*/Sku, Wraps/Style)", STAR),
  ("d2", rule order O "Lines/Qty" "Sum(Lines*/Qty) > 0 And FieldFilled(Wraps/Style)", STAR),
  ("a09", rule order O "Lines/Sku" "FieldsNotCollectivelyFilled(Lines*/Sku, Picks/Ref)", BIND),
  ("d3", rule order O "Lines/Qty" "Sum(Lines*/Qty) > 0 And FieldFilled(Picks/Ref)", BIND),
  ("d4", rule order O "Lines/Sku" "FieldFilled(Lines/Sku) And FieldsNotCollectivelyFilled(Lines*/Sku, Picks/Ref)",
    "admitted"),
  ("b1", rule (staffing [] []) ["Plan"] "Demand/Headcount" "FieldsNotCollectivelyFilled(Demand*/Headcount, Supply/Headcount)",
    BIND),
  -- A read of the error field's group is not a read of the error field.
  ("b2", rule (staffing [] []) ["Plan"] "Demand/Headcount"
    "FieldFilled(Demand/Note) And NoFieldFilled(Demand*/Headcount, Supply/Headcount)", BIND),
  ("b3", rule (staffing [] []) ["Plan"] "Demand/Headcount" "Sum(Demand*/Headcount) > 0 And FieldFilled(Supply/Note)", BIND),
  ("b4", rule (staffing [] []) ["Plan"] "Demand/Headcount"
    "FieldFilled(Demand/Headcount) And FieldsNotCollectivelyFilled(Demand*/Headcount, Supply/Headcount)", "admitted"),
  ("b5", rule (staffing [] []) ["Plan"] "Demand/Headcount" "AtLeastOneFieldFilled(Demand/Headcount, Supply/Headcount)",
    "admitted"),
  ("b6", rule (staffing [] []) ["Plan"] "Demand/Headcount" "Sum(Demand*/Headcount) > 0", "admitted"),
  -- The binding precedes the guard: the unguarded `NoFieldFilled` draws it, not the parallel class.
  ("w1", rule (staffing ["Weeks"] [10]) ["Plan"] "Weeks/Demand/Headcount"
    "NoFieldFilled(Weeks/Demand*/Headcount, Weeks/Supply/Headcount)", BIND),
  ("w2", rule (staffing ["Weeks"] [10]) ["Plan"] "Weeks/Demand/Headcount"
    "NoFieldFilled(Weeks/Demand/Headcount, Weeks/Supply/Headcount)", "MVK_PARALLEL_ITERATION_INVALID"),
  -- A containing group joins only at or below the joined group: `Weeks` does not, `Weeks/Demand` does.
  ("v12", rule (staffing ["Weeks"] [10]) ["Plan"] "Weeks/Demand/Headcount"
    "GroupFilled(Weeks) And FieldFilled(Weeks/Demand/Note) And FieldsNotCollectivelyFilled(Weeks/Demand*/Headcount, Weeks/Supply/Headcount)",
    BIND),
  ("v13", rule (staffing ["Weeks"] [10]) ["Plan"] "Weeks/Demand/Headcount"
    "GroupFilled(Weeks/Demand) And FieldFilled(Weeks/Demand/Note) And FieldsNotCollectivelyFilled(Weeks/Demand*/Headcount, Weeks/Supply/Headcount)",
    "admitted"),
  ("v14", rule (staffing ["Weeks"] [10]) ["Plan"] "Weeks/Demand/Headcount"
    "FieldFilled(Weeks/Demand/Headcount) And FieldsNotCollectivelyFilled(Weeks/Demand*/Headcount, Weeks/Supply/Headcount)",
    "admitted"),
  -- A computation precondition meets no negative-condition gate; a nested read of the line is unbound.
  ("k01", guarded "FieldNotFilled(Lines/Sku)", "admitted"),
  ("k02", guarded "NoFieldFilled(Lines/Sku, Picks/Ref)", "admitted"),
  ("k03", guarded "FieldNotFilled(Lines/Sku) Or FieldNotFilled(Email)", "admitted"),
  ("k04", computation (some "FieldNotFilled(Lines/Sku)")
    [(some "FieldNotFilled(Email)", "1"), (some "FieldFilled(Email)", "2")], "admitted"),
  ("k05", computation none [(some "FieldNotFilled(Lines/Sku)", "1"), (some "FieldNotFilled(Lines/Code)", "2")],
    "admitted"),
  ("k06", guarded "CurrentRepetition(Lines) > 1", "admitted"),
  ("k07", guarded "FieldNotFilled(Picks/Ref)", "admitted"),
  ("k08", nestedGuarded "NoFieldFilled(Lines/Parts/PartNo, Picks/Ref)", "admitted"),
  ("k09", guarded "NoFieldFilled(Lines/Parts/PartNo, Picks/Ref)", STAR),
  ("k10", guarded "FieldNotFilled(Lines/Parts/PartNo)", STAR)]

/-- The rows this reader answers otherwise, each named by its capture row. -/
private def mismatches : List (String × String × String) :=
  rows.filterMap fun (id, actual, expected) => if actual == expected then none else some (id, expected, actual)

example : mismatches = [] := by native_decide

open Lean in
/-- The error pointers a rule over `Lines` rows of `(LineNo, Qty)` fires at, beside `Picks` rows of
`(LineNo, Ref)` and `Wraps` rows, each holding `Bows` rows of `(BowNo, Shade)`. -/
private def fired (errorField condition : String) (lines : List (String × String))
    (picks : List (String × Option String)) (wraps : List (List (String × String))) : Option (List String) := do
  let world : World := { now := { epochMillis := 0 } }
  let lineRows := lines.map fun (no, qty) => Json.mkObj [("LineNo", Json.str no), ("Qty", Json.str qty)]
  let pickRows := picks.map fun (no, ref) =>
    Json.mkObj ([("LineNo", Json.str no)] ++ ref.toList.map (("Ref", Json.str ·)))
  let wrapRows := wraps.map fun bows => Json.mkObj [("Style", Json.str "s"), ("Bows", Json.arr (bows.map fun (no, shade) =>
    Json.mkObj [("BowNo", Json.str no), ("Shade", Json.str shade)]).toArray)]
  let input ← (readDocument (dm order) (Json.mkObj [("Order", Json.mkObj [
    ("Lines", Json.arr lineRows.toArray), ("Picks", Json.arr pickRows.toArray), ("Wraps", Json.arr wrapRows.toArray)])])).toOption
  if !input.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler order).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  let definition : DmRule :=
    { group := O, name := "GuardProbe", errorCode := "P", errorEntityRelPath := "../" ++ errorField,
      condition, severity := "ERROR" }
  let checked ← (checkRule (dm order) .english definition).toOption
  pure ((← (runRule world document checked).toOption).map fun message => (observe order message).pointer)

/-- Internal witnesses, `external evidence pending`: the key is read at the rule's `Lines` row, so
only the line whose `LineNo` selects no filled `Picks` row fires; a read of one fixed line would fire
at every row or none. A constant selection below `Wraps` reads the rule's own `Wraps` row's `Bows`,
so of two rows only the second, whose `Bows` hold the key, fires. -/
example : fired "Lines/Qty" "FieldFilled(Lines/Qty) And FieldNotFilled(Picks/Ref For Lines/LineNo)"
      [("1", "5"), ("2", "6"), ("3", "7")] [("1", some "r"), ("3", none)] [] =
      some ["Order/Lines[2]/Qty", "Order/Lines[3]/Qty"] ∧
    fired "Wraps/Style" "FieldFilled(Wraps/Bows/Shade For \"a\") And FieldFilled(Wraps/Style)" []
      [] [[("b", "blue")], [("a", "red"), ("c", "green")]] = some ["Order/Wraps[2]/Style"] ∧
    fired "Wraps/Style" "FieldFilled(Wraps/Bows/Shade For \"c\") And FieldFilled(Wraps/Style)" []
      [] [[("a", "red")]] = some [] := by native_decide

end A12Kernel.Dm.IterationBindingLocks
