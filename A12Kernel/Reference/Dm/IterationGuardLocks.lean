import A12Kernel.Reference.Dm.ParallelValidation
import A12Kernel.Reference.Dm.Validate
import A12Kernel.Reference.Dm.Document

/-! # The ordinary iteration guard against the retained K04 capture

Each row is one rule of the
[iteration-guard capture](../../../docs/sources/model-structure-and-declaration-probes.md#src-iteration-guard-k04),
checked through the DM reader on a model with the capture's shape; the expected class is the
Kernel's `rule check` verdict for the same condition and error field. The rows separate a level
the guard skips (twice-repeating and keyed) from a judged one, and each comparison rule the Kernel
applies to a leaf it otherwise allows: a count below a positive constant, an operation equal to
zero, and an operation mixing row and fixed reads against any constant. The constant rows on `Sum`
also need a direct list of row fields, which the addressed comparison carrier reads at the rule's
row; the runtime rows separate that per-row read from one fixed row or a sum across rows.
-/

namespace A12Kernel.Dm.IterationGuardLocks

open A12Kernel

private def text (id : Nat) (groupPath : GroupPath) (name : String) (scope : List Nat) : FlatFieldDecl :=
  { id, name, groupPath, repeatableScope := scope, policy := { kind := .string } }

private def number (id : Nat) (groupPath : GroupPath) (name : String) (scope : List Nat) (scale : Nat) :
    FlatFieldDecl :=
  { text id groupPath name scope with policy := { kind := .number { scale, signed := true } } }

private def O : GroupPath := ["Order"]
private def L : GroupPath := ["Order", "Lines"]

/-- The capture's [order model](../../../evidence/kernel-30.8.1/captures/iteration-guard-2026-10-22/IterGuard_DM.json): `Lines` (50 rows, keyed) holds `Parts` (5) and `Slots` (2, keyed);
`Picks` (10, keyed), `Gifts` (2, keyed) and `Wraps` (2, unkeyed) sit beside it. -/
private def model : FlatModel :=
  { fields := [text 1 O "Email" [], text 2 O "Phone" [], text 3 O "Tier" [], number 4 O "Budget" [] 0,
      text 10 L "LineNo" [10], text 11 L "Sku" [10], text 12 L "Code" [10], number 13 L "Qty" [10] 0,
      number 14 L "Price" [10] 2, number 15 L "Day" [10] 0, number 16 L "Month" [10] 0,
      text 20 (L ++ ["Parts"]) "PartNo" [10, 11], number 21 (L ++ ["Parts"]) "Count" [10, 11] 0,
      text 22 (L ++ ["Slots"]) "SlotNo" [10, 12], text 23 (L ++ ["Slots"]) "Mark" [10, 12],
      text 30 (O ++ ["Picks"]) "LineNo" [13], text 31 (O ++ ["Picks"]) "Ref" [13],
      text 40 (O ++ ["Gifts"]) "GiftNo" [14], text 41 (O ++ ["Gifts"]) "Note" [14],
      text 42 (O ++ ["Gifts", "Card"]) "Text" [14],
      text 50 (O ++ ["Wraps"]) "Style" [15], text 51 (O ++ ["Wraps", "Ribbon"]) "Color" [15],
      text 52 (O ++ ["Wraps", "Tag"]) "Label" [15]]
    repeatableGroups := [
      { level := 10, path := L, repeatability := some 50, indexField := some 10 },
      { level := 11, path := L ++ ["Parts"], repeatability := some 5 },
      { level := 12, path := L ++ ["Slots"], repeatability := some 2, indexField := some 22 },
      { level := 13, path := O ++ ["Picks"], repeatability := some 10, indexField := some 30 },
      { level := 14, path := O ++ ["Gifts"], repeatability := some 2, indexField := some 40 },
      { level := 15, path := O ++ ["Wraps"], repeatability := some 2 }] }

example : model.validate.isOk = true := by native_decide

private def dm : DmModel :=
  { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }

/-- The class this reader answers, `admitted`, or the refusal's detail when it carries no class, so
a refusal without a class fails a row rather than passing as any expected class. -/
private def verdict (group : GroupPath) (errorField condition : String) : String :=
  let rule : DmRule :=
    { group, name := "GuardProbe", errorCode := "P", errorEntityRelPath := "../" ++ errorField,
      condition, severity := "ERROR" }
  match checkValidationRule dm .english rule with
  | .ok _ => "admitted"
  | .error refusal => refusal.kernelClass?.getD refusal.detail

private def NEG := "MVK_NEG_CONDITION_IN_ITERATION"

/-- `(capture row, rule group, error field, condition, Kernel class)`. -/
private def rows : List (String × GroupPath × String × String × String) := [
  ("c01", O, "Lines/Sku", "FieldNotFilled(Lines/Sku)", NEG),
  ("c02", O, "Lines/Sku", "FieldFilled(Lines/Qty) And FieldNotFilled(Lines/Sku)", "admitted"),
  -- `Gifts` and `Lines/Slots` repeat twice and are keyed, so the guard never judges their level.
  ("e01", O, "Gifts/Card/Text", "FieldNotFilled(Gifts/Card/Text)", "admitted"),
  ("e02", O, "Gifts/Note", "FieldNotFilled(Gifts/Note)", "admitted"),
  ("e03", O, "Wraps/Ribbon/Color", "FieldNotFilled(Wraps/Ribbon/Color)", NEG),
  ("e04", O ++ ["Gifts"], "Note", "FieldNotFilled(Note)", "admitted"),
  ("e05", O, "Gifts/GiftNo", "FieldNotFilled(Gifts/GiftNo)", "admitted"),
  ("e06", O, "Lines/Slots/Mark", "FieldNotFilled(Lines/Slots/Mark)", NEG),
  ("e07", O, "Lines/Slots/Mark", "FieldFilled(Lines/Sku) And FieldNotFilled(Lines/Slots/Mark)", "admitted"),
  ("e08", O, "Gifts/Note", "NoFieldFilled(Gifts/Note, Gifts/GiftNo)", "admitted"),
  ("e09", O, "Gifts/Note", "NumberOfFilledFields(Gifts/Note, Gifts/GiftNo) < 1", "admitted"),
  ("e10", O, "Picks/Ref", "FieldNotFilled(Picks/Ref)", NEG),
  ("e11", O, "Gifts/Note", "GroupNotFilled(Gifts/Card) And FieldFilled(Gifts/Note)", "admitted"),
  -- A count below a positive constant, read from either side, needs a filled row.
  ("u01", O, "Lines/Qty", "NumberOfFilledFields(Lines/Qty, Lines/Price) < 1", NEG),
  ("u02", O, "Lines/Qty", "NumberOfFilledFields(Lines/Qty, Lines/Price) <= 1", NEG),
  ("u03", O, "Lines/Qty", "NumberOfFilledFields(Lines/Qty, Lines/Price) != 1", NEG),
  ("u04", O, "Lines/Qty", "1 > NumberOfFilledFields(Lines/Qty, Lines/Price)", NEG),
  ("u05", O, "Lines/Qty", "1 >= NumberOfFilledFields(Lines/Qty, Lines/Price)", NEG),
  ("u06", O, "Lines/Qty", "1 != NumberOfFilledFields(Lines/Qty, Lines/Price)", NEG),
  ("u07", O, "Lines/Qty", "{NumberOfFilledFields(Lines/Qty, Lines/Price)} < 1", NEG),
  ("u08", O, "Lines/Qty", "NumberOfFilledFields(Lines/Qty, Lines/Price) > 1", "admitted"),
  ("u09", O, "Lines/Qty", "1 < NumberOfFilledFields(Lines/Qty, Lines/Price)", "admitted"),
  -- A count is not zero-sensitive: at most zero and equal to zero are admitted.
  ("u10", O, "Lines/Qty", "NumberOfFilledFields(Lines/Qty, Lines/Price) <= 0", "admitted"),
  ("u11", O, "Lines/Qty", "NumberOfFilledFields(Lines/Qty, Lines/Price) == 0", "admitted"),
  ("u12", O, "Lines/Qty", "NumberOfFilledFields(Lines/Qty, Email) > 1", NEG),
  ("u13", O, "Lines/Qty", "NumberOfFilledFields(Lines/Qty, Email) > 1234567890123456", NEG),
  ("u14", O, "Lines/Qty", "NumberOfFilledFields(Lines/Qty, Lines/Price) >= 1", "admitted"),
  ("u15", O, "Lines/Sku", "NumberOfDifferentValues(Lines/Sku, Lines/Code) < 1", NEG),
  ("u16", O, "Lines/Sku", "NumberOfDifferentValues(Lines/Sku, Lines/Code) > 0", "admitted"),
  ("u17", O, "Lines/Sku", "FieldFilled(Lines/Sku) Or CurrentRepetition(Lines) > 2", NEG),
  ("u18", O, "Lines/Sku", "FieldFilled(Lines/Sku) And CurrentRepetition(Lines) > 2", "admitted"),
  ("u19", O, "Lines/Sku", "NoFieldValueIncludedInValueList(Lines/Sku In \"X\", \"Y\")", NEG),
  ("u20", O, "Lines/Sku", "FieldFilled(Lines/Qty) And NoFieldValueIncludedInValueList(Lines/Sku In \"X\")",
    "admitted"),
  ("u21", O, "Lines/Code", "NotAllFieldValuesIncludedInValueList(Tier, Lines/Code In \"X\")", NEG),
  ("u22", O, "Lines/Code", "NotAllFieldValuesIncludedInValueList(Lines/Code In \"X\")", "admitted"),
  ("u23", O, "Lines/Code", "AtLeastOneFieldValueIncludedInValueList(Tier, Lines/Code In \"X\")", NEG),
  ("u24", O, "Lines/Code", "AtLeastOneFieldValueIncludedInValueList(Lines/Code In \"X\")", "admitted"),
  ("u25", O, "Lines/Qty", "Max([Lines/Qty], [Budget]) > 5", NEG),
  ("u26", O, "Lines/Qty", "Max([Lines/Qty], [Lines/Price]) > 5", "admitted"),
  -- A bracket only groups: the constant or read inside it is what the comparison sees.
  ("u27", O, "Lines/Price", "[Lines/Price] == {0}", NEG),
  ("u28", O, "Lines/Price", "[Lines/Price] == 0", NEG),
  ("u29", O, "Lines/Price", "[Lines/Price] == {1}", "admitted"),
  ("u30", O, "Lines/Price", "{[Lines/Price]} == 0", NEG),
  -- Value operations over a direct list of row fields: zero refuses, a constant rounding to one
  -- does not, and a fixed member mixes the reads.
  ("a01", O, "Lines/Qty", "Sum(Lines/Qty, Lines/Price) == 0", NEG),
  ("a02", O, "Lines/Qty", "Sum(Lines/Qty, Lines/Price) == 0.5", "admitted"),
  ("a03", O, "Lines/Qty", "MinValue(Lines/Qty, Lines/Price) == 0", NEG),
  ("a04", O, "Lines/Qty", "MaxValue(Lines/Qty, Lines/Price) > 0", "admitted"),
  ("a05", O, "Lines/Day", "Sum(Lines/Day, Lines/Month) > 31", "admitted"),
  ("a06", O, "Lines/Qty", "Sum(Lines/Qty, Budget) > 5", NEG),
  -- An error field the condition never names answers ahead of the guard; `o04` and `a12` keep
  -- their own classes beside it.
  ("o01", O, "Lines/Sku", "FieldNotFilled(Lines/Qty)", "MVK_ERROR_FIELD_NOT_REFERENCED"),
  ("o02", O, "Lines/Sku", "FieldFilled(Lines/Qty)", "MVK_ERROR_FIELD_NOT_REFERENCED"),
  ("o03", O, "Lines/Sku", "NumberOfFilledFields(Lines/Qty, Lines/Price) < 1", "MVK_ERROR_FIELD_NOT_REFERENCED"),
  ("o04", O, "Email", "FieldNotFilled(Email) And FieldNotFilled(Lines/Qty)", "MVK_NO_WILDCARD"),
  ("a12", O, "Lines/Sku", "NoFieldFilled(Lines/Sku, Picks/Ref)", "MVK_PARALLEL_ITERATION_INVALID")]

/-- The peer's Kernel rows ([inbound](../../../docs/sources/inbound-handbacks.md#src-inbound-2026-10-22b),
`CheckerIterationGuardAgreementTest`) on the same model shape: the constant beside a direct
row-field `Sum` under half-up rounding, 32-bit narrowing and a mirrored side, and the zero rule on
further value operations. -/
private def peerRows : List (String × GroupPath × String × String × String) :=
  let sum (constant : String) := s!"Sum(Lines/Qty, Lines/Price) == {constant}"
  [("c0.4", O, "Lines/Qty", sum "0.4", NEG), ("c0.5", O, "Lines/Qty", sum "0.5", "admitted"),
   ("c-0.4", O, "Lines/Qty", sum "-0.4", NEG), ("c-0.5", O, "Lines/Qty", sum "-0.5", NEG),
   ("c-0.50", O, "Lines/Qty", sum "-0.50", NEG), ("c- 0.4", O, "Lines/Qty", sum "- 0.4", NEG),
   ("c-0.6", O, "Lines/Qty", sum "-0.6", "admitted"), ("c2^32", O, "Lines/Qty", sum "4294967296", NEG),
   ("c2^32e9", O, "Lines/Qty", sum "4294967296000000000", NEG), ("b{0}", O, "Lines/Qty", sum "{0}", NEG),
   ("b{sum}", O, "Lines/Qty", "{Sum(Lines/Qty, Lines/Price)} == 0", NEG),
   ("0==sum", O, "Lines/Qty", "0 == Sum(Lines/Qty, Lines/Price)", NEG),
   ("sum<0", O, "Lines/Qty", "Sum(Lines/Qty, Lines/Price) < 0", "admitted"),
   ("sum>=0", O, "Lines/Qty", "Sum(Lines/Qty, Lines/Price) >= 0", NEG),
   ("sum<=0", O, "Lines/Qty", "Sum(Lines/Qty, Lines/Price) <= 0", NEG),
   ("nvif==0", O, "Lines/Qty", "NumberOfValueInFields(0 In Lines/Qty, Lines/Price) == 0", NEG),
   ("ff<=0", O, "Lines/Qty", "FirstFilledValue(Lines/Qty, Lines/Price) <= 0", NEG),
   ("abs==0", O, "Lines/Qty", "Abs([Lines/Qty] - [Lines/Price]) == 0", NEG),
   ("len==0", O, "Lines/Sku", "Length(Lines/Sku) == 0", NEG),
   ("len>0", O, "Lines/Sku", "Length(Lines/Sku) > 0", "admitted")]

/-- Rows the Kernel's visitor settles by source reading and no capture measures (`external evidence
pending`): its reference test skips filter bodies, so a `$` read inside a `Having` names `Picks`
without referencing it. The `Sum` leaf then rescues no `And` and fails an `Or`, and the value list
does not iterate at all. -/
private def sourceReadRows : List (String × GroupPath × String × String × String) :=
  let sum := "Sum(Lines*/Qty Having [Lines/Sku] == [$Picks/Ref]) > 0"
  [("f-and", O, "Picks/Ref", s!"FieldNotFilled(Picks/Ref) And {sum}", NEG),
   ("f-or", O, "Picks/Ref", s!"FieldFilled(Picks/Ref) Or {sum}", NEG),
   ("f-list", O, "Picks/Ref",
     "NoFieldValueIncludedInValueList(Lines*/Sku Having [Lines/Code] == [$Picks/Ref] In \"X\")", "admitted")]

/-- The rows this reader answers otherwise, each named by its capture row. -/
private def mismatches : List (String × String × String) :=
  (rows ++ peerRows ++ sourceReadRows).filterMap fun (id, group, errorField, condition, expected) =>
    let actual := verdict group errorField condition
    if actual == expected then none else some (id, expected, actual)

example : mismatches = [] := by native_decide

open Lean in
/-- The error pointers a rule fires at over `Lines` rows of `(LineNo, Qty, Price)`. -/
private def fired (group : GroupPath) (errorField condition : String)
    (lines : List (String × Option String × Option String)) : Option (List String) := do
  let world : World := { now := { epochMillis := 0 } }
  let rows := lines.map fun (no, qty, price) => Json.mkObj ([("LineNo", Json.str no)] ++
    qty.toList.map (("Qty", Json.str ·)) ++ price.toList.map (("Price", Json.str ·)))
  let input ← (readDocument dm (Json.mkObj [("Order", Json.mkObj [("Lines", Json.arr rows.toArray)])])).toOption
  if !input.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  let definition : DmRule :=
    { group, name := "GuardProbe", errorCode := "P", errorEntityRelPath := "../" ++ errorField,
      condition, severity := "ERROR" }
  let rule ← (checkRule dm .english definition).toOption
  pure ((← (runRule world document rule).toOption).map fun message => (observe model message).pointer)

/-- Row sums 5.5, 2 and 6, an empty `Price` contributing nothing: a read of one fixed row would fire
everywhere or nowhere, and a sum across rows (13.5) would fire at every row. -/
private def lines := [("1", some "2", some "3.50"), ("2", some "1", some "1.00"), ("3", some "6", none)]

example : fired O "Lines/Qty" "Sum(Lines/Qty, Lines/Price) > 5" lines =
      some ["Order/Lines/Qty", "Order/Lines[3]/Qty"] ∧
    fired L "Qty" "Sum(Qty, Price) > 5" lines = some ["Order/Lines/Qty", "Order/Lines[3]/Qty"] ∧
    fired O "Lines/Qty" "MaxValue(Lines/Qty, Lines/Price) < 2" lines = some ["Order/Lines[2]/Qty"] ∧
    fired O "Lines/Qty" "NumberOfDifferentValues(Lines/Qty, Lines/Price) > 1" lines =
      some ["Order/Lines/Qty"] := by native_decide

end A12Kernel.Dm.IterationGuardLocks
