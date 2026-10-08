import A12Kernel.Elaboration.NumericComputation
import A12Kernel.Semantics.ComputationSelfValidation

/-! # A fixed group below a starred level on the computation arm of `NumberOfFilledGroups`

The Kernel admits `Batches*/Seal` in a computation alone, beside a fixed group, and twice, and
computes it as the rule arm counts it: one per in-capacity batch whose `Seal` holds content. Two
seeded rounds on both codegen strategies, twelve and eleven documents, are retained at the
[computation checkpoint](../../docs/sources/group-list-and-capacity-probes.md#src-ancestor-starred-group-count-computation), and
this module replays them from elaboration through the addressed evaluator, for the computed values
and for the type of each target's implicit message.

The malformed rows carry the arm's own content. A malformed-only `Seal` counts, as a malformed-only
fixed group does on this arm, while its implicit message disappears. The fixed `Lab` beside `Grading` is
the in-run control that shows the disappearance is not the below-star form's. That it follows from
validation leaving such a group undecided is measured for the fixed form and read off the generated
rule for the below-star one.
-/

namespace A12Kernel.Conformance.AncestorStarredGroupCountComputation

open A12Kernel

private def number : FieldPolicy := { kind := .number { scale := 0, signed := true } }

private def batchesLevel : RepeatableLevel := 10
private def marksLevel : RepeatableLevel := 11

/-- The retained model less its root String `W`, which every document fills and no operand
    reads: `Batches` (max 2) holds its own `Qty` and a fixed `Seal`, which holds a Number, a String
    and a repeatable `Marks` (max 2); `Grading` and `Lab` are fixed, and the four computed targets
    sit in `Out`. -/
private def model : FlatModel :=
  { fields := [
      { id := 1, groupPath := ["Probe", "Grading"], name := "Grade", policy := number },
      { id := 2, groupPath := ["Probe", "Batches"], name := "Qty", policy := number,
        repeatableScope := [batchesLevel] },
      { id := 3, groupPath := ["Probe", "Batches", "Seal"], name := "Code", policy := number,
        repeatableScope := [batchesLevel] },
      { id := 4, groupPath := ["Probe", "Batches", "Seal"], name := "Tag",
        policy := { kind := .string }, repeatableScope := [batchesLevel] },
      { id := 5, groupPath := ["Probe", "Batches", "Seal", "Marks"], name := "Mk",
        policy := { kind := .string }, repeatableScope := [batchesLevel, marksLevel] },
      { id := 6, groupPath := ["Probe", "Lab"], name := "Score", policy := number },
      { id := 7, groupPath := ["Probe", "Out"], name := "SealCnt", policy := number },
      { id := 8, groupPath := ["Probe", "Out"], name := "SealGrd", policy := number },
      { id := 9, groupPath := ["Probe", "Out"], name := "BatCnt", policy := number },
      { id := 10, groupPath := ["Probe", "Out"], name := "LabGrd", policy := number }]
    repeatableGroups := [
      { level := batchesLevel, path := ["Probe", "Batches"], repeatability := some 2 },
      { level := marksLevel, path := ["Probe", "Batches", "Seal", "Marks"],
        repeatability := some 2 }] }

private def fixed (group : String) : SurfaceGroupCountOperand :=
  .fixed (.path { base := .absolute, groups := ["Probe", group] })

private def seals : SurfaceGroupCountOperand :=
  .starred { base := .absolute
             groups := [{ name := "Probe" }, { name := "Batches", starred := true },
               { name := "Seal" }] }

private def batches : SurfaceGroupCountOperand :=
  .starred (.terminallyStarred .absolute ["Probe", "Batches"])

/-- `Batches/Seal` without its star. -/
private def unstarredSeals : SurfaceGroupCountOperand :=
  .fixed (.path { base := .absolute, groups := ["Probe", "Batches", "Seal"] })

/-- The four retained targets in model order: `SealCnt`, `SealGrd`, `BatCnt`, `LabGrd`. -/
private def targets : List (FieldId × List SurfaceGroupCountOperand) :=
  [(7, [seals]), (8, [seals, fixed "Grading"]), (9, [batches]), (10, [fixed "Lab", fixed "Grading"])]

/-- `none` when admitted, otherwise the refusal's projected Kernel class, so an admitted list and
    an unmapped refusal stay apart. -/
private def admissionIn (m : FlatModel) (target : FieldId)
    (operands : List SurfaceGroupCountOperand) : Option (Option KernelStaticDiagnostic) :=
  match elaborateNumericComputationOperation m ["Probe"] target
      (.atom (.filledGroupCount operands)) with
  | .ok _ => none
  | .error error => some (error.groupCountDiagnostic? <|> error.iterationDiagnostic?)

/- Admission, measured through `computation add --dry-run`: the lone form, the form beside a fixed
   group, and the same form twice are admitted, and the unstarred spelling draws `MVK_NO_WILDCARD`
   alone and in a pair. The lone refusal is the one that pins gate order, since the arity class
   would answer there if it ran first. -/
example :
    [admissionIn model 7 [seals], admissionIn model 7 [seals, fixed "Grading"],
      admissionIn model 7 [seals, seals], admissionIn model 7 [unstarredSeals],
      admissionIn model 7 [unstarredSeals, fixed "Grading"]] =
    [none, none, none, some (some .noWildcard), some (some .noWildcard)] := by
  native_decide

private inductive Cell where
  | num (value : Nat)
  | malformed
  | text (value : String)

private def Cell.input (field : FieldId) (path : List Nat) : Cell → ClassifiedCellInput
  | .num value => { address := { field, path }, stored := toString value
                    raw := .parsed (.num value) }
  | .malformed => { address := { field, path }, stored := "bad", raw := .rejected .malformed }
  | .text value => { address := { field, path }, stored := value, raw := .parsed (.str value) }

/-- The computation context over one checked document, reading every cell at its exact address. -/
private def contextOf {m : FlatModel} (document : CheckedDocument m) :
    NumericComputationEvaluationContext :=
  let read (environment : Env) (field : FieldId) : CheckedCell :=
    (document.checkedCellWithRead document.read environment field).toOption.getD
      malformedCheckedCell
  { scalar := { read := read [], world := none }
    document := document.source.toDocument
    outer := []
    filterRead := read
    starRead := read }

/-- `.` is the untyped `.unknown` verdict, which carries no message; `=` an equal seed and `?` a
    missing growth channel, neither of which any retained row reaches. -/
private def messageCode : Option Verdict → Char
  | some (.fired .omission) => 'O'
  | some (.fired .value) => 'V'
  | some .unknown => '.'
  | some .notFired => '='
  | none => '?'

/-- One target's computed value and, against the retained seed `9`, its implicit message type. -/
private def targetReading (m : FlatModel) (context : NumericComputationEvaluationContext)
    (target : FieldId) (operands : List SurfaceGroupCountOperand) : Option (Nat × Char) := do
  let checked ← (elaborateNumericComputationOperation m ["Probe"] target
    (.atom (.filledGroupCount operands))).toOption
  let (atom, checkedOperands) ← match checked.core.expression with
    | .atom atom@(.filledGroupCountMixed checkedOperands) => some (atom, checkedOperands)
    | .atom atom@(.numeric (.filledGroupCount groups)) => some (atom, groups.map .fixed)
    | _ => none
  let computed ← match (context.readCheckedNumericComputationAtom atom).toOption with
    | some (.value amount) => some amount
    | _ => none
  let channels ← (context.growthOfGroupCountOperands m checkedOperands).toOption
  let decided ← (context.groupCountOperandsDecided m checkedOperands).toOption
  pure (computed.floor.toNat,
    messageCode (channels.map (computedNumberSelfValidationIfDecided decided 9 computed ·)))

/-- Every target over one document, or `none` when the document or a target fails. -/
private def readingIn (m : FlatModel) (targets : List (FieldId × List SurfaceGroupCountOperand))
    (rows : List RowAddr) (cells : List (FieldId × List Nat × Cell)) :
    Option (List (Nat × Char)) := do
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler m).toOption
  let document ← (checkDocument prepared "en_US" {
    instantiatedRows := rows
    cells := cells.map fun (field, path, cell) => cell.input field path }).toOption
  targets.mapM fun (target, operands) => targetReading m (contextOf document) target operands

private def reading := readingIn model targets

private def batch (row : Nat) : RowAddr := { group := batchesLevel, path := [row] }

/- The retained table in artifact order, each target as its computed value and message type, `.`
   where the Kernel emits no message. `seals-instantiated-empty` separates the two growth channels:
   both batches exist, so `BatCnt` is at capacity and types VALUE, while `SealCnt` is still OMISSION
   because an empty `Seal` can be filled. `over-limit-only` counts no `Seal` in the third batch, and
   `empty-mark-row` counts one through the row constituent alone. `malformed-beside-valid` keeps its
   message where `malformed-only` loses it, so a formal error does not suppress the message; an
   undecided instance does, and `lab-malformed` shows the fixed form losing it the same way. -/
example :
    [reading [] [],
     reading [batch 1, batch 2] [(3, [1], .num 1), (3, [2], .num 2)],
     reading [batch 1, batch 2] [(3, [1], .num 1), (2, [2], .num 5)],
     reading [batch 1, batch 2] [],
     reading [batch 1] [(3, [1], .malformed)],
     reading [batch 1] [(3, [1], .malformed), (4, [1], .text "t")],
     reading [batch 1, batch 2] [(3, [1], .malformed), (3, [2], .malformed)],
     reading [batch 1, batch 2, batch 3] [(3, [3], .num 3)],
     reading [batch 1] [(1, [], .num 1), (3, [1], .num 1)],
     reading [batch 1, { group := marksLevel, path := [1, 1] }] [],
     reading [] [(6, [], .malformed), (1, [], .num 1)],
     reading [batch 1] [(6, [], .malformed), (1, [], .num 1), (3, [1], .malformed)]] =
    [some [(0, 'O'), (0, 'O'), (0, 'O'), (0, 'O')],
     some [(2, 'V'), (2, 'O'), (2, 'V'), (0, 'O')],
     some [(1, 'O'), (1, 'O'), (2, 'V'), (0, 'O')],
     some [(0, 'O'), (0, 'O'), (2, 'V'), (0, 'O')],
     some [(1, '.'), (1, '.'), (1, 'O'), (0, 'O')],
     some [(1, 'O'), (1, 'O'), (1, 'O'), (0, 'O')],
     some [(2, '.'), (2, '.'), (2, 'V'), (0, 'O')],
     some [(0, 'O'), (0, 'O'), (2, 'V'), (0, 'O')],
     some [(1, 'O'), (2, 'O'), (1, 'O'), (1, 'O')],
     some [(1, 'O'), (1, 'O'), (1, 'O'), (0, 'O')],
     some [(0, 'O'), (1, 'O'), (0, 'O'), (2, '.')],
     some [(1, '.'), (2, '.'), (1, 'O'), (2, '.')]] := by
  native_decide

/-! ## Separators and wider shapes

A second seeded run on its own model, retained at the same
[computation checkpoint](../../docs/sources/group-list-and-capacity-probes.md#src-ancestor-starred-group-count-computation): one
filled beside one malformed-only `Seal`, a malformed-only `Seal` in an over-limit batch, the form
twice, a disjoint terminal star beside it, and a fixed group below two reopened levels. -/

private def boxesLevel : RepeatableLevel := 11
private def cratesLevel : RepeatableLevel := 12

/-- The second retained model less its root String `W`: `Batches` (max 2) holds `Qty`, a fixed
    `Seal`, and a repeatable `Boxes` (max 2) holding a fixed `BSeal`; `Crates` (max 2) is a
    disjoint repeatable group. -/
private def separatorModel : FlatModel :=
  { fields := [
      { id := 2, groupPath := ["Probe", "Batches"], name := "Qty", policy := number,
        repeatableScope := [batchesLevel] },
      { id := 3, groupPath := ["Probe", "Batches", "Seal"], name := "Code", policy := number,
        repeatableScope := [batchesLevel] },
      { id := 4, groupPath := ["Probe", "Batches", "Seal"], name := "Tag",
        policy := { kind := .string }, repeatableScope := [batchesLevel] },
      { id := 5, groupPath := ["Probe", "Batches", "Boxes", "BSeal"], name := "BCode",
        policy := number, repeatableScope := [batchesLevel, boxesLevel] },
      { id := 6, groupPath := ["Probe", "Crates"], name := "Ck", policy := number,
        repeatableScope := [cratesLevel] },
      { id := 7, groupPath := ["Probe", "Out"], name := "SealCnt", policy := number },
      { id := 8, groupPath := ["Probe", "Out"], name := "SealTwice", policy := number },
      { id := 9, groupPath := ["Probe", "Out"], name := "MixCnt", policy := number },
      { id := 10, groupPath := ["Probe", "Out"], name := "BoxCnt", policy := number }]
    repeatableGroups := [
      { level := batchesLevel, path := ["Probe", "Batches"], repeatability := some 2 },
      { level := boxesLevel, path := ["Probe", "Batches", "Boxes"], repeatability := some 2 },
      { level := cratesLevel, path := ["Probe", "Crates"], repeatability := some 2 }] }

private def crates (starred : Bool) : SurfaceGroupCountOperand :=
  if starred then .starred (.terminallyStarred .absolute ["Probe", "Crates"])
  else .fixed (.path { base := .absolute, groups := ["Probe", "Crates"] })

private def boxSeals (outer inner : Bool) : SurfaceGroupCountOperand :=
  .starred { base := .absolute
             groups := [{ name := "Probe" }, { name := "Batches", starred := outer },
               { name := "Boxes", starred := inner }, { name := "BSeal" }] }

/- The second admission batch: the disjoint star beside the below-star form and the two-level form
   are admitted, and unstarring `Crates` or either level of the two-level path draws
   `MVK_NO_WILDCARD`. The inner level answers through the star plan and the outer one through the
   per-row operand gate, whose carrier matrix
   [`StarBinding`](NumericComputation/StarBinding.lean) owns. -/
example :
    [admissionIn separatorModel 7 [crates true, seals],
      admissionIn separatorModel 7 [crates false, seals],
      admissionIn separatorModel 7 [boxSeals true true],
      admissionIn separatorModel 7 [boxSeals true false],
      admissionIn separatorModel 7 [boxSeals false true]] =
    [none, some (some .noWildcard), none, some (some .noWildcard), some (some .noWildcard)] := by
  native_decide

/-- `SealCnt`, `SealTwice`, `MixCnt` and `BoxCnt`, in model order. -/
private def separatorTargets : List (FieldId × List SurfaceGroupCountOperand) :=
  [(7, [seals]), (8, [seals, seals]), (9, [crates true, seals]), (10, [boxSeals true true])]

private def separatorReading := readingIn separatorModel separatorTargets

private def crate (row : Nat) : RowAddr := { group := cratesLevel, path := [row] }
private def box (outer inner : Nat) : RowAddr := { group := boxesLevel, path := [outer, inner] }

/- The second table. One filled beside one malformed-only `Seal` counts two with no message, so a
   single undecided instance decides the operand rather than all of them, and a malformed-only
   `Seal` in an over-limit batch neither counts nor suppresses. The form twice doubles value and
   extent, the disjoint star adds its rows, and the two-level form moves against the product of both
   maxima: at capacity with every `BSeal` empty it still types OMISSION. -/
example :
    [separatorReading [] [],
     separatorReading [batch 1, batch 2] [(3, [1], .num 1), (3, [2], .malformed)],
     separatorReading [batch 1, batch 2, batch 3] [(3, [3], .malformed)],
     separatorReading [batch 1, batch 2] [(3, [1], .num 1), (3, [2], .num 2)],
     separatorReading [crate 1, crate 2, batch 1] [(6, [1], .num 1), (3, [1], .num 1)],
     separatorReading [crate 1, crate 2, batch 1, batch 2] [(3, [1], .num 1), (3, [2], .num 2)],
     separatorReading [batch 1, box 1 1, box 1 2, batch 2, box 2 1]
       [(5, [1, 1], .num 1), (5, [2, 1], .num 2)],
     separatorReading [batch 1, box 1 1, box 1 2, batch 2, box 2 1, box 2 2]
       [(5, [1, 1], .num 1), (5, [1, 2], .num 2), (5, [2, 1], .num 3), (5, [2, 2], .num 4)],
     separatorReading [batch 1, box 1 1, box 1 2, box 1 3] [(5, [1, 3], .num 3)],
     separatorReading [batch 1, box 1 1] [(5, [1, 1], .malformed)],
     separatorReading [batch 1, box 1 1, box 1 2, batch 2, box 2 1, box 2 2] []] =
    [some [(0, 'O'), (0, 'O'), (0, 'O'), (0, 'O')],
     some [(2, '.'), (4, '.'), (2, '.'), (0, 'O')],
     some [(0, 'O'), (0, 'O'), (0, 'O'), (0, 'O')],
     some [(2, 'V'), (4, 'V'), (2, 'O'), (0, 'O')],
     some [(1, 'O'), (2, 'O'), (3, 'O'), (0, 'O')],
     some [(2, 'V'), (4, 'V'), (4, 'V'), (0, 'O')],
     some [(0, 'O'), (0, 'O'), (0, 'O'), (2, 'O')],
     some [(0, 'O'), (0, 'O'), (0, 'O'), (4, 'V')],
     some [(0, 'O'), (0, 'O'), (0, 'O'), (0, 'O')],
     some [(0, 'O'), (0, 'O'), (0, 'O'), (1, '.')],
     some [(0, 'O'), (0, 'O'), (0, 'O'), (0, 'O')]] := by
  native_decide

end A12Kernel.Conformance.AncestorStarredGroupCountComputation
