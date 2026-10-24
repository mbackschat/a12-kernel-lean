import A12Kernel.Reference.Dm.ParallelValidation
import A12Kernel.Reference.Dm.Document

/-! # Partial calls on a parallel rule whose error field lies below its joined group, through the reader

The [nested-join partial capture](../../../evidence/kernel-30.8.1/captures/nested-join-partial-2026-10-24/)
joins `Lines` and `Picks` by `LineNo` and reports `C1` on `Lines/Parts/Count`, a level below the joined
`Lines`, under eleven relevant sets. The call reaches the rule only when the error field's selectors,
compressed into one, leave the joined `Lines` level wild: one concrete part, two parts of one line and
one whole line select nothing, while two parts of different lines dispatch and then fire only where
`Count` is relevant. A set naming no index field supplies no join key. Full validation is replayed by
`lake exe a12-kernel-replay`; these cases run the partial evaluator.
-/

namespace A12Kernel.Dm.ParallelNestedPartialLocks
open A12Kernel A12Kernel.Dm Lean

private def field (name : String) : Json :=
  Json.mkObj [("type", "Field"), ("name", Json.str name),
    ("Field", Json.mkObj [("fieldType", Json.mkObj [("type", "StringType")])])]

private def group (name : String) (count : Nat) (key : Option String) (elements : List Json) : Json :=
  Json.mkObj [("type", "Group"), ("name", Json.str name), ("Group", Json.mkObj ([
    ("repeatability", toJson count), ("elements", Json.arr elements.toArray)] ++
    key.toList.map fun key => ("indexFieldName", Json.str key)))]

private def order : Json :=
  Json.mkObj [("header", Json.mkObj [("locales", Json.arr #[Json.mkObj [("code", "en_US")]])]),
    ("content", Json.mkObj [("modelConfig", Json.mkObj [("conditionLanguage", Json.mkObj [("code", "en_US")])]),
      ("modelRoot", Json.mkObj [("rootGroups", Json.arr #[group "Order" 1 none [
        group "Lines" 50 (some "LineNo") [field "LineNo", group "Parts" 5 none [field "PartNo", field "Count"]],
        group "Picks" 10 (some "LineNo") [field "LineNo", field "Ref"],
        Json.mkObj [("type", "Rule"), ("name", "C1"), ("Rule", Json.mkObj [
          ("errorEntityRelPath", "../Lines/Parts/Count"), ("errorCode", "C1"), ("severity", "ERROR"),
          ("errorCondition", "FieldFilled(Lines/Parts/Count) And NoFieldFilled(Lines/Parts/PartNo, Picks/Ref)")])]]])])])]

/-- The capture's document: line `A` with two counted parts and a `Picks` row without `Ref`, `B` with a
`Ref`, `C` with two counted parts and no `Picks` row, and a `Picks` row `D` without a line. -/
private def document : Json :=
  let parts := fun (counts : List String) => Json.arr (counts.map fun count => Json.mkObj [("Count", Json.str count)]).toArray
  Json.mkObj [("Order", Json.mkObj [
    ("Lines", Json.arr #[Json.mkObj [("LineNo", "A"), ("Parts", parts ["2", "3"])],
      Json.mkObj [("LineNo", "B"), ("Parts", parts ["4"])], Json.mkObj [("LineNo", "C"), ("Parts", parts ["5", "6"])]]),
    ("Picks", Json.arr #[Json.mkObj [("LineNo", "A")], Json.mkObj [("LineNo", "B"), ("Ref", "r")],
      Json.mkObj [("LineNo", "D"), ("Ref", "r")]])])]

private def every (path : List String) : RelevantEntityPattern := .allInstances path

private def part (line row : Nat) : RelevantEntityPattern :=
  { path := ["Order", "Lines", "Parts", "Count"], indices := [.concrete 1, .concrete line, .concrete row, .concrete 1] }

private def payload : List RelevantEntityPattern :=
  [every ["Order", "Lines", "Parts", "PartNo"], every ["Order", "Picks", "Ref"]]

private def keys : List RelevantEntityPattern :=
  [every ["Order", "Lines", "LineNo"], every ["Order", "Picks", "LineNo"]]

/-- Each fired message as its line and part. -/
private def partialMessages (relevant : List RelevantEntityPattern) : Except String (List (Nat × Nat)) := do
  let dm ← (readModel order).mapError reprStr
  let input ← (readDocument dm document).mapError reprStr
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler dm.flat).mapError reprStr
  let checked ← (checkDocument prepared "en_US" input.data).mapError reprStr
  dm.rules.flatMapM fun rule => do
    let .parallel plan ← (checkValidationRule dm .english rule).mapError (·.detail)
      | throw s!"{rule.errorCode} is not a parallel rule"
    let messages ← runPartialParallelRule checked plan relevant none (some world)
    pure (messages.map fun message => match message.errorAddress.coordinates with
      | [.concrete line, .concrete row] => (line, row)
      | _ => (0, 0))

private def all : List (Nat × Nat) := [(1, 1), (1, 2), (3, 1), (3, 2)]

-- The capture's rows `whole`, `wild`, `lines`, `twoParts`, then the six that select nothing: `payload`,
-- `part11`, `part12`, `part31`, `sameLine`, `line3` and `noRef`.
example :
    ((partialMessages [every ["Order"]]).toOption == some all &&
      (partialMessages ([every ["Order", "Lines", "Parts", "Count"]] ++ payload ++ keys)).toOption == some all &&
      (partialMessages [every ["Order", "Lines"], every ["Order", "Picks"]]).toOption == some all &&
      (partialMessages ([part 1 1, part 3 2] ++ payload ++ keys)).toOption == some [(1, 1), (3, 2)] &&
      [[every ["Order", "Lines", "Parts", "Count"]] ++ payload, [part 1 1] ++ payload ++ keys,
        [part 1 2] ++ payload ++ keys, [part 3 1] ++ payload ++ keys, [part 1 1, part 1 2] ++ payload ++ keys,
        [{ path := ["Order", "Lines"], indices := [.concrete 1, .concrete 3] }, every ["Order", "Picks"]],
        [every ["Order", "Lines", "Parts", "Count"], every ["Order", "Lines", "Parts", "PartNo"]] ++ keys].all
        fun relevant => (partialMessages relevant).toOption == some []) = true := by
  native_decide

end A12Kernel.Dm.ParallelNestedPartialLocks
