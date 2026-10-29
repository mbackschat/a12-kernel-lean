import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.ParallelValidation
import A12Kernel.Reference.Dm.EntryFrameFixture

/-! # Partial dispatch of ordinary rules over two repeatable levels, through the reader

The [ordinary partial dispatch capture](../../../evidence/kernel-30.8.1/captures/ordinary-partial-dispatch-2026-10-24/)
reports five ordinary rules on `Lines/Parts/Count` under six relevant sets. A rule runs at a part only
when the error field's selectors, compressed into one with every differing coordinate made a
wildcard, matches that part's line and part: two parts of different lines run every part, two parts of
one line run that line's parts, and a starred level runs every row there. `O1` and `O4` read a leaf
that a run decides without the part's own `Count`, so they fire on parts the selectors do not name,
while `O6`, reading only `Count`, fires only on named parts. `O2` and `O3` read `CurrentRepetition`
of the outer and of the inner level. Full validation is replayed by `lake exe a12-kernel-replay`;
these cases run the partial evaluator.
-/

namespace A12Kernel.Dm.OrdinaryPartialCompressionLocks
open A12Kernel A12Kernel.Dm Lean

private def field (name : String) (number : Bool := false) : Json :=
  Json.mkObj [("type", "Field"), ("name", Json.str name), ("Field", Json.mkObj [("fieldType",
    if number then Json.mkObj [("type", "NumberType"), ("NumberType", Json.mkObj [("maxFractionalDigits", toJson (0 : Nat))])]
    else Json.mkObj [("type", "StringType")])])]

private def group (name : String) (count : Nat) (elements : List Json) : Json :=
  Json.mkObj [("type", "Group"), ("name", Json.str name), ("Group", Json.mkObj [
    ("repeatability", toJson count), ("elements", Json.arr elements.toArray)])]

private def rule (code condition : String) : Json :=
  Json.mkObj [("type", "Rule"), ("name", Json.str code), ("Rule", Json.mkObj [
    ("errorEntityRelPath", "../Lines/Parts/Count"), ("errorCode", Json.str code), ("severity", "ERROR"),
    ("errorCondition", Json.str condition)])]

/-- The capture's rules `O1`–`O4` and `O6`, in its declaration order. -/
private def order : Json :=
  checkedEntryFrame <| Json.mkObj [("header", Json.mkObj [("locales", Json.arr #[Json.mkObj [("code", "en_US")]])]),
    ("content", Json.mkObj [("modelConfig", Json.mkObj [("conditionLanguage", Json.mkObj [("code", "en_US")])]),
      ("modelRoot", Json.mkObj [("rootGroups", Json.arr #[group "Order" 1 [
        field "Email", group "Lines" 50 [field "Code", group "Parts" 5 [field "Count" true, field "Tag"]],
        rule "O1" "FieldFilled(Lines/Parts/Tag) And (FieldFilled(Email) Or FieldFilled(Lines/Parts/Count))",
        rule "O2" "FieldFilled(Lines/Parts/Count) And CurrentRepetition(Lines) > 1",
        rule "O3" "FieldFilled(Lines/Parts/Count) And CurrentRepetition(Lines/Parts) > 1",
        rule "O4" "FieldFilled(Lines/Parts/Tag) And (CurrentRepetition(Lines) > 2 Or FieldFilled(Lines/Parts/Count))",
        rule "O6" "FieldFilled(Lines/Parts/Count)"]])])])]

/-- The capture's document: line one holds two counted parts and a third holding only `Tag`, line two
one counted part and line three two; every part holds `Tag`. -/
private def document : Json :=
  let part := fun (count : Option String) => Json.mkObj ((count.toList.map fun count => ("Count", Json.str count)) ++ [("Tag", Json.str "t")])
  let line := fun (parts : List (Option String)) => Json.mkObj [("Code", "c"), ("Parts", Json.arr (parts.map part).toArray)]
  Json.mkObj [("Order", Json.mkObj [("Email", "e"), ("Lines", Json.arr #[
    line [some "2", some "3", none], line [some "4"], line [some "5", some "6"]])])]

private def count (line part : RelevanceIndex) : RelevantEntityPattern :=
  { path := ["Order", "Lines", "Parts", "Count"], indices := [.concrete 1, line, part, .concrete 1] }

private def tags : List RelevantEntityPattern := [.allInstances ["Order", "Lines", "Parts", "Tag"]]

private def email : RelevantEntityPattern := .allInstances ["Order", "Email"]

/-- Each fired message as its code, line and part. -/
private def partialMessages (relevant : List RelevantEntityPattern) : Except String (List (String × Nat × Nat)) := do
  let dm ← (readModel order).mapError reprStr
  let input ← (readDocument dm document).mapError reprStr
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler dm.flat).mapError reprStr
  let checked ← (checkDocument prepared "en_US" input.data).mapError reprStr
  dm.rules.flatMapM fun rule => do
    let .ordinary checkedRule ← (checkValidationRule dm .english rule).mapError (·.detail)
      | throw s!"{rule.errorCode} is not an ordinary rule"
    let .rows _ := checkedRule.ordinaryIterationPlan | throw s!"{rule.errorCode} does not iterate rows"
    let outcome ← (checkedRule.evalOrdinaryRepeatablePartial checked (.partialSet relevant) (some world)).mapError reprStr
    let messages : List FlatRuleMessage := match outcome with
      | .skipped => []
      | .evaluated rows => rows.filterMap fun
        | (_, .evaluated outcome) => outcome.message?
        | (_, .skipped) => none
    pure (messages.map fun message => (rule.errorCode, match message.errorAddress.coordinates with
      | [.concrete line, .concrete part] => (line, part)
      | _ => (0, 0)))

-- The capture's rows `twoParts`, `threeNoEmail`, `sameLine`, `part2star`, `line2star` and `emailOnly`.
example :
    ((partialMessages ([count (.concrete 1) (.concrete 1), count (.concrete 3) (.concrete 2), email] ++ tags)).toOption ==
        some [("O1", 1, 1), ("O1", 1, 2), ("O1", 1, 3), ("O1", 2, 1), ("O1", 3, 1), ("O1", 3, 2), ("O2", 3, 2),
          ("O3", 3, 2), ("O4", 1, 1), ("O4", 3, 1), ("O4", 3, 2), ("O6", 1, 1), ("O6", 3, 2)] &&
      (partialMessages ([count (.concrete 1) (.concrete 2), count (.concrete 2) (.concrete 1),
          count (.concrete 3) (.concrete 2)] ++ tags)).toOption ==
        some [("O1", 1, 2), ("O1", 2, 1), ("O1", 3, 2), ("O2", 2, 1), ("O2", 3, 2), ("O3", 1, 2), ("O3", 3, 2),
          ("O4", 1, 2), ("O4", 2, 1), ("O4", 3, 1), ("O4", 3, 2), ("O6", 1, 2), ("O6", 2, 1), ("O6", 3, 2)] &&
      (partialMessages ([count (.concrete 1) (.concrete 1), count (.concrete 1) (.concrete 2), email] ++ tags)).toOption ==
        some [("O1", 1, 1), ("O1", 1, 2), ("O1", 1, 3), ("O3", 1, 2), ("O4", 1, 1), ("O4", 1, 2), ("O6", 1, 1),
          ("O6", 1, 2)] &&
      (partialMessages ([count .all (.concrete 2), email] ++ tags)).toOption ==
        some [("O1", 1, 2), ("O1", 3, 2), ("O2", 3, 2), ("O3", 1, 2), ("O3", 3, 2), ("O4", 1, 2), ("O4", 3, 2),
          ("O6", 1, 2), ("O6", 3, 2)] &&
      (partialMessages ([count (.concrete 2) .all, email] ++ tags)).toOption ==
        some [("O1", 2, 1), ("O2", 2, 1), ("O4", 2, 1), ("O6", 2, 1)] &&
      (partialMessages ([email] ++ tags)).toOption == some []) = true := by
  native_decide

end A12Kernel.Dm.OrdinaryPartialCompressionLocks
