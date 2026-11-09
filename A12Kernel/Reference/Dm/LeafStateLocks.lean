import Lean.Data.Json
import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.Validate
import A12Kernel.Reference.Dm.Replay

/-! # The cell states of the scalar kinds and the leaf verdicts over them

Each admitted condition leaf over a Number, Boolean, Confirm, Enumeration or String field without a
pattern, read against an absent, an empty, a not-check-relevant and a filled cell. The verdict
follows the leaf's spec/14 cells V (unavailable read), N (empty read), B (content gate) and T (traversal) with the
consumer classes of spec/02 §B.2. A case observes one bit, whether the rule fires: `And` and `Or` are
strong-Kleene and the language has no negation (spec/02 §A.1, §A.2), so a leaf's UNKNOWN and FALSE
compose identically and no rule observes the difference. The matrix is the Q2-P2 acceptance set of
[the plan](../../../docs/PLAN.md#q2-preparation-checklist).

Which nonempty values are filled rather than not check-relevant is each kind's admitted set, locked
in [the formal-domain locks](FormalDomainLocks.lean) (Q2-P3). Bounded repetition (Q2-P5) closes the
module; the acceptance relations (Q2-P4) are locked against
retained Kernel rows in [the control locks](AcceptedSampleControlLocks.lean). -/

namespace A12Kernel.Dm.LeafStateLocks

open Lean

private def form : GroupPath := ["Form"]
private def rows : GroupPath := ["Form", "Rows"]

private def model : FlatModel := {
  fields := [
    { id := 1, name := "Anchor", groupPath := form, policy.kind := .number { scale := 0, signed := true } },
    { id := 2, name := "N", groupPath := form, policy.kind := .number { scale := 0, signed := true } },
    { id := 3, name := "M", groupPath := form, policy.kind := .number { scale := 0, signed := true } },
    { id := 4, name := "B", groupPath := form, policy.kind := .boolean },
    { id := 5, name := "C", groupPath := form, policy.kind := .confirm },
    { id := 6, name := "E", groupPath := form, policy.kind := .enumeration,
      enumeration := some { storedTokens := ["A", "Z"], categories := [{ name := "Band", tokens := ["Lo", "Hi"] }] } },
    { id := 7, name := "S", groupPath := form, policy.kind := .string, stringPolicy := { maxLength := some 3 } },
    { id := 8, name := "T", groupPath := form, policy.kind := .string, stringPolicy := { maxLength := some 3 } },
    { id := 9, name := "GX", groupPath := ["Form", "G"], policy.kind := .number { scale := 0, signed := true } },
    { id := 10, name := "RN", groupPath := rows, repeatableScope := [10],
      policy.kind := .number { scale := 0, signed := true } },
    { id := 11, name := "RS", groupPath := rows, repeatableScope := [10], policy.kind := .string,
      stringPolicy := { maxLength := some 3 } },
    { id := 12, name := "WN", groupPath := ["Form", "Wide"], repeatableScope := [11],
      policy.kind := .number { scale := 0, signed := true } },
    { id := 13, name := "D", groupPath := form, policy.kind := .number { scale := 2, signed := true } }]
  repeatableGroups := [{ level := 10, path := rows, repeatability := some 3 },
    { level := 11, path := ["Form", "Wide"], repeatability := some 6 }] }

private def world : World := { now := { epochMillis := 0 } }

/-- A cell's authored state. `absent` writes no member; `empty` writes the empty text, the
present-empty placement; `invalid` writes a text the field's formal check refuses. -/
private inductive Cell where
  | absent
  | empty
  | invalid
  | value (text : String)

private def Cell.member (name : String) : Cell → Option (String × Json)
  | .absent => none
  | .empty => some (name, .str "")
  | .invalid => some (name, .str (if name == "S" || name == "T" || name == "RS" then "abcd" else "x"))
  | .value text => some (name, .str text)

/-- A root `Form` holding `Anchor = 1`, the named root cells, an optional `G` instance and the
`Rows` and `Wide` rows, each a list of named cells. -/
private def document (cells : List (String × Cell)) (group : List (String × Cell) := [])
    (rowCells : List (List (String × Cell)) := []) (wideCells : List (List (String × Cell)) := []) : Json :=
  let members := fun (named : List (String × Cell)) => named.filterMap fun (name, cell) => cell.member name
  let rowsOf := fun (name : String) (shape : List (List (String × Cell))) =>
    if shape.isEmpty then [] else [(name, Json.arr (shape.map (Json.mkObj ∘ members)).toArray)]
  let root := [("Anchor", Json.str "1")] ++ members cells
    ++ (if group.isEmpty then [] else [("G", Json.mkObj (members group))])
    ++ rowsOf "Rows" rowCells ++ rowsOf "Wide" wideCells
  Json.mkObj [("Form", Json.mkObj root)]

/-- How many messages the rule `FieldFilled(Anchor) And condition`, reporting on `Anchor` from `Form`,
fires over `doc`; `none` when the model check refuses the rule or the document does not read. The rule must
reference its error field (`MVK_ERROR_FIELD_NOT_REFERENCED`), and `Anchor` is always filled, so the
prefix is TRUE and the leaf alone decides. A `target` instead reports on that path with the bare
`condition`, for a leaf that must bind the target's repeatable level. -/
private def messageCount (condition : String) (doc : Json) (target : Option String := none) : Option Nat := do
  let dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let input ← (readDocument dm doc).toOption
  if !input.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let validated ← checked.fullValidationDocument.toOption
  let (path, text) := match target with
    | none => ("Anchor", s!"FieldFilled(Anchor) And {condition}")
    | some path => (path, condition)
  let rule : DmRule :=
    { group := form, name := "P", errorCode := "P", errorEntityRelPath := "../" ++ path, condition := text
      severity := "ERROR" }
  let checkedRule ← (checkValidationRule dm .english rule world).toOption
  let messages ← (runValidationRule world validated checkedRule).toOption
  pure messages.length

private def fires (condition : String) (doc : Json) (target : Option String := none) : Option Bool :=
  (messageCount condition doc target).map (· > 0)

/-- The four states of one root cell, in the order absent, empty, not-check-relevant, filled. -/
private def overStates (condition field filled : String) : List (Option Bool) :=
  [Cell.absent, .empty, .invalid, .value filled].map fun cell => fires condition (document [(field, cell)])

/-- Two root cells `N` and `M` in each listed pair of states. -/
private def overPairs (condition : String) (pairs : List (Cell × Cell)) : List (Option Bool) :=
  pairs.map fun (n, m) => fires condition (document [("N", n), ("M", m)])

/-- `Rows` rows, each one `field` cell. -/
private def overRows (condition field : String) (shapes : List (List Cell)) : List (Option Bool) :=
  shapes.map fun cells => fires condition (document [] [] (cells.map fun cell => [(field, cell)]))

private def filled : Cell := .value "5"

/-! ## Presence predicates: `presence/fill`, an unavailable cell is neither filled nor empty -/

example : overStates "FieldFilled(N)" "N" "5" = [some false, some false, some false, some true] := by
  native_decide

example : overStates "FieldNotFilled(N)" "N" "5" = [some true, some true, some false, some false] := by
  native_decide

/-- The not-check-relevant state reaches every admitted kind: a filled cell fires `FieldFilled`, an
invalid one fires neither presence predicate. -/
example : [("B", "true"), ("C", "true"), ("E", "A"), ("S", "ab")].all (fun (field, text) =>
    overStates s!"FieldFilled({field})" field text == [some false, some false, some false, some true] &&
    overStates s!"FieldNotFilled({field})" field text == [some true, some true, some false, some false]) := by
  native_decide

/-! ## Field-fill quantifiers over `(N, M)`: a known member settles, an unavailable one never does

The pairs are filled–invalid, empty–invalid, filled–filled, empty–empty and filled–empty. -/

private def fillPairs : List (Cell × Cell) :=
  [(filled, .invalid), (.empty, .invalid), (filled, filled), (.empty, .empty), (filled, .empty)]

example : overPairs "AllFieldsFilled(N, M)" fillPairs =
    [some false, some false, some true, some false, some false] := by native_decide
example : overPairs "NoFieldFilled(N, M)" fillPairs =
    [some false, some false, some false, some true, some false] := by native_decide
example : overPairs "AtLeastOneFieldFilled(N, M)" fillPairs =
    [some true, some false, some true, some false, some true] := by native_decide
example : overPairs "MoreThanOneFieldFilled(N, M)" fillPairs =
    [some false, some false, some true, some false, some false] := by native_decide
example : overPairs "NotAllFieldsFilled(N, M)" fillPairs =
    [some false, some true, some false, some true, some true] := by native_decide
example : overPairs "NotExactlyOneFieldFilled(N, M)" fillPairs =
    [some false, some false, some true, some true, some false] := by native_decide
example : overPairs "FieldsNotCollectivelyFilled(N, M)" fillPairs =
    [some false, some false, some false, some false, some true] := by native_decide

/-- Column T over `Rows*`, declaring 3 slots: a `declared` scan reads the two missing slots as empty, an
`instantiated` one sees only the one filled row, and `FieldsNotCollectivelyFilled` asks the first and
then the second. Three filled rows are the control. -/
example : [("AllFieldsFilled(Rows*/RN)", [some false, some true]),
      ("NotAllFieldsFilled(Rows*/RN)", [some true, some false]),
      ("FieldsNotCollectivelyFilled(Rows*/RN)", [some true, some false]),
      ("NoFieldFilled(Rows*/RN)", [some false, some false]),
      ("AtLeastOneFieldFilled(Rows*/RN)", [some true, some true])].all (fun (condition, expected) =>
        overRows condition "RN" [[filled], [filled, filled, filled]] == expected) ∧
    overRows "NoFieldFilled(Rows*/RN)" "RN" [[], [.empty]] = [some true, some true] := by native_decide

/-! ## Comparisons: `scalar read` with each kind's empty default -/

/-- Number and Confirm substitute `0` and `False`; Boolean, Enumeration and String leave the
comparison unevaluated. -/
example : overStates "[N] < 5" "N" "3" = [some true, some true, some false, some true] ∧
    overStates "[C] != True" "C" "true" = [some true, some true, some false, some false] ∧
    overStates "[B] == False" "B" "false" = [some false, some false, some false, some true] ∧
    overStates "[E] != \"A\"" "E" "Z" = [some false, some false, some false, some true] ∧
    overStates "[S] != \"a\"" "S" "b" = [some false, some false, some false, some true] := by native_decide

/-- The ordering comparisons share the Number default; each threshold is chosen so that the empty
reading `0` fires and an unavailable cell does not. -/
example : overStates "[N] <= 0" "N" "5" = [some true, some true, some false, some false] ∧
    overStates "[N] >= 0" "N" "-1" = [some true, some true, some false, some false] ∧
    overStates "[N] > -1" "N" "-1" = [some true, some true, some false, some false] := by native_decide

/-- `+`, `-` and `*` read an empty operand as `0` and an unavailable one as unavailable. -/
example : [("[N] + [M] == 5", [some true, some false, some false]),
      ("[N] - [M] == -5", [some true, some false, some false]),
      ("[N] * [M] == 0", [some true, some false, some false])].all (fun (condition, expected) =>
        overPairs condition [(.empty, filled), (.invalid, filled), (filled, filled)] == expected) := by
  native_decide

/-- `Or` is strong-Kleene: an unavailable part beside a TRUE one fires, beside a FALSE one does not. -/
example : overPairs "([N] == 5 Or [M] == 5)" [(.invalid, filled), (.invalid, .value "1"), (.value "1", .value "1")] =
    [some true, some false, some false] := by native_decide

/-- An operand read through arithmetic keeps the Number default. -/
example : overStates "Abs([N]) == 0" "N" "5" = [some true, some true, some false, some false] := by
  native_decide

/-- The tolerance comparisons read an empty side as `0` and fire strictly outside the band, each at its
own threshold (spec/04 §4.6): a difference of exactly the threshold does not fire. -/
example : overPairs "[N] DiffersWithToleranceRange1 [M]" [(filled, .empty), (filled, .invalid), (.value "1", .empty)] =
      [some true, some false, some false] ∧
    overPairs "[N] DiffersWithToleranceRange2 [M]" [(.value "2", .empty), (.value "3", .empty), (filled, .invalid)] =
      [some false, some true, some false] ∧
    overPairs "[N] DiffersWithToleranceRange5 [M]" [(.value "5", .empty), (.value "6", .empty)] =
      [some false, some true] ∧
    overPairs "[N] DiffersWithToleranceRange10 [M]" [(.value "10", .empty), (.value "11", .empty)] =
      [some false, some true] := by native_decide

/-- Rounding, `RangeAsNumber` and the operand-list extrema keep the Number default; an empty `RangeAsNumber`
source reads a fillable `0`. -/
example : ["RoundDown([N]) == 0", "RoundUp([N]) == 0", "RoundAccounting([N]) == 0"].all (fun condition =>
      overStates condition "N" "5" == [some true, some true, some false, some false]) ∧
    overStates "RangeAsNumber(S, 1, 2) == 0" "S" "12" = [some true, some true, some false, some false] ∧
    overPairs "Min([N], [M]) == 0" [(.empty, filled), (.invalid, filled), (filled, filled)] =
      [some true, some false, some false] ∧
    overPairs "Max([N], [M]) == 0" [(.empty, .value "-3"), (.invalid, .value "-3"), (.value "-5", .value "-3")] =
      [some true, some false, some false] := by native_decide

/-- On the scale-2 `D` the roundings take their direction (spec/04 §4): `RoundDown` toward −∞, `RoundUp`
toward +∞, `RoundAccounting` to the nearest with ties away from zero; an empty `D` rounds its `0`. -/
example : [("RoundDown([D]) == 1", "1.99"), ("RoundDown([D]) == -2", "-1.5"), ("RoundUp([D]) == 2", "1.01"),
      ("RoundUp([D]) == -1", "-1.5"), ("RoundAccounting([D]) == 3", "2.5"), ("RoundAccounting([D]) == -3", "-2.5"),
      ("RoundAccounting([D]) == 2", "2.49")].map (fun (condition, value) =>
        fires condition (document [("D", .value value)])) = List.replicate 7 (some true) ∧
    fires "RoundDown([D]) == 0" (document [("D", .empty)]) = some true := by native_decide

/-- A reached division-by-zero or invalid-power domain failure makes the comparison not fire under either
polarity (spec/04 §3), through a `RoundAccounting` wrapper the scale gate requires; each nonzero twin fires.
-/
example : overPairs "RoundAccounting([N] / [M], 0) == 0" [(.value "0", .value "0"), (.value "0", filled)] =
      [some false, some true] ∧
    overPairs "RoundAccounting([N] / [M], 0) != 0" [(filled, .value "0"), (filled, .value "1")] =
      [some false, some true] ∧
    ["RoundAccounting([N] ^ -1, 0) == 0", "RoundAccounting([N] ^ -1, 0) != 0"].map
        (fun condition => fires condition (document [("N", .value "0")])) = [some false, some false] ∧
    fires "RoundAccounting([N] ^ -1, 0) != 0" (document [("N", .value "1")]) = some true := by native_decide

/-- A category read inherits the Enumeration cell's state: empty is not evaluated, invalid unavailable. -/
example : overStates "[E -> Band] == \"Hi\"" "E" "Z" = [some false, some false, some false, some true] ∧
    overStates "[E -> Band] != \"Hi\"" "E" "A" = [some false, some false, some false, some true] := by
  native_decide

/-! ## Value-list predicates over the Enumeration `E` and the literal `"A"` -/

example : overStates "FieldValueIncludedInValueList(E, \"A\")" "E" "A" =
      [some false, some false, some false, some true] ∧
    overStates "FieldValueNotIncludedInValueList(E, \"A\")" "E" "Z" =
      [some false, some false, some false, some true] ∧
    overStates "AtLeastOneFieldValueIncludedInValueList(E In \"A\")" "E" "A" =
      [some false, some false, some false, some true] ∧
    overStates "NoFieldValueIncludedInValueList(E In \"A\")" "E" "Z" =
      [some true, some true, some false, some true] ∧
    overStates "NotAllFieldValuesIncludedInValueList(E In \"A\")" "E" "Z" =
      [some false, some false, some false, some true] := by native_decide

/-- Over two subject fields `S, T` the quantifiers treat an unavailable field cell differently (spec/06
§B.3): `No` is suppressed by one reached before any match, `AtLeastOne` and `NotAll`'s restarted scan skip
it. Each outside-value or match twin fires. -/
example : [("NoFieldValueIncludedInValueList(S, T In \"a\")", Cell.invalid, Cell.value "b", false),
      ("NoFieldValueIncludedInValueList(S, T In \"a\")", .value "b", .value "c", true),
      ("AtLeastOneFieldValueIncludedInValueList(S, T In \"a\")", .invalid, .value "a", true),
      ("AtLeastOneFieldValueIncludedInValueList(S, T In \"a\")", .invalid, .value "b", false),
      ("NotAllFieldValuesIncludedInValueList(S, T In \"a\")", .invalid, .value "b", true),
      ("NotAllFieldValuesIncludedInValueList(S, T In \"a\")", .invalid, .value "a", false)].all
        (fun (condition, s, t, expected) => fires condition (document [("S", s), ("T", t)]) == some expected) := by
  native_decide

/-- A match ends `No` without firing; the filled control above shows an outside value fires it. -/
example : overStates "NoFieldValueIncludedInValueList(E In \"A\")" "E" "A" =
    [some true, some true, some false, some false] := by native_decide

/-! ## Counts over `(N, M)`: `all-cells`, one unavailable member makes the count unavailable -/

example : overPairs "NumberOfFilledFields(N, M) == 1" [(filled, .empty), (filled, .invalid), (.empty, .invalid)] =
      [some true, some false, some false] ∧
    overPairs "NumberOfDifferentValues(N, M) == 1" [(filled, filled), (filled, .empty), (filled, .invalid)] =
      [some true, some true, some false] ∧
    overPairs "NumberOfValueInFields(5 In N, M) == 1" [(filled, .empty), (filled, .invalid)] =
      [some true, some false] ∧
    overPairs "NumberOfValueInFields(0 In N, M) == 0" [(.empty, filled), (.value "0", filled)] =
      [some true, some false] := by native_decide

/-! ## Aggregates over `Rows*/RN`: empties are skipped, an unavailable cell decides by its class -/

private def numberRows : List (List Cell) :=
  [[.value "1", .empty, .value "2"], [.value "1", .invalid, .value "2"]]

example : overRows "Sum(Rows*/RN) == 3" "RN" numberRows = [some true, some false] ∧
    overRows "MaxValue(Rows*/RN) == 2" "RN" numberRows = [some true, some false] ∧
    overRows "MinValue(Rows*/RN) == 1" "RN" numberRows = [some true, some false] := by native_decide

/-- `MaxValue` skips an empty row rather than folding it as `0`, which negative rows separate. -/
example : overRows "MaxValue(Rows*/RN) == -1" "RN" [[.value "-3", .empty, .value "-1"], [.value "-3", .invalid, .value "-1"]] =
    [some true, some false] := by native_decide

/-- `SumOfTerms` adds its term over every instantiated row, an empty read as `0`; an unavailable read
makes it unavailable, and over no row it is `0` (spec/07). -/
example : overRows "SumOfTerms(Rows*, [Rows/RN]) == 3" "RN" numberRows = [some true, some false] ∧
    overRows "SumOfTerms(Rows*, [Rows/RN]) == 0" "RN" [[]] = [some true] := by native_decide

/-- A `Having` filter keeps a row only when it is known true (spec/07): the row whose filter reads an
unavailable `RS` is dropped, from a `Sum` and from `NoFieldFilled` alike; the control keeps it. -/
example : fires "Sum(Rows*/RN Having [Rows/RS] == \"a\") == 3"
      (document [] [] [[("RN", .value "3"), ("RS", .value "a")], [("RN", .value "5"), ("RS", .value "b")],
        [("RN", .value "7"), ("RS", .invalid)]]) = some true ∧
    [Cell.invalid, .value "a"].map (fun tag => fires "NoFieldFilled(Rows*/RN Having [Rows/RS] == \"a\")"
      (document [] [] [[("RN", .empty), ("RS", .value "a")], [("RN", filled), ("RS", tag)]])) =
      [some true, some false] := by native_decide

/-- `stop-at-first`: an unavailable cell decides only in the first-filled position. -/
example : overRows "FirstFilledValue(Rows*/RN) == 2" "RN"
      [[.empty, .value "2", .invalid], [.invalid, .value "2"]] = [some true, some false] := by
  native_decide

/-- `skip-invalid`: an unavailable member is skipped like an empty one. -/
example : overRows "FieldValuesNotUnique(Rows*/RS)" "RS"
      [[.value "a", .value "a", .invalid], [.value "a", .invalid], [.value "a", .empty, .empty]] =
    [some true, some false, some false] := by native_decide

/-- `row drop`: an invalid key drops its own row, an all-empty key row is skipped, and the duplicate
among the remaining rows still fires. The rule reports on the key, so it iterates `Rows`. -/
example : [[Cell.value "a", .value "a"], [.value "a", .invalid, .value "a"], [.value "a", .invalid],
      [.value "a", .empty]].map (fun cells => fires "RepetitionNotUnique(Rows/RS)"
        (document [] [] (cells.map fun cell => [("RS", cell)])) (some "Rows/RS")) =
    [some true, some true, some false, some false] := by native_decide

/-! ## Group presence: malformed-only content is unavailable, an absent group is empty -/

private def overGroup (condition : String) : List (Option Bool) :=
  [[], [("GX", filled)], [("GX", Cell.invalid)]].map fun group =>
    fires condition (document [] group)

example : overGroup "GroupFilled(G)" = [some false, some true, some false] ∧
    overGroup "GroupNotFilled(G)" = [some true, some false, some false] := by native_decide

/-- A group whose only descendant is present-empty holds no admitted content (spec/07 §5.1). -/
example : [fires "GroupFilled(G)" (document [] [("GX", .empty)]),
      fires "GroupNotFilled(G)" (document [] [("GX", .empty)])] = [some false, some true] := by native_decide

example : overRows "AtLeastOneGroupFilled(Rows*)" "RN" [[], [.empty], [filled]] =
      [some false, some true, some true] ∧
    overRows "NoGroupFilled(Rows*)" "RN" [[], [.empty], [filled]] = [some true, some false, some false] ∧
    overRows "NumberOfFilledGroups(Rows*) == 2" "RN" [[filled, .empty], [filled]] = [some true, some false] := by
  native_decide

/-- The trio over a group and a field: an absent group is definitely empty. -/
example : [fires "AllGroupsFilled(G, N)" (document [("N", filled)] [("GX", filled)]),
      fires "AllGroupsFilled(G, N)" (document [("N", .invalid)] [("GX", filled)]),
      fires "NotAllGroupsFilled(G, N)" (document [("N", filled)]),
      fires "GroupsNotCollectivelyFilled(G, N)" (document [("N", .empty)] [("GX", filled)])] =
    [some true, some false, some true, some true] := by native_decide

/-! ## Column B over a blank root: only a condition that can fire on empty, or a count on a
comparison's small side, is evaluated there (spec/03 §A.4)

Each rule reports on `N` from `Form`, over no root and over a present root without content. -/

private def overBlank (condition : String) : List (Option Bool) :=
  [Json.mkObj [], Json.mkObj [("Form", Json.mkObj [])]].map (fires condition · (some "N"))

example : [("[N] < 5", false), ("FieldNotFilled(N)", true), ("NoFieldFilled(N, M)", true),
      ("NotAllFieldsFilled(N, M)", true), ("NotExactlyOneFieldFilled(N, M)", true),
      ("GroupNotFilled(G) And FieldNotFilled(N)", true), ("FieldNotFilled(N) And FieldNotFilled(M)", true),
      ("[S] == \"e\" And FieldNotFilled(N)", false), ("FieldNotFilled(N) Or FieldFilled(M)", true),
      ("NumberOfFilledFields(N, M) < 1", true), ("1 >= NumberOfFilledFields(N, M)", true),
      ("NumberOfFilledFields(N, M) >= 0 And NumberOfFilledFields(N, B) >= 0", false),
      ("NumberOfFilledFields(N, M) < 1 And NumberOfFilledFields(N, M) >= 0", true)].all
        (fun (condition, expected) => overBlank condition == [some expected, some expected]) := by
  native_decide

/-! ## String operators and coercions -/

/-- `Length` and concatenation read an empty String as zero and as the empty text. -/
example : overStates "Length(S) == 0" "S" "ab" = [some true, some true, some false, some false] ∧
    overStates "[S] + \"x\" == \"x\"" "S" "ab" = [some true, some true, some false, some false] := by
  native_decide

/-- `empty text` (spec/03 §A.2): an empty source yields `""`, which a concatenation joins, while as a whole
comparison operand it meets the String rule and leaves the comparison unevaluated under either polarity. -/
example : overStates "FieldValueAsString(N) == \"5\"" "N" "5" = [some false, some false, some false, some true] ∧
    overStates "FieldValueAsString(N) != \"5\"" "N" "7" = [some false, some false, some false, some true] ∧
    overStates "FieldValueAsString(N) + \"x\" == \"x\"" "N" "5" = [some true, some true, some false, some false] ∧
    overStates "RangeAsString(S, 1, 2) == \"ab\"" "S" "abc" = [some false, some false, some false, some true] ∧
    overStates "RangeAsString(S, 1, 2) != \"ab\"" "S" "xyz" = [some false, some false, some false, some true] ∧
    overStates "RangeAsString(S, 1, 2) + \"x\" == \"x\"" "S" "ab" = [some true, some true, some false, some false] := by
  native_decide

/-- `CurrentRepetition` is the 1-based coordinate of the row the rule iterates. -/
example : [1, 2, 3].map (fun k => messageCount s!"FieldFilled(Rows/RN) And CurrentRepetition(Rows) == {k}"
      (document [] [] [[("RN", filled)], [("RN", filled)]]) (some "Rows/RN")) = [some 1, some 1, some 0] := by
  native_decide

/-! ## Bounded repetition (Q2-P5)

A sample's `k` rows of a group, `0 ≤ k ≤` its declared repeatability, are its instantiated rows, and a
blank one is content (spec/03 §A.4). They do not bound where a rule fires: an ordinary rule walks the
rule iteration domain of spec/07 §1.3, every declared slot while the declared product is at most 5, and
above it coordinate 1 plus the coordinates some group occupies. Each rule here reports on its group's
field, so it iterates that group. -/

private def rowsCount (shape : List (List (String × Cell))) : Option Nat :=
  messageCount "[Rows/RN] < 5" (document [] [] shape) (some "Rows/RN")

/-- `Rows` declares 3 slots, a product of 3: with no row, with a blank row and with a present-empty `RN`
the rule fires at all three declared slots, each read as `0`; of three filled rows only one is below 5. -/
example : [[], [[]], [[("RN", Cell.empty)]], [[("RN", .value "9")], [("RN", .value "1")], [("RN", .value "9")]]].map
      rowsCount = [some 3, some 3, some 3, some 1] := by native_decide

private def wideCount (wide : List (List (String × Cell))) (rows : List (List (String × Cell)) := []) : Option Nat :=
  messageCount "[Wide/WN] < 5" (document [] [] rows wide) (some "Wide/WN")

/-- `Wide` declares 6 slots, a product above 5: with no row only coordinate 1 is visited, two blank rows
are two coordinates, filled rows fire where they are below 5, and three `Rows` rows occupy coordinates
`Wide` lacks, widening its domain to three. -/
example : [wideCount [], wideCount [[], []], wideCount [[("WN", .value "9")], [("WN", .value "1")], [("WN", .value "1")]],
      wideCount [] [[], [], []]] = [some 1, some 2, some 2, some 3] := by native_decide

end A12Kernel.Dm.LeafStateLocks
