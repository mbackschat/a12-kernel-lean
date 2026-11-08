import Lean.Data.Json
import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.Validate
import A12Kernel.Reference.Dm.Replay
import A12Kernel.Semantics.NumericInput

/-! # The cell states of the scalar kinds and the leaf verdicts over them

Each admitted condition leaf over a Number, Boolean, Confirm, Enumeration or String field without a
pattern, read against an absent, an empty, a not-check-relevant and a filled cell. The verdict
follows the leaf's spec/14 cells V (unavailable read), N (empty read) and B (content gate) with the
consumer classes of spec/02 §B.2. A case observes one bit, whether the rule fires: the validation
connectives are two-valued (spec/02 §A.1) and monotone, so a leaf's UNKNOWN and FALSE compose
identically and no rule observes the difference. The matrix is the Q2-P2 acceptance set of
[the plan](../../../docs/PLAN.md#q2-preparation-checklist).

Which nonempty values are filled rather than not check-relevant is each kind's admitted set: for a
decimal-valued Number the conjunction spec/04 §4.8 states, locked here against the cascade, and for
the other kinds the clauses of spec/06 and spec/02 §A.3, locked through the document route (Q2-P3). -/

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
      enumeration := some { storedTokens := ["A", "Z"] } },
    { id := 7, name := "S", groupPath := form, policy.kind := .string, stringPolicy := { maxLength := some 3 } },
    { id := 8, name := "T", groupPath := form, policy.kind := .string, stringPolicy := { maxLength := some 3 } },
    { id := 9, name := "GX", groupPath := ["Form", "G"], policy.kind := .number { scale := 0, signed := true } },
    { id := 10, name := "RN", groupPath := rows, repeatableScope := [10],
      policy.kind := .number { scale := 0, signed := true } },
    { id := 11, name := "RS", groupPath := rows, repeatableScope := [10], policy.kind := .string,
      stringPolicy := { maxLength := some 3 } }]
  repeatableGroups := [{ level := 10, path := rows, repeatability := some 3 }] }

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
`Rows` rows, each a list of named cells. -/
private def document (cells : List (String × Cell)) (group : List (String × Cell) := [])
    (rowCells : List (List (String × Cell)) := []) : Json :=
  let members := fun (named : List (String × Cell)) => named.filterMap fun (name, cell) => cell.member name
  let root := [("Anchor", Json.str "1")] ++ members cells
    ++ (if group.isEmpty then [] else [("G", Json.mkObj (members group))])
    ++ (if rowCells.isEmpty then [] else [("Rows", Json.arr (rowCells.map (Json.mkObj ∘ members)).toArray)])
  Json.mkObj [("Form", Json.mkObj root)]

/-- Whether the rule `FieldFilled(Anchor) And condition`, reporting on `Anchor` from `Form`, fires
over `doc`; `none` when the model check refuses the rule or the document does not read. The rule must
reference its error field (`MVK_ERROR_FIELD_NOT_REFERENCED`), and `Anchor` is always filled, so the
prefix is TRUE and the leaf alone decides. A `target` instead reports on that path with the bare
`condition`, for a leaf that must bind the target's repeatable level. -/
private def fires (condition : String) (doc : Json) (target : Option String := none) : Option Bool := do
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
  pure !messages.isEmpty

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

/-! ## Comparisons: `scalar read` with each kind's empty default -/

/-- Number and Confirm substitute `0` and `False`; Boolean, Enumeration and String leave the
comparison unevaluated. -/
example : overStates "[N] < 5" "N" "3" = [some true, some true, some false, some true] ∧
    overStates "[C] != True" "C" "true" = [some true, some true, some false, some false] ∧
    overStates "[B] == False" "B" "false" = [some false, some false, some false, some true] ∧
    overStates "[E] != \"A\"" "E" "Z" = [some false, some false, some false, some true] ∧
    overStates "[S] != \"a\"" "S" "b" = [some false, some false, some false, some true] := by native_decide

/-- An operand read through arithmetic keeps the Number default. -/
example : overStates "Abs([N]) == 0" "N" "5" = [some true, some true, some false, some false] := by
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

/-- A match ends `No` without firing; the filled control above shows an outside value fires it. -/
example : overStates "NoFieldValueIncludedInValueList(E In \"A\")" "E" "A" =
    [some true, some true, some false, some false] := by native_decide

/-! ## Counts over `(N, M)`: `all-cells`, one unavailable member makes the count unavailable -/

example : overPairs "NumberOfFilledFields(N, M) == 1" [(filled, .empty), (filled, .invalid), (.empty, .invalid)] =
      [some true, some false, some false] ∧
    overPairs "NumberOfDifferentValues(N, M) == 1" [(filled, filled), (filled, .empty), (filled, .invalid)] =
      [some true, some true, some false] ∧
    overPairs "NumberOfValueInFields(5 In N, M) == 1" [(filled, .empty), (filled, .invalid)] =
      [some true, some false] := by native_decide

/-! ## Aggregates over `Rows*/RN`: empties are skipped, an unavailable cell decides by its class -/

private def numberRows : List (List Cell) :=
  [[.value "1", .empty, .value "2"], [.value "1", .invalid, .value "2"]]

example : overRows "Sum(Rows*/RN) == 3" "RN" numberRows = [some true, some false] ∧
    overRows "MaxValue(Rows*/RN) == 2" "RN" numberRows = [some true, some false] ∧
    overRows "MinValue(Rows*/RN) == 1" "RN" numberRows = [some true, some false] := by native_decide

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

/-! ## String operators and coercions -/

/-- `Length` and concatenation read an empty String as zero and as the empty text. -/
example : overStates "Length(S) == 0" "S" "ab" = [some true, some true, some false, some false] ∧
    overStates "[S] + \"x\" == \"x\"" "S" "ab" = [some true, some true, some false, some false] := by
  native_decide

/-- An empty coercion result leaves the comparison unevaluated. -/
example : overStates "FieldValueAsString(N) == \"5\"" "N" "5" = [some false, some false, some false, some true] ∧
    overStates "RangeAsString(S, 1, 2) == \"ab\"" "S" "abc" = [some false, some false, some false, some true] := by
  native_decide

/-! ## Admitted sets (Q2-P3)

The decimal-valued Number set is spec/04 §4.8's conjunction over the read text, compared with the
cascade over every declaration–value pair below. -/

/-- spec/04 §4.8's admitted-set conjunction, written from the clause rather than from the cascade. -/
private def admittedDecimal (info : NumField) (c : NumericTargetConstraints) (v : NumericInputDecimal) : Bool :=
  let read := v.formalReadStored c.minFractionalDigits
  let r := read.scale
  let n := (toString (read.unscaled.natAbs / decimalFactor r)).length
  let length := (if read.unscaled < 0 then 1 else 0) + n + (if r > 0 then r + 1 else 0)
  n + r ≤ 15 &&
    (read.unscaled ≥ 0 || info.signed) &&
    (!c.fractionalDigitsChecked || (c.minFractionalDigits ≤ r && r ≤ info.scale)) &&
    c.maxIntegerDigits.all (n ≤ ·) &&
    (read.unscaled != 0 || c.zeroAllowed) &&
    c.minStoredLength.all (· ≤ length) && c.maxStoredLength.all (length ≤ ·) &&
    c.minimum.all (· ≤ read.amount) && c.maximum.all (read.amount ≤ ·)

private def numberDeclarations : List (NumField × NumericTargetConstraints) := [
  ({ scale := 0, signed := true }, {}),
  ({ scale := 2, signed := true }, { minFractionalDigits := 2 }),
  ({ scale := 2, signed := true }, {}),
  ({ scale := 10, signed := true }, { minFractionalDigits := 10 }),
  ({ scale := 14, signed := true }, {}),
  ({ scale := 0, signed := false }, { zeroAllowed := false, amount := true }),
  ({ scale := 0, signed := true }, { maxIntegerDigits := some 3 }),
  ({ scale := 2, signed := true }, { minFractionalDigits := 2, minStoredLength := some 5, maxStoredLength := some 6 }),
  ({ scale := 2, signed := true }, { minimum := some 1, maximum := some (555 / 100) }),
  ({ scale := 0, signed := true }, { fractionalDigitsChecked := false })]

/-- `(unscaled, scale)`: zero, signs, a negative scale, trailing zeros, the fifteen-digit cap and its
rounding, a rounding carry into a new integer digit, a value that rounds to zero, bound edges. -/
private def numberValues : List NumericInputDecimal :=
  [(0, 0), (5, 0), (-5, 0), (250, 0), (25000, 2), (1, -5), (12345, 0), (123456, 0), (999995, 3), (125, 3),
    (-1, 3), (1555, 3), (556, 2), (5555, 3), (12345678901234567, 7), (5, 1), (1000, 0), (9999, 0),
    (1234567890123456, 0), (100, 2), (-100, 2)].map fun (unscaled, scale) => { unscaled, scale }

example : numberDeclarations.all (fun (info, c) => numberValues.all (fun v =>
    admittedDecimal info c v == (c.checkFormalRead info (.decimal v)).toBool)) := by native_decide

/-- The set is not vacuous: every declaration-specific row the decimal read text can reach refuses some
pair, and some pair is admitted. -/
example : [NumericFormalReadError.totalDigitsTooLong, .negativeNotAllowed, .decimalSeparatorForbidden,
      .fractionalDigitsOutOfRange, .integerDigitsTooLong, .zeroNotAllowed, .textTooShort, .textTooLong,
      .belowMinimum, .aboveMaximum].all (fun error => numberDeclarations.any (fun (info, c) =>
        numberValues.any (fun v => match c.checkFormalRead info (.decimal v) with
          | .error refused => refused == error
          | .ok _ => false))) &&
    numberDeclarations.any (fun (info, c) => numberValues.any (fun v => (c.checkFormalRead info (.decimal v)).toBool)) := by
  native_decide

/-- The other kinds through the document route: an admitted text fires `FieldFilled`, a refused one
leaves the cell not check-relevant. Strings: the length bound, both blanks, a line break and a
character outside the default set; tokens are case-folded by the reader only for Boolean and Confirm. -/
example : [("S", "abc"), ("S", "abcd"), ("S", " ab"), ("S", "ab "), ("S", "a\nb"), ("S", "😀"),
      ("E", "A"), ("E", "Z"), ("E", "B"), ("E", "a"),
      ("B", "true"), ("B", "false"), ("B", "TRUE"), ("B", "yes"),
      ("C", "true"), ("C", "TRUE"), ("C", "false")].map (fun (field, text) =>
        fires s!"FieldFilled({field})" (document [(field, .value text)])) =
    [some true, some false, some false, some false, some false, some false,
      some true, some true, some false, some false,
      some true, some true, some true, some false,
      some true, some true, some false] := by native_decide

end A12Kernel.Dm.LeafStateLocks
