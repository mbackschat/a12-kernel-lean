import A12Kernel.Elaboration.CheckedGroupPresence
import A12Kernel.Elaboration.FilledFieldGroupCount

/-! # Checked group-scope `NumberOfFilledFields` conformance

The fixed-group rows distinguish filled, present-empty, and absent descendants. The starred rows distinguish whole-extent expansion from a per-row or row-1 read and lock the empty-group zero.

The last case reads **group presence** on the same three-level fixture, because presence and this count answer differently on one document and no fixture of either family alone can show it.
-/

namespace A12Kernel

private def fixedModel : FlatModel :=
  { fields := [
      { id := 1, groupPath := ["Order", "Contact"], name := "Street",
        policy := { kind := .string } },
      { id := 2, groupPath := ["Order", "Contact"], name := "City",
        policy := { kind := .string } }] }

private def fixedPrepared :
    PreparedFlatStringContext fixedModel builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler fixedModel).toOption.get (by native_decide)

private def fixedSource : SurfaceFilledFieldCountFixedGroupValidationSource :=
  { group := { base := .absolute, groups := ["Order", "Contact"] } }

private def fixedChecked? : Option (CheckedFilledFieldCountGroupSource fixedModel) :=
  (elaborateFilledFieldCountFixedGroupValidationSource
    fixedModel ["Order"] fixedSource).toOption

private def fixedRootError? : Option FilledFieldCountGroupElabError :=
  match elaborateFilledFieldCountFixedGroupValidationSource fixedModel ["Order"] {
      group := { base := .absolute, groups := ["Order"] } } with
  | .ok _ => none
  | .error error => some error

example : fixedRootError? = some (.rootGroup ["Order"]) := by
  native_decide

private def fixedCount (cells : List ClassifiedCellInput) : Option FilledFieldCount := do
  let checked ← fixedChecked?
  let document ← (checkDocument fixedPrepared "en_US" {
    instantiatedRows := []
    cells }).toOption
  (checked.evaluateCheckedDocumentValidation document []).toOption

private def fixedOperand (cells : List ClassifiedCellInput) : Option NumericOperand := do
  let checked ← fixedChecked?
  let document ← (checkDocument fixedPrepared "en_US" {
    instantiatedRows := []
    cells }).toOption
  (checked.evaluateCheckedDocumentFixedValidationOperand? document []).toOption.join

private def fixedVerdict (cells : List ClassifiedCellInput) : Option Verdict := do
  let operand ← fixedOperand cells
  pure (NumericComparisonOp.less.evalFixedRight operand 3)

private def cell (field : FieldId) (path : List Nat)
    (stored : String) : ClassifiedCellInput :=
  { address := { field, path }
    stored
    raw := .parsed (.str stored) }

example :
    fixedCount [cell 1 [] "s"] = some (.value 1) ∧
    fixedCount [cell 1 [] "s", cell 2 [] "c"] = some (.value 2) ∧
    fixedCount [] = some (.value 0) := by
  native_decide

/- The declared field extent, not the group's valueless path, controls comparison movement. A
   full fixed group therefore fires with VALUE, while the same firing with one empty direct field
   remains OMISSION because that field can still change the count. -/
example :
    fixedOperand [cell 1 [] "s", cell 2 [] "c"] =
        some (.value 2 .fixed) ∧
      fixedOperand [cell 1 [] "s"] = some (.value 1 .growOnly) ∧
      fixedVerdict [cell 1 [] "s", cell 2 [] "c"] =
        some (.fired .value) ∧
      fixedVerdict [cell 1 [] "s"] = some (.fired .omission) := by
  native_decide

private def starredModel : FlatModel :=
  { fields := [
      { id := 10, groupPath := ["Order", "Lines"], name := "A",
        policy := { kind := .string }, repeatableScope := [10] },
      { id := 11, groupPath := ["Order", "Lines"], name := "B",
        policy := { kind := .string }, repeatableScope := [10] }]
    repeatableGroups := [{
      level := 10, path := ["Order", "Lines"], repeatability := some 10 }] }

private def starredPrepared :
    PreparedFlatStringContext starredModel builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler starredModel).toOption.get (by native_decide)

private def starredSource : SurfaceFilledFieldCountStarredGroupValidationSource :=
  { group := {
      base := .absolute
      groups := [{ name := "Order" }, { name := "Lines", starred := true }] } }

private def starredChecked? :
    Option (CheckedFilledFieldCountGroupSource starredModel) :=
  (elaborateFilledFieldCountStarredGroupValidationSource
    starredModel ["Order"] starredSource).toOption

private def starredCount (rows : List RowAddr)
    (cells : List ClassifiedCellInput) : Option FilledFieldCount := do
  let checked ← starredChecked?
  let document ← (checkDocument starredPrepared "en_US" {
    instantiatedRows := rows
    cells }).toOption
  (checked.evaluateCheckedDocumentValidation document []).toOption

private def twoRows : List RowAddr := [
  { group := 10, path := [1] }, { group := 10, path := [2] }]

private def fourFilled : List ClassifiedCellInput := [
  cell 10 [1] "a1", cell 11 [1] "b1",
  cell 10 [2] "a2", cell 11 [2] "b2"]

example :
    starredCount twoRows fourFilled = some (.value 4) ∧
    starredCount [] [] = some (.value 0) ∧
    starredCount twoRows [cell 10 [2] "a2"] = some (.value 1) := by
  native_decide

private def nestedModel : FlatModel :=
  { fields := [
      { id := 20, groupPath := ["Probe", "Flat"], name := "FlatA",
        policy := { kind := .string } },
      { id := 21, groupPath := ["Probe", "Flat", "Rows"], name := "RowR",
        policy := { kind := .string }, repeatableScope := [20] }]
    repeatableGroups := [{
      level := 20, path := ["Probe", "Flat", "Rows"], repeatability := some 3 }] }

private def nestedPrepared :
    PreparedFlatStringContext nestedModel builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler nestedModel).toOption.get (by native_decide)

private def nestedChecked? : Option (CheckedFilledFieldCountGroupSource nestedModel) :=
  (elaborateFilledFieldCountFixedGroupValidationSource nestedModel ["Probe"] {
    group := { base := .absolute, groups := ["Probe", "Flat"] } }).toOption

private def nestedOperand (rows : List RowAddr)
    (cells : List ClassifiedCellInput) : Option NumericOperand := do
  let checked ← nestedChecked?
  let document ← (checkDocument nestedPrepared "en_US" {
    instantiatedRows := rows
    cells }).toOption
  (checked.evaluateCheckedDocumentFixedValidationOperand? document []).toOption.join

private def nestedRows (count : Nat) : List RowAddr :=
  (List.range count).map fun index => { group := 20, path := [index + 1] }

private def nestedFilled (count : Nat) : List ClassifiedCellInput :=
  cell 20 [] "a" :: (List.range count).map fun index => cell 21 [index + 1] "r"

/- Movement is bounded by the subtree's declared **slot capacity**, not by its declaration count. One
   direct field beside a `max 3` descendant row holding one field admits four cells, so a document at
   two or three filled cells can still grow and fires OMISSION, and only the fourth is fixed. Measured
   on kernel 30.8.1 at the
   [nested-capacity checkpoint](../../docs/SOURCES.md#src-filled-field-count-nested-capacity); the two
   numbers coincide exactly when the subtree owns no repeatable descendant, which every other fixture
   here satisfies. -/
example :
    nestedOperand (nestedRows 1) (nestedFilled 1) = some (.value 2 .growOnly) ∧
    nestedOperand (nestedRows 2) (nestedFilled 2) = some (.value 3 .growOnly) ∧
    nestedOperand (nestedRows 3) (nestedFilled 3) = some (.value 4 .fixed) := by
  native_decide

private def deepModel : FlatModel :=
  { fields := [
      { id := 30, groupPath := ["Probe", "Flat"], name := "FlatA",
        policy := { kind := .string } },
      { id := 31, groupPath := ["Probe", "Flat", "Rows"], name := "RowR",
        policy := { kind := .string }, repeatableScope := [30] },
      { id := 32, groupPath := ["Probe", "Flat", "Rows", "Inner"], name := "InnerI",
        policy := { kind := .string }, repeatableScope := [30, 31] }]
    repeatableGroups := [
      { level := 30, path := ["Probe", "Flat", "Rows"], repeatability := some 2 },
      { level := 31, path := ["Probe", "Flat", "Rows", "Inner"],
        repeatability := some 2 }] }

private def deepPrepared :
    PreparedFlatStringContext deepModel builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler deepModel).toOption.get (by native_decide)

private def deepChecked? : Option (CheckedFilledFieldCountGroupSource deepModel) :=
  (elaborateFilledFieldCountFixedGroupValidationSource deepModel ["Probe"] {
    group := { base := .absolute, groups := ["Probe", "Flat"] } }).toOption

private def deepOperand (rows : List RowAddr)
    (cells : List ClassifiedCellInput) : Option NumericOperand := do
  let checked ← deepChecked?
  let document ← (checkDocument deepPrepared "en_US" {
    instantiatedRows := rows
    cells }).toOption
  (checked.evaluateCheckedDocumentFixedValidationOperand? document []).toOption.join

private def deepOuterRows : List RowAddr :=
  [{ group := 30, path := [1] }, { group := 30, path := [2] }]

private def deepInnerRows (outer : Nat) : List RowAddr :=
  [{ group := 31, path := [outer, 1] }, { group := 31, path := [outer, 2] }]

private def deepOuterCells : List ClassifiedCellInput :=
  [cell 30 [] "a", cell 31 [1] "r", cell 31 [2] "r"]

private def deepInnerCells (outer : Nat) : List ClassifiedCellInput :=
  [cell 32 [outer, 1] "i", cell 32 [outer, 2] "i"]

/- Capacity **compounds** through a second nesting level rather than adding each level once. Two
   `max 2` levels beneath one direct field admit `1 + 2 * (1 + 2 * 1) = 7` cells, so the count is
   still grow-only at five and fixed only at seven. Measured on kernel 30.8.1 at the
   [deep-capacity checkpoint](../../docs/SOURCES.md#src-filled-field-count-deep-capacity), whose
   walk separates this reading from three others: summing each level once bounds at five, the
   declaration count at three, and instantiated rather than declared rows would fix every saturated
   document including the three-cell one below. -/
example :
    deepOperand deepOuterRows deepOuterCells = some (.value 3 .growOnly) ∧
    deepOperand (deepOuterRows ++ deepInnerRows 1)
        (deepOuterCells ++ deepInnerCells 1) = some (.value 5 .growOnly) ∧
    deepOperand (deepOuterRows ++ deepInnerRows 1 ++ deepInnerRows 2)
        (deepOuterCells ++ deepInnerCells 1 ++ deepInnerCells 2) =
      some (.value 7 .fixed) := by
  native_decide

private def nestedStarModel : FlatModel :=
  { fields := [
      { id := 40, groupPath := ["Probe", "Shell", "L1"], name := "V1",
        policy := { kind := .string }, repeatableScope := [40] },
      { id := 41, groupPath := ["Probe", "Shell", "L1", "L2"], name := "V2",
        policy := { kind := .string }, repeatableScope := [40, 41] }]
    repeatableGroups := [
      { level := 40, path := ["Probe", "Shell", "L1"], repeatability := some 2 },
      { level := 41, path := ["Probe", "Shell", "L1", "L2"], repeatability := some 2 }] }

private def nestedStarPrepared :
    PreparedFlatStringContext nestedStarModel builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler nestedStarModel).toOption.get (by native_decide)

/-- The star sits on the **inner** level while the outer one stays unstarred, because the rule
reading it is authored on that outer group and binds it. -/
private def nestedStarChecked? :
    Option (CheckedFilledFieldCountGroupSource nestedStarModel) :=
  (elaborateFilledFieldCountStarredGroupValidationSource nestedStarModel
    ["Probe", "Shell", "L1"] {
      group := {
        base := .absolute
        groups := [{ name := "Probe" }, { name := "Shell" },
                   { name := "L1" }, { name := "L2", starred := true }] } }).toOption

private def nestedStarDocument? : Option (CheckedDocument nestedStarModel) :=
  (checkDocument nestedStarPrepared "en_US" {
    instantiatedRows := [
      { group := 40, path := [1] }, { group := 40, path := [2] },
      { group := 41, path := [1, 1] }]
    cells := [cell 40 [1] "a", cell 40 [2] "b", cell 41 [1, 1] "y"] }).toOption

private def nestedStarCount (outer : Env) : Option FilledFieldCount := do
  let checked ← nestedStarChecked?
  let document ← nestedStarDocument?
  (checked.evaluateCheckedDocumentValidation document outer).toOption

/- A nested star answers from its **own enclosing row**, not from the union of every outer row.
   The second outer row instantiates no inner row at all, so a union account would report the
   first row's cell there too and the two bindings would be indistinguishable. Unbound the
   operand refuses rather than guessing a row, which is what makes this shape a reading question
   rather than a representational one. Measured on kernel 30.8.1 at the
   [nested-star checkpoint](../../docs/SOURCES.md#src-nested-star-bound-outer-level), where the
   same condition draws exactly one message, on the first outer row. -/
example :
    nestedStarCount [(40, 1)] = some (.value 1) ∧
    nestedStarCount [(40, 2)] = some (.value 0) ∧
    nestedStarCount [] = none := by
  native_decide

private def threeLevelModel : FlatModel :=
  { fields := [
      { id := 60, groupPath := ["Probe", "Shell", "L1"], name := "V1",
        policy := { kind := .string }, repeatableScope := [60] },
      { id := 61, groupPath := ["Probe", "Shell", "L1", "L2"], name := "V2",
        policy := { kind := .string }, repeatableScope := [60, 61] },
      { id := 62, groupPath := ["Probe", "Shell", "L1", "L2", "L3"], name := "V3",
        policy := { kind := .string }, repeatableScope := [60, 61, 62] }]
    repeatableGroups := [
      { level := 60, path := ["Probe", "Shell", "L1"], repeatability := some 2 },
      { level := 61, path := ["Probe", "Shell", "L1", "L2"], repeatability := some 2 },
      { level := 62, path := ["Probe", "Shell", "L1", "L2", "L3"],
        repeatability := some 2 }] }

private def threeLevelPrepared :
    PreparedFlatStringContext threeLevelModel builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler threeLevelModel).toOption.get (by native_decide)

private def threeLevelChecked? :
    Option (CheckedFilledFieldCountGroupSource threeLevelModel) :=
  (elaborateFilledFieldCountFixedGroupValidationSource threeLevelModel ["Probe"] {
    group := { base := .absolute, groups := ["Probe", "Shell"] } }).toOption

private def threeLevelCount (rows : List RowAddr)
    (cells : List ClassifiedCellInput) : Option FilledFieldCount := do
  let checked ← threeLevelChecked?
  let document ← (checkDocument threeLevelPrepared "en_US" {
    instantiatedRows := rows
    cells }).toOption
  (checked.evaluateCheckedDocumentValidation document []).toOption

private def threeLevelRows : List RowAddr :=
  [{ group := 60, path := [1] }, { group := 61, path := [1, 1] },
   { group := 62, path := [1, 1, 1] }]

/- The extent reaches a cell **three** repetition levels below the operand, so no axis count bounds
   it. The depth-2 reading this clause once carried would answer zero on the first document, and the
   empty control shows the first is not a group counting unconditionally. Measured on kernel 30.8.1
   at the [group-operand extent checkpoint](../../docs/SOURCES.md#src-group-operand-over-limit-extent),
   where `AtLeastOneFieldFilled` and `NoFieldFilled` over the same operand agree in the same run. -/
example :
    threeLevelCount threeLevelRows [cell 62 [1, 1, 1] "x"] = some (.value 1) ∧
    threeLevelCount threeLevelRows [] = some (.value 0) := by
  native_decide

private def threeLevelOuterRows : List RowAddr :=
  [{ group := 60, path := [1] }, { group := 60, path := [2] },
   { group := 60, path := [3] }]

private def threeLevelInnerRows : List RowAddr :=
  [{ group := 60, path := [1] }, { group := 61, path := [1, 1] },
   { group := 61, path := [1, 2] }, { group := 61, path := [1, 3] }]

/- A cell in a row beyond the group's declared repeatability is **not counted and does not make the
   count unknown**, at the outer level and the inner one alike. The distinction is what the fixture
   is built for: the in-capacity rows are instantiated and empty, so an account that retained the
   offending cell as formally invalid would answer unknown, and kernel 30.8.1 fires a `< 1` rule on
   these documents ([checkpoint](../../docs/SOURCES.md#src-group-operand-over-limit-extent)). Each
   control differs only in the offending index. -/
example :
    threeLevelCount (threeLevelOuterRows.take 2) [cell 60 [2] "x"] = some (.value 1) ∧
    threeLevelCount threeLevelOuterRows [cell 60 [3] "x"] = some (.value 0) ∧
    threeLevelCount (threeLevelInnerRows.take 3) [cell 61 [1, 2] "x"] = some (.value 1) ∧
    threeLevelCount threeLevelInnerRows [cell 61 [1, 3] "x"] = some (.value 0) := by
  native_decide

private def malformedCell (field : FieldId) (path : List Nat) : ClassifiedCellInput :=
  { address := { field, path }
    stored := "?"
    raw := .rejected .malformed }

private def fixedFill
    (operator : CheckedFilledFieldCountGroupSource.GroupFieldFillQuantifier)
    (cells : List ClassifiedCellInput) : Option ValidationFillOutcome := do
  let checked ← fixedChecked?
  let document ← (checkDocument fixedPrepared "en_US" {
    instantiatedRows := []
    cells }).toOption
  (checked.evaluateCheckedDocumentValidationFill operator document []).toOption

private def threeLevelFill
    (operator : CheckedFilledFieldCountGroupSource.GroupFieldFillQuantifier)
    (rows : List RowAddr) (cells : List ClassifiedCellInput) :
    Option ValidationFillOutcome := do
  let checked ← threeLevelChecked?
  let document ← (checkDocument threeLevelPrepared "en_US" {
    instantiatedRows := rows
    cells }).toOption
  (checked.evaluateCheckedDocumentValidationFill operator document []).toOption

/- The two Kernel-measured operators read the same depth-3 extent the count does, and each carries a
   different polarity: `AtLeastOneFieldFilled` fires VALUE, `NoFieldFilled` fires OMISSION. The empty
   control separates a firing from an operator that fires unconditionally, and it is the document on
   which the two exchange places. Measured in the same run as the count
   ([checkpoint](../../docs/SOURCES.md#src-group-operand-over-limit-extent)). -/
example :
    (threeLevelFill .atLeastOneFieldFilled threeLevelRows [cell 62 [1, 1, 1] "x"],
     threeLevelFill .noFieldFilled threeLevelRows [cell 62 [1, 1, 1] "x"],
     threeLevelFill .atLeastOneFieldFilled threeLevelRows [],
     threeLevelFill .noFieldFilled threeLevelRows []) =
    (some (.fired .value), some .falseOrUnknown,
     some .falseOrUnknown, some (.fired .omission)) := by
  native_decide

/- An over-limit filled cell leaves both operators reading an empty extent, exactly as it leaves the
   count at zero. The in-capacity control differs only in the offending index, so the row separates
   the capacity projection from a general failure to see the cell. -/
example :
    (threeLevelFill .atLeastOneFieldFilled threeLevelOuterRows [cell 60 [3] "x"],
     threeLevelFill .noFieldFilled threeLevelOuterRows [cell 60 [3] "x"],
     threeLevelFill .atLeastOneFieldFilled (threeLevelOuterRows.take 2) [cell 60 [2] "x"],
     threeLevelFill .noFieldFilled (threeLevelOuterRows.take 2) [cell 60 [2] "x"]) =
    (some .falseOrUnknown, some (.fired .omission),
     some (.fired .value), some .falseOrUnknown) := by
  native_decide

/- A formally invalid cell is **retained inside** the extent and **excluded above** it, so the same
   bad cell one index apart moves the count between unknown and zero and moves `NoFieldFilled`
   between silent and fired. A definite zero alone cannot separate *removed from the domain* from
   *classified unavailable and not counted*; this pair can, and it is why the consumer opts into the
   in-capacity projection rather than filtering the cells afterwards. Kernel-measured on this
   carrier — `NumberOfFilledFields` is unavailable with the bad cell in capacity and answers `1` with
   the identical cell one index above it, on the starred and unstarred spellings alike
   ([checkpoint](../../docs/sources/inbound-group-operand-batches.md#src-group-operand-capacity-consumer-sweep)).
   It was first locked here as this project's account of the shared extent, carried over from the
   same separator on `Sum`; the count's own row replaced that inheritance rather than confirming it. -/
example :
    (threeLevelCount threeLevelOuterRows [malformedCell 60 [3]],
     threeLevelFill .noFieldFilled threeLevelOuterRows [malformedCell 60 [3]],
     threeLevelCount (threeLevelOuterRows.take 2) [malformedCell 60 [2]],
     threeLevelFill .noFieldFilled (threeLevelOuterRows.take 2) [malformedCell 60 [2]]) =
    (some (.value 0), some (.fired .omission),
     some .unknown, some .falseOrUnknown) := by
  native_decide

/- The fill operators are **not** a projection of the count, and this is the document that proves it:
   one filled cell beside one formally invalid sibling leaves the count unavailable while
   `AtLeastOneFieldFilled` still fires on the filled one. An implementation that answered the
   quantifiers by comparing the count would answer nothing here. `NoFieldFilled` stays silent for the
   opposite reason — it needs both no filled cell and no unknown one — so the two admitted operators
   are not each other's negation either. -/
example :
    (fixedCount [cell 1 [] "s", malformedCell 2 []],
     fixedFill .atLeastOneFieldFilled [cell 1 [] "s", malformedCell 2 []],
     fixedFill .noFieldFilled [cell 1 [] "s", malformedCell 2 []]) =
    (some .unknown, some (.fired .value), some .falseOrUnknown) := by
  native_decide

/- The two evidence-pending operators are the same mechanism at a different threshold: one filled
   cell leaves `MoreThanOneFieldFilled` silent, and `NotExactlyOneFieldFilled` silent as well, while
   a second filled cell fires both with VALUE. The pair is retained because the threshold is where a
   naive `≠ 1` reading would fire on the empty document too, and the empty control shows it fires
   with OMISSION there instead. -/
example :
    (fixedFill .moreThanOneFieldFilled [cell 1 [] "s"],
     fixedFill .notExactlyOneFieldFilled [cell 1 [] "s"],
     fixedFill .moreThanOneFieldFilled [cell 1 [] "s", cell 2 [] "c"],
     fixedFill .notExactlyOneFieldFilled [cell 1 [] "s", cell 2 [] "c"],
     fixedFill .notExactlyOneFieldFilled []) =
    (some .falseOrUnknown, some .falseOrUnknown,
     some (.fired .value), some (.fired .value), some (.fired .omission)) := by
  native_decide

private def threeLevelContent (rows : List RowAddr)
    (cells : List ClassifiedCellInput) : Option Bool := do
  let document ← (checkDocument threeLevelPrepared "en_US" {
    instantiatedRows := rows
    cells }).toOption
  let input ← (document.groupPresenceInput ["Probe", "Shell"] [] .fullyRelevant false).toOption
  pure input.derive.content

/- **Group presence and this count are not one quantity, and the capacity projection is where they
   come apart.** Two documents give the identical count of `0` and opposite presence: with no `L1`
   row at all the shell has neither constituent, while three rows whose only filled cell sits in the
   over-limit third still fill it — the in-capacity rows satisfy presence's *row* constituent, which
   the count has no way to express. Kernel-measured as one pair in one run: `NumberOfFilledGroups`
   drops to one operand on the empty document and stays at two on the over-limit one, while the
   count's `< 1` rule fires on both
   ([checkpoint](../../docs/SOURCES.md#src-group-operand-over-limit-extent)). A consumer that derived
   either operator from the other would answer these two documents alike. -/
example :
    (threeLevelContent threeLevelOuterRows [cell 60 [3] "x"],
     threeLevelCount threeLevelOuterRows [cell 60 [3] "x"],
     threeLevelContent [] [],
     threeLevelCount [] []) =
    (some true, some (.value 0), some false, some (.value 0)) := by
  native_decide

end A12Kernel
