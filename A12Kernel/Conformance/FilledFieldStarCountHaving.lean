import A12Kernel.Elaboration.FilledFieldStarCount

/-! # Filtered starred filled-field counts

A row-local `Having` selects candidates before `NumberOfFilledFields` reads any cell, so a non-true
filter drops exactly its own row and the count answers over the survivors rather than becoming
unavailable. The retained Kernel rows are the filter-true, filter-false, filter-operand-malformed,
and mixed selections at the [non-true-row checkpoint](../../docs/sources/group-and-iteration-probes.md#src-having-filter-nontrue-row).

Two case pairs carry the load. The **read-order** pair changes only the second row's `Other` cell,
so the same malformed *counted* cell is dropped with its row in one document and counted in the
other; without filter-before-consumer both would answer unknown. The **selection-versus-fill** case
keeps a row whose counted cell is empty, which separates counting selected rows from counting
filled cells in selected rows.

The filter fragment admits no literal, so the separating condition is the field pair `Flag == Other`:
true where they agree, false where they differ, non-true where either is malformed.
-/

namespace A12Kernel

private def amount : FlatFieldDecl :=
  { id := 1
    groupPath := ["Form", "Rows"]
    name := "Amount"
    policy := { kind := .number { scale := 0, signed := false } }
    repeatableScope := [10] }

private def flag : FlatFieldDecl :=
  { id := 2
    groupPath := ["Form", "Rows"]
    name := "Flag"
    policy := { kind := .number { scale := 0, signed := false } }
    repeatableScope := [10] }

private def other : FlatFieldDecl :=
  { id := 3
    groupPath := ["Form", "Rows"]
    name := "Other"
    policy := { kind := .number { scale := 0, signed := false } }
    repeatableScope := [10] }

private def tag : FlatFieldDecl :=
  { id := 4
    groupPath := ["Form", "Rows"]
    name := "Tag"
    policy := { kind := .string }
    repeatableScope := [10] }

private def model : FlatModel :=
  { fields := [amount, flag, other, tag]
    repeatableGroups := [{
      level := 10, path := ["Form", "Rows"], repeatability := some 5 }] }

private def starPath : SurfaceStarFieldPath :=
  { base := .absolute
    groups := [{ name := "Form" }, { name := "Rows", starred := true }]
    field := "Amount" }

private def repeatedPath (field : String) : SurfaceFieldPath :=
  { base := .absolute, groups := ["Form", "Rows"], field }

private def flagEqualsOther : SurfaceCorrelatedHaving :=
  .compareNumbers .equal
    { origin := .inner, field := repeatedPath "Flag" }
    { origin := .inner, field := repeatedPath "Other" }

private def source? (having : Option SurfaceCorrelatedHaving) :
    Option (CheckedFilledFieldStarSource model) :=
  (elaborateFilledFieldStarSource model ["Form"] starPath having).toOption

/-- The same route declared **in** the repeatable group, so the filter has a captured outer
    environment to bind. Every other case in this module uses the nonrepeatable declaring group,
    where an outer-origin reference has no environment at all and is refused for that reason
    instead — which is why the scope rule below needs its own entry point rather than reusing
    `source?`. -/
private def correlatedSource? (having : Option SurfaceCorrelatedHaving) :
    Option (CheckedFilledFieldStarSource model) :=
  (elaborateFilledFieldStarSource model ["Form", "Rows"] starPath having).toOption

private def tagPresent (origin : HavingOrigin) : SurfaceCorrelatedHaving :=
  .presence .filled { origin, field := repeatedPath "Tag" }

/- The filter's scope rule, measured on the Kernel and matched here: a `$`-marked reference does
   **not** bind the filtered list's own iterated level, so a filter whose only reference is
   outer-origin is refused, while one in-scope conjunct beside the identical outer leaf admits it.
   The Kernel reports `MVK_NO_ITERATION_FOR_WILDCARD` for the refused form
   ([checkpoint](../../docs/sources/group-and-iteration-probes.md#src-outer-origin-filter-leaves)). -/

private def correlatedSourceError? (having : Option SurfaceCorrelatedHaving) :
    Option FilledFieldStarCountElabError :=
  match elaborateFilledFieldStarSource model ["Form", "Rows"] starPath having with
  | .ok _ => none
  | .error error => some error

/-- The exact arm, not a bare `none`: the filter reaches no reopened level. -/
example : correlatedSourceError? (some (tagPresent .outer)) =
    some (.having .missingInner) := by
  native_decide

example : (correlatedSource? (some (.and (tagPresent .inner) (tagPresent .outer)))).isSome
    = true := by
  native_decide

example : (correlatedSource? (some (tagPresent .inner))).isSome = true := by
  native_decide

private def prepared :
    PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def rows : List RowAddr := [
  { group := 10, path := [1] },
  { group := 10, path := [2] }]

private def num (field row value : Nat) : ClassifiedCellInput :=
  { address := { field, path := [row] }
    stored := toString value
    raw := .parsed (.num value) }

private def bad (field row : Nat) : ClassifiedCellInput :=
  { address := { field, path := [row] }
    stored := "bad"
    raw := .rejected .malformed }

private def documentWith? (cells : List ClassifiedCellInput) :
    Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" { instantiatedRows := rows, cells }).toOption

private def countWith? (having : Option SurfaceCorrelatedHaving)
    (cells : List ClassifiedCellInput) : Option FilledFieldCount := do
  let source ← source? having
  let document ← documentWith? cells
  (source.evaluateFilledFieldCountValidation document []).toOption

private def filteredCount? (cells : List ClassifiedCellInput) :
    Option FilledFieldCount :=
  countWith? (some flagEqualsOther) cells

private def unfilteredCount? (cells : List ClassifiedCellInput) :
    Option FilledFieldCount :=
  countWith? none cells

/-- Both rows agree, so both survive and both filled cells count. -/
example : filteredCount? [
    num amount.id 1 7, num flag.id 1 1, num other.id 1 1,
    num amount.id 2 9, num flag.id 2 1, num other.id 2 1] =
    some (.value 2) := by
  native_decide

/-- A definitely false filter keeps no row, and the count is an ordinary zero rather than unknown. -/
example : filteredCount? [
    num amount.id 1 7, num flag.id 1 1, num other.id 1 2,
    num amount.id 2 9, num flag.id 2 1, num other.id 2 2] =
    some (.value 0) := by
  native_decide

/-- A malformed filter operand is non-true, so it drops its row exactly as a false one does. The
    count stays available: the counted cells are well formed and simply unreached. -/
example : filteredCount? [
    num amount.id 1 7, bad flag.id 1, num other.id 1 1,
    num amount.id 2 9, bad flag.id 2, num other.id 2 1] =
    some (.value 0) := by
  native_decide

/-- Exclusion is per row: one surviving row answers from its own cell, not by collapsing. -/
example : filteredCount? [
    num amount.id 1 7, num flag.id 1 1, num other.id 1 1,
    num amount.id 2 9, num flag.id 2 1, num other.id 2 2] =
    some (.value 1) := by
  native_decide

/- The read-order pair. Only row 2's `Other` differs between these two cases, so the malformed
   counted cell is identical and its row's selection is the whole difference. -/

/-- Row 2 is dropped, so its malformed counted cell is never read. -/
example : filteredCount? [
    num amount.id 1 7, num flag.id 1 1, num other.id 1 1,
    bad amount.id 2, num flag.id 2 1, num other.id 2 2] =
    some (.value 1) := by
  native_decide

/-- Row 2 is kept, so the same malformed counted cell makes the count unavailable. -/
example : filteredCount? [
    num amount.id 1 7, num flag.id 1 1, num other.id 1 1,
    bad amount.id 2, num flag.id 2 1, num other.id 2 1] =
    some .unknown := by
  native_decide

/-- Without the filter the dropped row's malformed cell is counted, so the filter is what hides it. -/
example : unfilteredCount? [
    num amount.id 1 7, num flag.id 1 1, num other.id 1 1,
    bad amount.id 2, num flag.id 2 1, num other.id 2 2] =
    some .unknown := by
  native_decide

/-- Selection is not fill: a kept row with an empty counted cell contributes nothing, so a document
    whose only surviving row is empty counts zero rather than one. -/
example : filteredCount? [
    num flag.id 1 1, num other.id 1 1,
    num amount.id 2 9, num flag.id 2 1, num other.id 2 2] =
    some (.value 0) := by
  native_decide

/-- The unfiltered baseline on that same document counts the second row's filled cell, so the zero
    above is the filter's doing rather than an empty operand list. -/
example : unfilteredCount? [
    num flag.id 1 1, num other.id 1 1,
    num amount.id 2 9, num flag.id 2 1, num other.id 2 2] =
    some (.value 1) := by
  native_decide

/- Partial validation. The Kernel skips a filtered rule whatever the coverage: relevance over the
   filter's own operands does not lift it, and neither does relevance over the whole tree. Only the
   unfiltered count evaluates, which is what makes the skip a property of carrying a filter. -/

private def allCells : List ClassifiedCellInput := [
  num amount.id 1 7, num flag.id 1 1, num other.id 1 1,
  num amount.id 2 9, num flag.id 2 1, num other.id 2 1]

private def partialCountWith? (having : Option SurfaceCorrelatedHaving)
    (scope : ValidationRelevanceScope) :
    Option PartialValidationFilledFieldCountResult := do
  let source ← source? having
  let document ← (checkDocument prepared "en_US" {
    instantiatedRows := rows
    cells := allCells }).toOption
  (source.evaluatePartialFilledFieldCountValidation document [] scope).toOption

private def everyInstanceOf (field : FlatFieldDecl) : RelevantEntityPattern :=
  RelevantEntityPattern.allInstances field.path

private def filterOperandsRelevant : ValidationRelevanceScope :=
  .partialSet [everyInstanceOf amount, everyInstanceOf flag, everyInstanceOf other]

/-- A filtered operand is skipped even when every field its filter reads is relevant. -/
example : partialCountWith? (some flagEqualsOther) filterOperandsRelevant =
    some .skippedHaving := by
  native_decide

/-- `skippedHaving` is separated from the confusable arm rather than being the only one observed:
    under a scope that covers nothing the operand reads, the **plain** route answers `nonRelevant`
    while the filtered one still answers `skippedHaving`. So the filter's skip is not a relabelled
    non-relevance, and the two arms are distinguishable on one scope. -/
private def nothingRelevant : ValidationRelevanceScope :=
  .partialSet [everyInstanceOf tag]

example : partialCountWith? none nothingRelevant = some .nonRelevant := by
  native_decide

example : partialCountWith? (some flagEqualsOther) nothingRelevant =
    some .skippedHaving := by
  native_decide

/-- The unfiltered operand over that same relevance evaluates, so the skip above is the filter's
    doing rather than missing coverage. -/
example : partialCountWith? none filterOperandsRelevant =
    some (.evaluated (.value 2)) := by
  native_decide

/- The String-equality filter leaf. Its Kernel runtime is retained at the same checkpoint: an
   absent or present-empty operand fails the equality and drops only its own row, which is a
   different rule from the Number leaf, where an empty operand participates as zero and can
   therefore satisfy its comparison. -/

private def tagEquals (expected : String) : SurfaceCorrelatedHaving :=
  .compareStrings .equal { origin := .inner, field := repeatedPath "Tag" } expected

private def numberThroughStringLeaf : SurfaceCorrelatedHaving :=
  .compareStrings .equal { origin := .inner, field := repeatedPath "Flag" } "K"

/-- The same leaf naming the star's own target field. Kept beside the case above so the refusal is
    attributable to the **kind** rather than to the reference coinciding with the counted field:
    `Flag` is not the target and refuses identically. -/
private def targetThroughStringLeaf : SurfaceCorrelatedHaving :=
  .compareStrings .equal { origin := .inner, field := repeatedPath "Amount" } "K"

private def sourceError? (having : Option SurfaceCorrelatedHaving) :
    Option FilledFieldStarCountElabError :=
  match elaborateFilledFieldStarSource model ["Form"] starPath having with
  | .ok _ => none
  | .error error => some error

private def tagDiffers (expected : String) : SurfaceCorrelatedHaving :=
  .compareStrings .notEqual { origin := .inner, field := repeatedPath "Tag" } expected

private def text (field row : Nat) (value : String) : ClassifiedCellInput :=
  { address := { field, path := [row] }
    stored := value
    raw := .parsed (.str value) }

private def tagCount? (expected : String) (cells : List ClassifiedCellInput) :
    Option FilledFieldCount :=
  countWith? (some (tagEquals expected)) cells

/-- Both rows carry the matching text, so both survive and both counted cells contribute. -/
example : tagCount? "K" [
    num amount.id 1 7, text tag.id 1 "K",
    num amount.id 2 9, text tag.id 2 "K"] = some (.value 2) := by
  native_decide

/-- A non-matching row drops on its own, so the count comes from the matching row alone. -/
example : tagCount? "K" [
    num amount.id 1 7, text tag.id 1 "K",
    num amount.id 2 9, text tag.id 2 "X"] = some (.value 1) := by
  native_decide

/-- An **absent** String operand fails the equality; the count is an ordinary zero, not unknown. -/
example : tagCount? "K" [
    num amount.id 1 7,
    num amount.id 2 9] = some (.value 0) := by
  native_decide

/-- A present-empty String **cell** is not representable here, and that is the representation
    boundary rather than a gap in the filter. `CheckedDocument` refuses an empty stored text, because
    this theory encodes A12's "no empty String values" rule as absence instead of as an
    empty-texted cell; the nonempty control on the same shape is accepted. So the Kernel's
    present-empty input collapses onto the absent case above, which is why the two measured rows
    share one case here. -/
example : documentWith? [
    num amount.id 1 7, text tag.id 1 "",
    num amount.id 2 9, text tag.id 2 ""] = none := by
  native_decide

example : (documentWith? [
    num amount.id 1 7, text tag.id 1 "K",
    num amount.id 2 9, text tag.id 2 "K"]).isSome := by
  native_decide

/-- Mixing the two: the empty operand costs its own row and nothing else. -/
example : tagCount? "K" [
    num amount.id 1 7, text tag.id 1 "K",
    num amount.id 2 9] = some (.value 1) := by
  native_decide

/-- The read-order pair again, now on the String leaf: row 2 is dropped, so its malformed counted
    cell is never read. -/
example : tagCount? "K" [
    num amount.id 1 7, text tag.id 1 "K",
    bad amount.id 2, text tag.id 2 "X"] = some (.value 1) := by
  native_decide

/-- The same malformed counted cell makes the count unavailable once its row is kept. -/
example : tagCount? "K" [
    num amount.id 1 7, text tag.id 1 "K",
    bad amount.id 2, text tag.id 2 "K"] = some .unknown := by
  native_decide

/-- The leaf resolves through the model-owned String **value** capability rather than accepting any
    declaration, so a Number field named through it is refused at elaboration — and the exact arm is
    asserted, because a bare `none` is equally consistent with a scope or environment refusal. -/
example : sourceError? (some numberThroughStringLeaf) =
    some (.having (.fieldNotStringValue ["Form", "Rows", "Flag"])) := by
  native_decide

/-- The star's own target field refuses through the identical arm, so the kind is the cause rather
    than the reference coinciding with the counted field. -/
example : sourceError? (some targetThroughStringLeaf) =
    some (.having (.fieldNotStringValue ["Form", "Rows", "Amount"])) := by
  native_decide

/- Inequality is the one operator that separates an operand which *participates* with an empty value
   from one that suppresses its comparison, because a participating empty would differ from any
   nonempty literal and so keep its row. It suppresses: an absent operand answers not-fired under
   `!=` exactly as under `==`. Kernel-retained on both the direct comparison surface and here, each
   with its own live positive control, so the zeros below are suppression rather than an inert rule.
   [`spec/03`](../../spec/03-empty-and-required.md)'s primitive default tier owns the rule; these
   rows are its String carrier under the negated operator. -/

/-- Both operands absent: `!=` keeps neither row, though a participating empty would keep both. -/
example : countWith? (some (tagDiffers "K")) [
    num amount.id 1 7,
    num amount.id 2 9] = some (.value 0) := by
  native_decide

/-- The positive control on the same filter: a present operand differing from the literal keeps its
    row, so the leaf is live and `!=` really does fire. -/
example : countWith? (some (tagDiffers "K")) [
    num amount.id 1 7, text tag.id 1 "X",
    num amount.id 2 9] = some (.value 1) := by
  native_decide

/-- And a matching operand fails `!=`, which is the ordinary false rather than a suppression. -/
example : countWith? (some (tagDiffers "K")) [
    num amount.id 1 7, text tag.id 1 "K",
    num amount.id 2 9] = some (.value 0) := by
  native_decide

/- The presence leaves. Both polarities are Kernel-retained at the same checkpoint over clean
   cells, where they are exact complements: each keeps precisely the rows the other drops, and the
   two counts sum to the row count. -/

private def tagFilled : SurfaceCorrelatedHaving :=
  .presence .filled { origin := .inner, field := repeatedPath "Tag" }

private def tagNotFilled : SurfaceCorrelatedHaving :=
  .presence .notFilled { origin := .inner, field := repeatedPath "Tag" }

private def flagFilled : SurfaceCorrelatedHaving :=
  .presence .filled { origin := .inner, field := repeatedPath "Flag" }

private def flagNotFilled : SurfaceCorrelatedHaving :=
  .presence .notFilled { origin := .inner, field := repeatedPath "Flag" }

private def bothTagged : List ClassifiedCellInput := [
  num amount.id 1 7, text tag.id 1 "K",
  num amount.id 2 9, text tag.id 2 "K"]

private def neitherTagged : List ClassifiedCellInput := [
  num amount.id 1 7,
  num amount.id 2 9]

private def oneTagged : List ClassifiedCellInput := [
  num amount.id 1 7, text tag.id 1 "K",
  num amount.id 2 9]

example : countWith? (some tagFilled) bothTagged = some (.value 2) := by
  native_decide

example : countWith? (some tagNotFilled) bothTagged = some (.value 0) := by
  native_decide

example : countWith? (some tagFilled) neitherTagged = some (.value 0) := by
  native_decide

example : countWith? (some tagNotFilled) neitherTagged = some (.value 2) := by
  native_decide

/-- One row each way, so the two polarities split the rows rather than one of them collapsing. -/
example : countWith? (some tagFilled) oneTagged = some (.value 1) := by
  native_decide

example : countWith? (some tagNotFilled) oneTagged = some (.value 1) := by
  native_decide

/- A formally unavailable presence operand is non-true under *both* polarities, so it drops its row
   either way and the two counts stop being complements — they sum to one row short. Every row of
   this block is Kernel-retained at the same checkpoint. -/

/-- One clean and one unavailable operand: only the clean row's polarity keeps anything. -/
example : countWith? (some flagFilled) [
    num amount.id 1 7, num flag.id 1 1,
    num amount.id 2 9, bad flag.id 2] = some (.value 1) := by
  native_decide

example : countWith? (some flagNotFilled) [
    num amount.id 1 7, num flag.id 1 1,
    num amount.id 2 9, bad flag.id 2] = some (.value 0) := by
  native_decide

/-- Both operands unavailable: **neither** polarity keeps a row, which is what distinguishes an
    unknown leaf from a false one being negated into a true one. -/
example : countWith? (some flagFilled) [
    num amount.id 1 7, bad flag.id 1,
    num amount.id 2 9, bad flag.id 2] = some (.value 0) := by
  native_decide

example : countWith? (some flagNotFilled) [
    num amount.id 1 7, bad flag.id 1,
    num amount.id 2 9, bad flag.id 2] = some (.value 0) := by
  native_decide

/-- Absence and formal unavailability side by side in one document, which is the separator against
    the most tempting wrong account: an **absent** operand makes `FieldNotFilled` true and keeps its
    row, while an unavailable one does not. Treating unavailable as absent would answer two here. -/
example : countWith? (some flagNotFilled) [
    num amount.id 1 7,
    num amount.id 2 9, bad flag.id 2] = some (.value 1) := by
  native_decide

example : countWith? (some flagFilled) [
    num amount.id 1 7,
    num amount.id 2 9, bad flag.id 2] = some (.value 0) := by
  native_decide

/- A disjunctive filter. The filter's condition is the ordinary strong-Kleene tree, so a true
   disjunct dominates an unavailable one and keeps its row — which is what separates the filter
   position from the computation arm, where a reached invalid read aborts instead. Every row is
   Kernel-retained; row 2 of each document names no filter operand, so it is definitely dropped and
   the count reads as the first row's own survival. -/

private def flagOrTagFilled : SurfaceCorrelatedHaving :=
  .or
    (.presence .filled { origin := .inner, field := repeatedPath "Flag" })
    (.presence .filled { origin := .inner, field := repeatedPath "Tag" })

/-- Unavailable `Or` true keeps the row: the healthy disjunct decides. -/
example : countWith? (some flagOrTagFilled) [
    num amount.id 1 7, bad flag.id 1, text tag.id 1 "K",
    num amount.id 2 9] = some (.value 1) := by
  native_decide

/-- Unavailable `Or` false drops it, so the row above survived on its true disjunct rather than on
    the filter tolerating an unavailable operand anywhere. -/
example : countWith? (some flagOrTagFilled) [
    num amount.id 1 7, bad flag.id 1,
    num amount.id 2 9] = some (.value 0) := by
  native_decide

example : countWith? (some flagOrTagFilled) [
    num amount.id 1 7, num flag.id 1 1,
    num amount.id 2 9] = some (.value 1) := by
  native_decide

example : countWith? (some flagOrTagFilled) [
    num amount.id 1 7,
    num amount.id 2 9] = some (.value 0) := by
  native_decide

end A12Kernel
