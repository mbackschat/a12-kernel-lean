import A12Kernel.Elaboration.ValidationRule

/-! # `NumberOfFilledGroups` under partial validation

The count is decided on the counted group's own instances by the four-step walk. Every coverage
below is a row of the peer's second `kf464` table, on its three group-count carriers: a starred
repeatable terminal, a fixed group below that star, and a fixed-only list; the second and third also
run as whole rules on their partial routes. A second fixture replays
`KF209`'s nine selections and three controls, which the walk reproduces because that fixture's group
holds a second field the selections leave uncovered
([inbound](../../docs/SOURCES.md#inbound-2026-09-24b-kf464-partial-group-count)).
-/

namespace A12Kernel.Conformance.PartialGroupCount

open A12Kernel

private def number : FieldPolicy := { kind := .number { scale := 0, signed := false } }

/-- `Batches` of a `Lot` and a fixed `Seal` of a `Code` and a Number `Weight`, at the capacity each
    row names, beside a fixed `Label` of a `Text` and a Number `Grade` and a fixed `Stamp` of a
    `Mark`, as the peer's second fixture declares them. -/
private def model (capacity : Nat) : FlatModel :=
  { fields := [
      { id := 1, groupPath := ["Item", "Batches"], name := "Lot", policy := { kind := .string },
        repeatableScope := [10] },
      { id := 2, groupPath := ["Item", "Batches", "Seal"], name := "Code",
        policy := { kind := .string }, repeatableScope := [10] },
      { id := 3, groupPath := ["Item", "Batches", "Seal"], name := "Weight", policy := number,
        repeatableScope := [10] },
      { id := 4, groupPath := ["Item", "Label"], name := "Text", policy := { kind := .string } },
      { id := 5, groupPath := ["Item", "Label"], name := "Grade", policy := number },
      { id := 6, groupPath := ["Item", "Stamp"], name := "Mark", policy := { kind := .string } }]
    repeatableGroups := [{ level := 10, path := ["Item", "Batches"], repeatability := some capacity }] }

/-- Which one covered value is malformed, if any. -/
private inductive Fault where
  | none | weightRow1 | weightRow2 | grade
  deriving DecidableEq

private def text (field : FieldId) (path : List Nat) : ClassifiedCellInput :=
  { address := { field, path }, stored := "A", raw := .parsed (.str "A") }

private def amount (field : FieldId) (path : List Nat) (malformed : Bool) : ClassifiedCellInput :=
  if malformed then { address := { field, path }, stored := "bad", raw := .rejected .malformed }
  else { address := { field, path }, stored := "1", raw := .parsed (.num 1) }

/-- Two batches, each with all three fields, and every fixed field. -/
private def cells (fault : Fault) : List ClassifiedCellInput :=
  [text 1 [1], text 1 [2], text 2 [1], text 2 [2],
    amount 3 [1] (fault == .weightRow1), amount 3 [2] (fault == .weightRow2),
    text 4 [], amount 5 [] (fault == .grade), text 6 []]

private def batches : SurfaceStarGroupPath :=
  { base := .absolute, groups := [{ name := "Item" }, { name := "Batches", starred := true }] }

private def sealPath : SurfaceStarGroupPath :=
  { base := .absolute,
    groups := [{ name := "Item" }, { name := "Batches", starred := true }, { name := "Seal" }] }

private def fixedGroup (name : String) : SurfaceGroupReference :=
  .path { base := .absolute, groups := ["Item", name] }

/-- The three carriers, in the table's column order: `Batches*`, `Batches*/Seal`, `Label, Stamp`. -/
private def carriers (model : FlatModel) : Option (List (List (CheckedGroupCountOperand model))) := do
  let batchesSource ← (elaborateStarredGroupSource model ["Item"] batches).toOption
  let sealSource ← match elaborateStarredGroupOperandSource model ["Item"] sealPath with
    | .ok (.terminalPresence source) => some source
    | _ => none
  let label ← (model.resolveFixedGroupReference ["Item"] (fixedGroup "Label")).toOption
  let stamp ← (model.resolveFixedGroupReference ["Item"] (fixedGroup "Stamp")).toOption
  pure [[.starred batchesSource], [.starredPresence sealSource], [.fixed label, .fixed stamp]]

/-- The checked document of one row and its partial preliminary. -/
private def setup (capacity : Nat) (fault : Fault) (entities : List RelevantEntityPattern) :
    Option (CheckedDocument (model capacity) × CheckedPartialPreliminary (model capacity)) := do
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler (model capacity)).toOption
  let document ← (checkDocument prepared "en_US" {
    instantiatedRows := [{ group := 10, path := [1] }, { group := 10, path := [2] }]
    cells := cells fault }).toOption
  let preliminary ← (document.applyPartialGeneratedPreliminaryForScope
    (.partialSet entities)).toOption
  pure (document, preliminary)

/-- Each carrier's partial count for one row of the table, in column order. -/
private def counts (capacity : Nat) (fault : Fault) (entities : List RelevantEntityPattern) :
    Option (List PartialValidationFilledGroupCountResult) := do
  let (_, preliminary) ← setup capacity fault entities
  let lists ← carriers (model capacity)
  (lists.mapM fun operands =>
    CheckedGroupCountOperand.evaluatePartial operands preliminary []).toOption

/-- The lone `Batches*/Seal` carrier as the peer's rule comparison, `== 2`, through the partial
    addressed route with the preliminary's own group slice: `some true` fired, `some false` not
    fired, `none` UNKNOWN. -/
private def sealRule (capacity : Nat) (fault : Fault) (entities : List RelevantEntityPattern) :
    Option (Option Bool) := do
  let (document, preliminary) ← setup capacity fault entities
  let comparison ← (elaborateMixedFilledGroupCountComparison (model capacity) ["Item"]
    [.starred sealPath] .equal 2).toOption
  let context : AddressedValidationEvaluationContext (model capacity) := {
    scalar := { fields := document.flatContext, groups := GroupPresenceContext.unavailable }
    outer := []
    input := .partialView document fun environment field =>
      (document.validationAddressedCell environment field).map fun addressed => some addressed.cell }
  let result ← comparison.core.evalAddressedPartial? context preliminary.relevance
    (fun field => preliminary.relevance.coversField (model capacity) field [])
    fun groupPath environment =>
      (preliminary.groupPresenceInput groupPath environment false).mapError .group
  match ← result.toOption with
  | .fired _ => pure (some true)
  | .notFired => pure (some false)
  | .unknown => pure none

private def every (path : List String) : RelevantEntityPattern :=
  RelevantEntityPattern.allInstances path

/-- The given rows of the repeatable second segment, every other segment wildcarded. -/
private def atRows (path : List String) (rows : List Nat) : List RelevantEntityPattern :=
  rows.map fun row =>
    { path, indices := path.mapIdx fun index _ => if index == 1 then .concrete row else .all }

private def lot := ["Item", "Batches", "Lot"]
private def code := ["Item", "Batches", "Seal", "Code"]
private def weight := ["Item", "Batches", "Seal", "Weight"]
private def batchFields := [lot, code, weight]
private def everyField :=
  batchFields ++ [["Item", "Label", "Text"], ["Item", "Label", "Grade"], ["Item", "Stamp", "Mark"]]

/-- The second table's twelve rows, in its order: capacity, fault, coverage. -/
private def rows : List (Nat × Fault × List RelevantEntityPattern) :=
  [ (4, .none, atRows lot [1, 2, 3, 4] ++ [code, weight].map every),
    (4, .none, atRows code [1, 2, 3, 4] ++ [lot, weight].map every),
    (2, .none, every lot :: atRows code [1, 2] ++ atRows weight [1, 2]),
    (2, .none, batchFields.flatMap (atRows · [1, 2])),
    (4, .none, atRows lot [1, 2] ++ [code, weight].map every),
    (4, .none, atRows lot [1, 3] ++ [code, weight].map every),
    (2, .none, every lot :: atRows code [1] ++ atRows weight [1]),
    (2, .none, every lot :: atRows code [2] ++ atRows weight [2]),
    (2, .weightRow1, batchFields.map every),
    (2, .weightRow2, batchFields.map every),
    (2, .grade, everyField.map every),
    (2, .none, everyField.map every) ]

private def decided (count : Nat) : PartialValidationFilledGroupCountResult :=
  .evaluated (.value count)

/- Each decided carrier answers the full-validation count of two, and each undecided one stays
   non-relevant rather than collapsing to a smaller count. The pairs name the step they separate:
   rows 1 and 2 against `NumberOfFilledFields`, which asks `Lot` itself, settle the extent by the
   group's own identifiers; rows 3 and 4 leave a concrete row at the starred level; rows 7 and 8, 9
   and 10 move the first instance's relevance and error; rows 5 and 6 leave a declared instance the
   document lacks open; and row 11 makes a fixed group its own erroneous first instance. -/
example :
    rows.map (fun (capacity, fault, entities) => counts capacity fault entities) =
      [ some [decided 2, decided 2, .nonRelevant],
        some [decided 2, decided 2, .nonRelevant],
        some [decided 2, .nonRelevant, .nonRelevant],
        some [.nonRelevant, .nonRelevant, .nonRelevant],
        some [.nonRelevant, decided 2, .nonRelevant],
        some [.nonRelevant, decided 2, .nonRelevant],
        some [decided 2, .nonRelevant, .nonRelevant],
        some [.nonRelevant, .nonRelevant, .nonRelevant],
        some [.nonRelevant, .nonRelevant, .nonRelevant],
        some [decided 2, decided 2, .nonRelevant],
        some [decided 2, decided 2, .nonRelevant],
        some [decided 2, decided 2, decided 2] ] := by
  native_decide

/- The partial rule route reaches the same walk: the `Seal` column's decided rows fire the peer's
   `== 2` rule and its undecided rows are UNKNOWN, never a smaller count that would not fire. -/
example :
    rows.map (fun (capacity, fault, entities) => sealRule capacity fault entities) =
      [ some (some true), some (some true), some none, some none, some (some true),
        some (some true), some none, some none, some none, some (some true), some (some true),
        some (some true) ] := by
  native_decide

/-- The fixed-only pair as the peer's `== 2` rule on the scalar partial route, its group states read
    off the same preliminary: `some true` fired, `some false` not fired, `none` UNKNOWN. -/
private def fixedPairRule (fault : Fault) (entities : List RelevantEntityPattern) :
    Option (Option Bool) := do
  let (_, preliminary) ← setup 2 fault entities
  let surface : SurfaceNumericComparison :=
    { op := .ordinary .equal
      left := .atom (.filledGroupCount [.fixed (fixedGroup "Label"), .fixed (fixedGroup "Stamp")])
      right := .literal { value := 2, authoredScale := 0 } }
  let comparison ← (elaborateNumericComparison (model 2) ["Item"] surface).toOption
  let condition ← (CheckedValidationCondition.fromNumeric comparison).toOption
  let rule ← (assembleResolvedValidationRule (model 2) condition 6 "PAIR" .error
    { parts := [] }).toOption
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler (model 2)).toOption
  let groups : GroupPresenceContext := fun path =>
    (preliminary.groupPresenceInput path [] false).toOption.map (·.derive)
  match ← (rule.evalPartial prepared "en_US" { read := fun _ => .empty } groups
      (.partialSet entities)).toOption with
  | .skipped => none
  | .evaluated outcome =>
      match outcome.verdict with
      | .fired _ => pure (some true)
      | .notFired => pure (some false)
      | .unknown => pure none

/- The fixed column's two wholly covered rows through a whole rule: a `Label` carrying a malformed
   covered `Grade` beside its admitted `Text` leaves the count undecidable, which full validation
   would count, and the clean twin fires. -/
example : (fixedPairRule .grade (everyField.map every), fixedPairRule .none (everyField.map every)) =
    (some none, some (some true)) := by
  native_decide

/-! ## `KF209`'s selections

`Items` (max 50) of a `Tag` and a Number `Qty`, with two rows whose `Qty` the selections cover and
whose `Tag` none does. -/

private def itemsModel : FlatModel :=
  { fields := [
      { id := 1, groupPath := ["Order", "Items"], name := "Tag", policy := { kind := .string },
        repeatableScope := [10] },
      { id := 2, groupPath := ["Order", "Items"], name := "Qty", policy := number,
        repeatableScope := [10] }]
    repeatableGroups := [{ level := 10, path := ["Order", "Items"], repeatability := some 50 }] }

private def items : SurfaceStarGroupPath :=
  { base := .absolute, groups := [{ name := "Order" }, { name := "Items", starred := true }] }

/-- The starred count over `rowCount` instantiated rows, each `Qty` holding `quantity` if any. -/
private def itemsCount (rowCount : Nat) (quantity : Option Nat)
    (entities : List RelevantEntityPattern) : Option PartialValidationFilledGroupCountResult := do
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler itemsModel).toOption
  let source ← (elaborateStarredGroupSource itemsModel ["Order"] items).toOption
  let rows := (List.range rowCount).map fun index => index + 1
  let document ← (checkDocument prepared "en_US" {
    instantiatedRows := rows.map fun row => { group := 10, path := [row] }
    cells := match quantity with
      | some value => rows.map fun row =>
          { address := { field := 2, path := [row] }, stored := toString value,
            raw := .parsed (.num value) }
      | none => [] }).toOption
  let preliminary ← (document.applyPartialGeneratedPreliminaryForScope
    (.partialSet entities)).toOption
  (CheckedGroupCountOperand.evaluatePartial [.starred source] preliminary []).toOption

private def qtyAt (order items row : RelevanceIndex) : RelevantEntityPattern :=
  { path := ["Order", "Items", "Qty"], indices := [order, items, row] }

private def itemsAt (order items : RelevanceIndex) : RelevantEntityPattern :=
  { path := ["Order", "Items"], indices := [order, items] }

private def concreteRows := [itemsAt .all (.concrete 1), itemsAt .all (.concrete 2)]

/- The nine selections, in `KF209`'s order: only the concrete field beside a group wildcard decides
   the count. A field wildcard alone leaves `Tag` uncovered in the first instance, and concrete group
   rows beside it leave the forty-eight declared rows the document lacks open, so of the four rows a
   count asking `Qty` alone decides, only the one naming the group wildcard is decided here. -/
example :
    [ [qtyAt (.concrete 1) .all (.concrete 1)],
      qtyAt (.concrete 1) .all (.concrete 1) :: concreteRows,
      [qtyAt (.concrete 1) .all (.concrete 1), qtyAt (.concrete 1) (.concrete 1) (.concrete 1)],
      [qtyAt (.concrete 1) (.concrete 1) (.concrete 1), itemsAt .all .all],
      qtyAt .all .all .all :: concreteRows,
      [qtyAt (.concrete 1) .all (.concrete 1), itemsAt (.concrete 1) (.concrete 1),
        itemsAt (.concrete 1) (.concrete 2)],
      concreteRows,
      [itemsAt .all (.concrete 1)],
      [itemsAt .all (.concrete 2)] ].map (itemsCount 2 (some 10)) =
      [ some .nonRelevant, some .nonRelevant, some .nonRelevant, some (decided 2),
        some .nonRelevant, some .nonRelevant, some .nonRelevant, some .nonRelevant,
        some .nonRelevant ] := by
  native_decide

/- The three controls under a field and group wildcard: an instantiated row is a repeatable
   instance's content whether or not a field in it is filled, so two empty rows count two, and no
   rows count zero. -/
example :
    let wildcard := [qtyAt .all .all .all, itemsAt .all .all]
    itemsCount 2 (some 11) wildcard = some (decided 2) ∧
      itemsCount 2 none wildcard = some (decided 2) ∧
      itemsCount 0 none wildcard = some (decided 0) := by
  native_decide

end A12Kernel.Conformance.PartialGroupCount
