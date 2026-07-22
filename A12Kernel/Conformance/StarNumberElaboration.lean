import A12Kernel.Elaboration.FirstFilledValue

/-! # Checked nested Number-star consumption locks -/

namespace A12Kernel.Conformance.StarNumberElaboration

open A12Kernel

private def amount : FlatFieldDecl :=
  { id := 7
    groupPath := ["Shop", "Sections", "Items"]
    name := "Amount"
    policy := { kind := .number { scale := 0, signed := false } }
    repeatableScope := [10, 20] }

private def note : FlatFieldDecl :=
  { amount with id := 8, name := "Note", policy := { kind := .string } }

private def sectionLimit : FlatFieldDecl :=
  { id := 9
    groupPath := ["Shop", "Sections"]
    name := "Limit"
    policy := { kind := .number { scale := 0, signed := false } }
    repeatableScope := [10] }

private def otherAmount : FlatFieldDecl :=
  { id := 10
    groupPath := ["Shop", "Other"]
    name := "Amount"
    policy := { kind := .number { scale := 0, signed := false } }
    repeatableScope := [30] }

private def model : FlatModel :=
  { fields := [amount, note, sectionLimit, otherAmount]
    repeatableGroups := [
      { level := 20, path := ["Shop", "Sections", "Items"], repeatability := some 2 },
      { level := 10, path := ["Shop", "Sections"], repeatability := some 2 },
      { level := 30, path := ["Shop", "Other"], repeatability := some 2 }] }

private def source (field : String := "Amount") (outerStar : Bool := true) :
    SurfaceStarFieldPath :=
  { base := .absolute
    groups := [
      { name := "Shop" }, { name := "Sections", starred := outerStar },
      { name := "Items", starred := true }]
    field }

private def document (rows : List RowAddr) : Document :=
  { instantiatedRows := rows, rawCells := fun _ => none }

private def standardRows : List RowAddr := [
  { group := 10, path := [1] }, { group := 20, path := [1, 1] },
  { group := 20, path := [1, 2] }, { group := 10, path := [2] },
  { group := 20, path := [2, 1] }]

private def readAmount (environment : Env) (_ : FieldId) : RawCell :=
  match environment with
  | [(10, 1), (20, 1)] => .parsed (.num 1)
  | [(10, 1), (20, 2)] => .presentEmpty
  | [(10, 2), (20, 1)] => .parsed (.num 3)
  | _ => .empty

private inductive NumberCellSnapshot where
  | present (value : Rat)
  | empty
  | unknown (cause : FormalCause)
  deriving Repr, DecidableEq

private def snapshotCell : ValueListCell .number → NumberCellSnapshot
  | .present value => .present value
  | .empty => .empty
  | .unknown cause => .unknown cause

private def cellsOf (authored : SurfaceStarFieldPath) (rows : List RowAddr)
    (outer : Env := []) (read : Env → FieldId → RawCell := readAmount) :=
  match elaborateStarNumberSource model amount.groupPath authored with
  | .error _ => none
  | .ok checked => match checked.resolvedValueSide (document rows) outer read with
      | .error _ => none
      | .ok side => some (side.cells.map snapshotCell, side.hasUninstantiatedTail)

private def repetition (origin : HavingOrigin)
    (level : RepeatableLevel) : HavingRepetitionRef :=
  { origin, level }

private def absoluteField (groups : List String) (field : String) : SurfaceFieldPath :=
  { base := .absolute, groups, field }

private def absoluteGroup (groups : List String) : SurfaceGroupPath :=
  { base := .absolute, groups }

private def surfaceNumber (origin : HavingOrigin) (groups : List String)
    (field : String) : SurfaceHavingNumberRef :=
  { origin, field := absoluteField groups field }

private def surfaceRepetition (origin : HavingOrigin)
    (groups : List String) : SurfaceHavingRepetitionRef :=
  { origin, group := absoluteGroup groups }

private def surfaceSameParentEarlierChild : SurfaceCorrelatedHaving :=
  .and
    (.compareRepetitions .equal
      (surfaceRepetition .inner ["Shop", "Sections"])
      (surfaceRepetition .outer ["Shop", "Sections"]))
    (.compareRepetitions .less
      (surfaceRepetition .inner ["Shop", "Sections", "Items"])
      (surfaceRepetition .outer ["Shop", "Sections", "Items"]))

private def surfaceEarlierThanCapturedLimit : SurfaceCorrelatedHaving :=
  .compareNumbers .less
    (surfaceNumber .inner ["Shop", "Sections", "Items"] "Amount")
    (surfaceNumber .outer ["Shop", "Sections"] "Limit")

private def sameParentEarlierChild : CorrelatedHaving :=
  .and
    (CorrelatedHaving.compareRepetitions .equal
      (repetition .inner 10) (repetition .outer 10))
    (CorrelatedHaving.compareRepetitions .lessThan
      (repetition .inner 20) (repetition .outer 20))

private def unusedFilterRead (_ : Env) (_ : FieldId) : CheckedCell :=
  formalCheck { kind := .number { scale := 0, signed := false } } .empty

private def numberFilterRead (environment : Env) (fieldId : FieldId) : CheckedCell :=
  let raw :=
    if fieldId == amount.id then
      match environment with
      | [(10, 1), (20, 1)] => .parsed (.num 1)
      | [(10, 1), (20, 2)] => .parsed (.num 2)
      | [(10, 2), (20, 1)] => .parsed (.num 3)
      | _ => .empty
    else if fieldId == sectionLimit.id then
      match environment with
      | (10, 1) :: _ => .parsed (.num 2)
      | (10, 2) :: _ => .parsed (.num 4)
      | _ => .empty
    else
      .rejected .malformed
  formalCheck { kind := .number { scale := 0, signed := false } } raw

private def readSelectedOnly (environment : Env) (_ : FieldId) : RawCell :=
  match environment with
  | [(10, 1), (20, 1)] => .parsed (.num 1)
  | [(10, 2), (20, 1)] => .parsed (.num 3)
  | _ => .rejected .malformed

private def havingCellsOf (outer : Env) :=
  match elaborateStarNumberSource model amount.groupPath (source) with
  | .error _ => none
  | .ok checked =>
      match checked.resolvedValidationHavingValueSide (document standardRows) outer
          sameParentEarlierChild unusedFilterRead readSelectedOnly with
      | .error _ => none
      | .ok side => some (side.cells.map snapshotCell,
          side.hasUninstantiatedTail, side.hasHaving)

private def authoredHavingCellsOf (outer : Env) :=
  match elaborateStarNumberHavingSource model amount.groupPath (source)
      surfaceSameParentEarlierChild with
  | .error _ => none
  | .ok checked =>
      match checked.resolvedValueSide (document standardRows) outer
          unusedFilterRead readSelectedOnly with
      | .error _ => none
      | .ok side => some (side.cells.map snapshotCell,
          side.hasUninstantiatedTail, side.hasHaving)

private def authoredNumberHavingCellsOf (outer : Env) :=
  match elaborateStarNumberHavingSource model amount.groupPath (source)
      surfaceEarlierThanCapturedLimit with
  | .error _ => none
  | .ok checked =>
      match checked.resolvedValueSide (document standardRows) outer
          numberFilterRead readSelectedOnly with
      | .error _ => none
      | .ok side => some (side.cells.map snapshotCell,
          side.hasUninstantiatedTail, side.hasHaving)

private def havingErrorOf (declaringGroup : GroupPath)
    (authoredSource : SurfaceStarFieldPath) (having : SurfaceCorrelatedHaving) :=
  match elaborateStarNumberHavingSource model declaringGroup authoredSource having with
  | .ok _ => none
  | .error error => some error

private def relevance (path : List String) (indices : List RelevanceIndex) :
    RelevantEntityPattern :=
  { path, indices }

private inductive PartialSideSnapshot where
  | nonRelevant
  | relevant (cells : List NumberCellSnapshot) (hasUninstantiatedTail : Bool)
  deriving Repr, DecidableEq

private def partialCellsOf (scope : ValidationRelevanceScope) :=
  match elaborateStarNumberSource model amount.groupPath (source) with
  | .error _ => none
  | .ok checked =>
      match checked.resolvedPartialAllRowsValueSide
          (document standardRows) [] scope readAmount with
      | .error _ => none
      | .ok AllRowsValidationStarNumberSide.nonRelevant =>
          some PartialSideSnapshot.nonRelevant
      | .ok (AllRowsValidationStarNumberSide.relevant side) =>
          some (PartialSideSnapshot.relevant
          (side.cells.map snapshotCell) side.hasUninstantiatedTail)

private def partialFirstFilledOf (scope : ValidationRelevanceScope)
    (read : Env → FieldId → RawCell := readAmount) :=
  match elaborateStarNumberSource model amount.groupPath (source) with
  | .error _ => none
  | .ok checked =>
      match checked.resolvedPartialValidationFirstFilled
          (document standardRows) [] scope read with
      | .error _ => none
      | .ok result => some result

/- The checked consumer preserves canonical nested order, emptiness, and the hierarchical tail. -/
example : cellsOf (source) standardRows = some (
    [.present 1, .empty, .present 3], true) := by
  native_decide

/- An unstarred outer axis is bound by identity before the inner star reopens. -/
example : cellsOf (source (outerStar := false)) standardRows [(10, 2)] =
    some ([.present 3], true) := by
  native_decide

/- All-rows aggregate relevance is a path-level wildcard gate: full validation, an exact fully-wildcarded field, and a nonrepeatable ancestor group admit the unchanged topology-produced stream. -/
example :
    partialCellsOf .full = some (.relevant [.present 1, .empty, .present 3] true) ∧
    partialCellsOf (.partialSet [relevance amount.path
      [.concrete 1, .all, .all, .concrete 1]]) =
        some (.relevant [.present 1, .empty, .present 3] true) ∧
    partialCellsOf (.partialSet [relevance ["Shop"] [.concrete 1]]) =
        some (.relevant [.present 1, .empty, .present 3] true) := by
  native_decide

/- A relevant formally unavailable head is also terminal, so a later nonrelevant cell cannot replace its exact cause. -/
example :
    let malformedHead : Env → FieldId → RawCell := fun environment _ =>
      if environment == [(10, 1), (20, 1)] then .rejected .declaredConstraint
      else .parsed (.num 7)
    partialFirstFilledOf (.partialSet [relevance amount.path
      [.concrete 1, .concrete 1, .concrete 1, .concrete 1]]) malformedHead =
        some (.evaluated (.unavailable .declaredConstraint)) := by
  native_decide

/- Enumerating every actual leaf concretely still does not make an all-rows star fully relevant; nor does wildcarding only its outer repeatable level. -/
example :
    partialCellsOf (.partialSet [
      relevance amount.path [.concrete 1, .concrete 1, .concrete 1, .concrete 1],
      relevance amount.path [.concrete 1, .concrete 1, .concrete 2, .concrete 1],
      relevance amount.path [.concrete 1, .concrete 2, .concrete 1, .concrete 1]]) =
        some .nonRelevant ∧
    partialCellsOf (.partialSet [relevance amount.path
      [.concrete 1, .all, .concrete 1, .concrete 1]]) = some .nonRelevant := by
  native_decide

/- Relevance does not guess structural alignment or widen a sibling field into an ancestor. -/
example :
    partialCellsOf (.partialSet [relevance amount.path [.all, .all]]) =
        some .nonRelevant ∧
    partialCellsOf (.partialSet [relevance note.path [.all, .all, .all, .all]]) =
        some .nonRelevant := by
  native_decide

/- `FirstFilledValue` tests relevance only when a cell is reached: a relevant present head hides every later nonrelevant cell, while a nonrelevant head suppresses before a later present value. -/
example :
    partialFirstFilledOf (.partialSet [relevance amount.path
      [.concrete 1, .concrete 1, .concrete 1, .concrete 1]]) =
        some (.evaluated (.value 1 false)) ∧
    partialFirstFilledOf (.partialSet [relevance amount.path
      [.concrete 1, .concrete 1, .concrete 2, .concrete 1]]) =
        some .nonRelevant := by
  native_decide

/- A reached relevant empty prefix does not permit skipping the next relevance decision. If that next cell is relevant and present, the ordinary empty-prefix OMISSION polarity survives and the still-later nonrelevant cell remains invisible. -/
example :
    let emptyThenSeven : Env → FieldId → RawCell := fun environment _ =>
      match environment with
      | [(10, 1), (20, 1)] => .presentEmpty
      | [(10, 1), (20, 2)] => .parsed (.num 7)
      | _ => .rejected .malformed
    partialFirstFilledOf (.partialSet [relevance amount.path
      [.concrete 1, .concrete 1, .concrete 1, .concrete 1]]) emptyThenSeven =
        some .nonRelevant ∧
    partialFirstFilledOf (.partialSet [
      relevance amount.path
        [.concrete 1, .concrete 1, .concrete 1, .concrete 1],
      relevance amount.path
        [.concrete 1, .concrete 1, .concrete 2, .concrete 1]]) emptyThenSeven =
        some (.evaluated (.value 7 true)) := by
  native_decide

/- `$` retains the complete captured environment: parent equality restricts the nested scan to the captured parent, while child order selects only earlier children. The malformed target values on every dropped leaf never enter the selected side. -/
example :
    havingCellsOf [(10, 1), (20, 2)] = some ([.present 1], true, true) ∧
    havingCellsOf [(10, 2), (20, 2)] = some ([.present 3], true, true) ∧
      havingCellsOf [(10, 1), (20, 1)] = some ([], true, true) := by
  native_decide

/- Checked authored lowering reaches that same resolved filter without accepting a caller-forged core. -/
example :
    authoredHavingCellsOf [(10, 1), (20, 2)] =
        some ([.present 1], true, true) ∧
      authoredHavingCellsOf [(10, 2), (20, 2)] =
        some ([.present 3], true, true) := by
  native_decide

/- Number references route independently: the candidate Amount reads each leaf, while the captured ancestor Limit remains fixed for the outer rule row. -/
example :
    authoredNumberHavingCellsOf [(10, 1), (20, 2)] =
      some ([.present 1], true, true) := by
  native_decide

/- An uncorrelated filter is legal when an inner reference reaches a reopened level. -/
example :
    (elaborateStarNumberHavingSource model amount.groupPath (source)
      (.compareRepetitions .less
        (surfaceRepetition .inner ["Shop", "Sections", "Items"])
        (surfaceRepetition .inner ["Shop", "Sections", "Items"]))).isOk = true := by
  native_decide

/- The same general lowering admits a reopened candidate Number against an ancestor value available from the complete captured environment. -/
example :
    (elaborateStarNumberHavingSource model amount.groupPath (source)
      (.compareNumbers .less
        (surfaceNumber .inner ["Shop", "Sections", "Items"] "Amount")
        (surfaceNumber .outer ["Shop", "Sections"] "Limit"))).isOk = true := by
  native_decide

/- `$`-only/bound-only filters and references requiring unavailable candidate or captured bindings fail before runtime. -/
example :
    havingErrorOf amount.groupPath (source (outerStar := false))
        (.compareNumbers .equal
          (surfaceNumber .inner ["Shop", "Sections"] "Limit")
          (surfaceNumber .outer ["Shop", "Sections"] "Limit")) =
        some (.having .missingInner) ∧
      havingErrorOf amount.groupPath (source)
        (.compareNumbers .equal
          (surfaceNumber .inner ["Shop", "Other"] "Amount")
          (surfaceNumber .outer ["Shop", "Sections", "Items"] "Amount")) =
        some (.having (.fieldOutsideEnvironment .inner otherAmount.path
          [10, 20] [30])) ∧
      havingErrorOf ["Shop", "Sections"] (source)
        (.compareNumbers .equal
          (surfaceNumber .inner ["Shop", "Sections", "Items"] "Amount")
          (surfaceNumber .outer ["Shop", "Sections", "Items"] "Amount")) =
        some (.having (.fieldOutsideEnvironment .outer amount.path
          [10] [10, 20])) ∧
      havingErrorOf amount.groupPath (source)
        (.compareRepetitions .equal
          (surfaceRepetition .inner ["Shop", "Sections", "Items"])
          (surfaceRepetition .outer ["Shop", "Other"])) =
        some (.having (.repetitionOutsideEnvironment .outer ["Shop", "Other"]
          [10, 20] 30)) := by
  native_decide

/- Either an inner or outer over-capacity coordinate makes the selected Number cell formally unavailable. -/
example :
    let innerRows := standardRows ++ [{ group := 20, path := [1, 3] }]
    let outerRows := standardRows ++ [
      { group := 10, path := [3] }, { group := 20, path := [3, 1] }]
    cellsOf (source) innerRows (read := fun env _ =>
      if env == [(10, 1), (20, 3)] then .parsed (.num 9) else readAmount env amount.id) =
        some ([.present 1, .empty, .unknown .overRepetition, .present 3], true) ∧
    cellsOf (source (outerStar := false)) outerRows [(10, 3)] (read := fun env _ =>
      if env == [(10, 3), (20, 1)] then .parsed (.num 9) else readAmount env amount.id) =
        some ([.unknown .overRepetition], true) := by
  native_decide

/- General checked path admission remains kind-safe for the concrete Number consumer. -/
example :
    (match elaborateStarNumberSource model amount.groupPath (source "Note") with
    | .error (.fieldNotNumber path) => path == note.path
    | _ => false) = true := by
  native_decide

end A12Kernel.Conformance.StarNumberElaboration
