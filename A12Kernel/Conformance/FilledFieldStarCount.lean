import A12Kernel.Elaboration.FilledFieldStarCount
import A12Kernel.Elaboration.NumericAggregate.Entities

/-! # Capacity-bounded starred filled-field counts

The exact single-level over-repetition probe separates the star evaluation domain from the checked document's complete formal-cell view. Both `Sum` and `NumberOfFilledFields` must ignore the over-limit row while ordinary in-cap formal failures remain observable.
-/

namespace A12Kernel

private def premium : FlatFieldDecl :=
  { id := 2
    groupPath := ["Policy", "Coverages"]
    name := "Premium"
    policy := { kind := .number { scale := 0, signed := false } }
    repeatableScope := [10] }

private def model : FlatModel :=
  { fields := [premium]
    repeatableGroups := [{
      level := 10
      path := ["Policy", "Coverages"]
      repeatability := some 2 }] }

private def starPath : SurfaceStarFieldPath :=
  { base := .absolute
    groups := [
      { name := "Policy" },
      { name := "Coverages", starred := true }]
    field := "Premium" }

private def starredGroupPath : SurfaceStarGroupPath :=
  { base := .absolute
    groups := [
      { name := "Policy" },
      { name := "Coverages", starred := true }] }

private def numberSource? : Option (CheckedNumberEntitySource model) :=
  (elaborateNumberEntitySource model ["Policy"] {
    first := .star starPath
    rest := [] }).toOption

private def filledSource? : Option (CheckedStarFieldPath model) :=
  (elaborateFilledFieldStarValidationSource model ["Policy"] starPath).toOption

private def filledGroupSource? : Option (CheckedStarredGroupSource model) :=
  (elaborateStarredGroupSource model ["Policy"] starredGroupPath).toOption

private def prepared :
    PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def rows : List RowAddr := [
  { group := 10, path := [1] },
  { group := 10, path := [2] },
  { group := 10, path := [3] }]

private def cell (row value : Nat) : ClassifiedCellInput :=
  { address := { field := premium.id, path := [row] }
    stored := toString value
    raw := .parsed (.num value) }

private def malformedCell (row : Nat) : ClassifiedCellInput :=
  { address := { field := premium.id, path := [row] }
    stored := "bad"
    raw := .rejected .malformed }

private def documentWith? (cells : List ClassifiedCellInput) :
    Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := rows
    cells }).toOption

private def partialDocumentFor? (selectedRows : List RowAddr)
    (cells : List ClassifiedCellInput) :
    Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := selectedRows
    cells }).toOption

private def partialDocumentWith? (cells : List ClassifiedCellInput) :
    Option (CheckedDocument model) :=
  partialDocumentFor? (rows.take 2) cells

private def aggregateWith? (op : NumericAggregateOp)
    (cells : List ClassifiedCellInput) : Option NumericOperand := do
  let source ← numberSource?
  let document ← documentWith? cells
  (source.evaluateCheckedDocumentValidationAggregate op document []).toOption

private def sumWith? (cells : List ClassifiedCellInput) : Option NumericOperand :=
  aggregateWith? .sum cells

private def valueCountWith? (expected : Rat)
    (cells : List ClassifiedCellInput) : Option NumericOperand := do
  let source ← numberSource?
  let document ← documentWith? cells
  (source.evaluateCheckedDocumentValueCountValidation expected document []).toOption

private def filledCountWith?
    (cells : List ClassifiedCellInput) : Option FilledFieldCount := do
  let source ← filledSource?
  let document ← documentWith? cells
  (source.evaluateFilledFieldCountValidation document []).toOption

private def filledGroupCount? : Option FilledGroupCount := do
  let source ← filledGroupSource?
  (source.numberOfFilledGroups {
    instantiatedRows := rows
    rawCells := fun _ => none } []).toOption

private def relevance (path : List String) (indices : List RelevanceIndex) :
    RelevantEntityPattern :=
  { path, indices }

private def partialFilledCountFor? (selectedRows : List RowAddr)
    (scope : ValidationRelevanceScope) (cells : List ClassifiedCellInput) :
    Option PartialValidationFilledFieldCountResult := do
  let source ← filledSource?
  let document ← partialDocumentFor? selectedRows cells
  (source.evaluatePartialFilledFieldCountValidation document [] scope).toOption

private def partialValueCountFor? (selectedRows : List RowAddr)
    (scope : ValidationRelevanceScope) (cells : List ClassifiedCellInput) :
    Option PartialValidationNumberAggregateResult := do
  let source ← numberSource?
  let document ← partialDocumentFor? selectedRows cells
  (source.evaluateCheckedDocumentPartialValueCount 10 document [] scope).toOption

private def partialFilledGroupCountFor? (selectedRows : List RowAddr)
    (scope : ValidationRelevanceScope) :
    Option PartialValidationFilledGroupCountResult := do
  let source ← filledGroupSource?
  (source.evaluatePartialNumberOfFilledGroups {
    instantiatedRows := selectedRows
    rawCells := fun _ => none } [] scope).toOption

private def partialFilledCountWith? (scope : ValidationRelevanceScope)
    (cells : List ClassifiedCellInput) :
    Option PartialValidationFilledFieldCountResult :=
  partialFilledCountFor? (rows.take 2) scope cells

private def partialValueCountWith? (scope : ValidationRelevanceScope)
    (cells : List ClassifiedCellInput) :
    Option PartialValidationNumberAggregateResult :=
  partialValueCountFor? (rows.take 2) scope cells

private def partialFilledGroupCount? (scope : ValidationRelevanceScope) :
    Option PartialValidationFilledGroupCountResult :=
  partialFilledGroupCountFor? (rows.take 2) scope

private def fieldWildcard : RelevantEntityPattern :=
  relevance premium.path [.concrete 1, .all, .concrete 1]

private def allSemanticFieldWildcard : RelevantEntityPattern :=
  RelevantEntityPattern.allInstances premium.path

private def concreteField (row : Nat) : RelevantEntityPattern :=
  relevance premium.path [.concrete 1, .concrete row, .concrete 1]

private def groupWildcard : RelevantEntityPattern :=
  relevance premium.groupPath [.concrete 1, .all]

private def concreteGroup (row : Nat) : RelevantEntityPattern :=
  relevance premium.groupPath [.concrete 1, .concrete row]

/- The over-limit third row must not poison the ordinary starred aggregate or enter its sum. -/
example :
    sumWith? [cell 1 10, cell 2 20, cell 3 99] =
        some (.value 30 .fixed) ∧
    filledCountWith? [cell 1 10, cell 2 20, cell 3 99] =
        some (.value 2) ∧
    filledGroupCount? = some (.value 2) := by
  native_decide

/- Operators outside the measured three-consumer slice retain the complete formal-cell view rather than inheriting Sum's capacity projection. -/
example :
    aggregateWith? .minimum [cell 1 10, cell 2 20, cell 3 99] =
        some (.unknown .overRepetition) ∧
    aggregateWith? .maximum [cell 1 10, cell 2 20, cell 3 99] =
        some (.unknown .overRepetition) ∧
    aggregateWith? .distinctCount [cell 1 10, cell 2 20, cell 3 99] =
        some (.unknown .overRepetition) ∧
    valueCountWith? 99 [cell 1 10, cell 2 20, cell 3 99] =
        some (.unknown .overRepetition) := by
  native_decide

/- Capacity projection is not a blanket formal-error filter: an in-cap malformed row still makes both measured consumers unavailable. -/
example :
    sumWith? [cell 1 10, malformedCell 2, cell 3 99] =
        some (.unknown .malformed) ∧
    filledCountWith? [cell 1 10, malformedCell 2, cell 3 99] =
        some .unknown := by
  native_decide

/- The filled-field count uses the reduced-universal field extent. A wildcard survives a concrete identifier for the same field, but unrelated concrete group rows remain and make the extent unavailable. -/
example :
    let cells := [cell 1 10, cell 2 10]
    partialFilledCountWith? (.partialSet [fieldWildcard]) cells =
        some (.evaluated (.value 2)) ∧
      partialFilledCountWith? (.partialSet [fieldWildcard,
        concreteGroup 1, concreteGroup 2]) cells = some .nonRelevant ∧
      partialFilledCountWith? (.partialSet [fieldWildcard,
        concreteField 1]) cells = some (.evaluated (.value 2)) ∧
      partialFilledCountWith? (.partialSet [concreteField 1,
        groupWildcard]) cells = some (.evaluated (.value 2)) ∧
      partialFilledCountWith? (.partialSet [allSemanticFieldWildcard,
        concreteGroup 1, concreteGroup 2]) cells =
          some (.evaluated (.value 2)) ∧
      partialFilledCountWith? (.partialSet [concreteGroup 1,
        concreteGroup 2]) cells = some .nonRelevant ∧
      partialFilledCountWith? (.partialSet [concreteGroup 1]) cells =
        some .nonRelevant := by
  native_decide

/- The starred group count applies the same reduced-universal predicate to the group operand path. Field identifiers do not project upward to that path, so only the explicit group wildcard admits this matrix. -/
example :
    partialFilledGroupCount? (.partialSet [fieldWildcard]) =
        some .nonRelevant ∧
      partialFilledGroupCount? (.partialSet [fieldWildcard,
        concreteGroup 1, concreteGroup 2]) = some .nonRelevant ∧
      partialFilledGroupCount? (.partialSet [fieldWildcard,
        concreteField 1]) = some .nonRelevant ∧
      partialFilledGroupCount? (.partialSet [concreteField 1,
        groupWildcard]) = some (.evaluated (.value 2)) ∧
      partialFilledGroupCount? (.partialSet [allSemanticFieldWildcard,
        concreteGroup 1, concreteGroup 2]) = some .nonRelevant ∧
      partialFilledGroupCount? (.partialSet [concreteGroup 1,
        concreteGroup 2]) = some .nonRelevant ∧
      partialFilledGroupCount? (.partialSet [concreteGroup 2]) =
        some .nonRelevant := by
  native_decide

/- The numeric value count keeps the existential value-list extent. One field or ancestor-group wildcard suffices even beside concrete group siblings, while concrete rows alone cannot close the extent. -/
example :
    let cells := [cell 1 10, cell 2 10]
    partialValueCountWith? (.partialSet [fieldWildcard]) cells =
        some (.evaluated (.value 2 .fixed)) ∧
      partialValueCountWith? (.partialSet [fieldWildcard,
        concreteGroup 1, concreteGroup 2]) cells =
          some (.evaluated (.value 2 .fixed)) ∧
      partialValueCountWith? (.partialSet [concreteField 1,
        groupWildcard]) cells = some (.evaluated (.value 2 .fixed)) ∧
      partialValueCountWith? (.partialSet [concreteGroup 1,
        concreteGroup 2]) cells = some .nonRelevant ∧
      partialValueCountWith? (.partialSet [concreteGroup 1]) cells =
        some .nonRelevant := by
  native_decide

/- The three inert-fixture controls keep all operators relevant while separating filled fields, structural groups, and matching values. -/
example :
    let selectedRows := rows.take 2
    let scope := ValidationRelevanceScope.partialSet [fieldWildcard, groupWildcard]
    partialFilledCountFor? selectedRows scope [cell 1 11, cell 2 11] =
        some (.evaluated (.value 2)) ∧
      partialFilledGroupCountFor? selectedRows scope =
        some (.evaluated (.value 2)) ∧
      partialValueCountFor? selectedRows scope [cell 1 11, cell 2 11] =
        some (.evaluated (.value 0 .fixed)) ∧
      partialFilledCountFor? selectedRows scope [] =
        some (.evaluated (.value 0)) ∧
      partialFilledGroupCountFor? selectedRows scope =
        some (.evaluated (.value 2)) ∧
      partialValueCountFor? selectedRows scope [] =
        some (.evaluated (.value 0 .growOnly)) ∧
      partialFilledCountFor? [] scope [] =
        some (.evaluated (.value 0)) ∧
      partialFilledGroupCountFor? [] scope =
        some (.evaluated (.value 0)) ∧
      partialValueCountFor? [] scope [] =
        some (.evaluated (.value 0 .growOnly)) := by
  native_decide

/- A relevant malformed field is evaluated but unknown, which is distinct from an unavailable partial extent. -/
example :
    partialFilledCountWith? (.partialSet [fieldWildcard])
        [cell 1 10, malformedCell 2] = some (.evaluated .unknown) := by
  native_decide

end A12Kernel
