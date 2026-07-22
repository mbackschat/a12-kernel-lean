import A12Kernel.Elaboration.TokenDistinctCount
import A12Kernel.Proofs.ValueList

/-! # Checked token distinct-count laws -/

namespace A12Kernel

/-- Exact token equality absorbs a repeated representative. -/
theorem tokenDistinctCount_equal_pair (value : String) :
    evalDistinctCountAggregate ({
      cells := [.present value, .present value]
      hasUninstantiatedTail := false
      hasHaving := false } : ResolvedValueListSide .token) =
        .value 1 .fixed := by
  simp [evalDistinctCountAggregate, scanDistinctCells,
    ValueListCell.scanPresent, insertDistinctValue,
    ResolvedValueListSide.hasMissingPotential,
    ResolvedValueListSide.hasEmpty, ValueListCell.isEmpty,
    ValueListAtom.equal]

/-- Every checked generic entity-list shape has either a starred first slot or a trailing slot. -/
theorem checkedFieldEntityShape_requiredMultiplicity
    (checked : CheckedFieldEntityShape model) :
    (checked.first.isStar || !checked.rest.isEmpty) = true :=
  checked.requiredMultiplicity

/-- Every checked token distinct-count source retains the common cardinality invariant after family certification. -/
theorem checkedTokenDistinctSource_requiredMultiplicity
    (checked : CheckedTokenDistinctSource model) :
    (checked.first.isStar || !checked.rest.isEmpty) = true :=
  checked.requiredMultiplicity

/-- Repeated direct references are impossible at the checked token boundary. -/
theorem checkedTokenDistinctSource_uniqueDirectOperands
    (checked : CheckedTokenDistinctSource model) :
    firstDuplicateDirectTokenDistinctField? checked.operands = none :=
  checked.uniqueDirectOperands

/-- Token distinct count always reports the exact integral result scale. -/
theorem checkedTokenDistinctSource_scaleSummary
    (checked : CheckedTokenDistinctSource model) :
    checked.distinctScaleSummary = NumericScaleSummary.field 0 := by
  rfl

/-- A direct checked token slot contributes exactly one phase-indexed classified cell and no structural uncertainty. -/
theorem checkedTokenDistinctField_resolvedSideAt
    (checked : CheckedTokenDistinctField model) (phase : Phase)
    (read : FieldId → CheckedCell) :
    checked.resolvedSideAt phase read = {
      cells := [checked.valueListCellAt phase read]
      hasUninstantiatedTail := false
      hasHaving := false } := by
  rfl

/-- Unfiltered starred phase resolution delegates to the one checked path topology and the one checked token classifier. -/
theorem checkedTokenDistinctStar_resolvedUnfilteredSideAt
    (checked : CheckedTokenDistinctStarSource model) (phase : Phase)
    (document : Document) (outer : Env)
    (read : Env → FieldId → CheckedCell)
    (unfiltered : checked.filter.isNone = true) :
    checked.resolvedUnfilteredSideAt phase document outer read unfiltered =
      checked.source.resolvedValueListSide document outer
        (checked.valueListCellAt phase read) := by
  rfl

/-- Partial relevance is decided before a direct checked token cell is inspected. -/
theorem checkedTokenDistinctField_partial_relevance
    (source : CheckedTokenDistinctField model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (directRead : FieldId → CheckedCell)
    (starRead : Env → FieldId → CheckedCell) :
    (scope.coversCell model source.declaration.path [] = true →
      (CheckedTokenEntityOperand.field source).resolvedPartialDistinctValidationSide
        document outer scope directRead starRead =
          .ok (.inl (source.resolvedSideAt .validation directRead))) ∧
    (scope.coversCell model source.declaration.path [] = false →
      (CheckedTokenEntityOperand.field source).resolvedPartialDistinctValidationSide
        document outer scope directRead starRead =
          .ok (.inr .nonRelevant)) := by
  constructor <;> intro relevant <;>
    simp [CheckedTokenEntityOperand.resolvedPartialDistinctValidationSide, relevant] <;>
    rfl

end A12Kernel
