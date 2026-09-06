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

/-- A checked generic entity-list shape built under the **many-required** arity rule has either an
already-many first slot or a trailing slot. A group slot is already-many by itself, so this is
weaker than requiring a star.

The hypothesis is what the measurement made necessary: the value-list quantifiers apply
`soleAllowed` and a sole unstarred field is legal there, so an unconditional statement would now be
false. It is also the more informative form, since a consumer reading it learns which rule the
carrier applied rather than assuming one. -/
theorem checkedFieldEntityShape_requiredMultiplicity
    (checked : CheckedFieldEntityShape model)
    (hArity : checked.arity = .manyRequired) :
    (checked.first.isAlreadyMany || !checked.rest.isEmpty) = true := by
  have := checked.requiredMultiplicity
  rw [hArity] at this
  simpa [EntityListArity.allowsSole] using this

/-- Every checked token distinct-count source retains the common cardinality invariant after family
certification. This carrier is **measured** to be many-required — a sole unstarred field draws
`MVK_PARAMSIZE_INVALIDN` — so the hypothesis is discharged wherever it is applied rather than
constraining the result. -/
theorem checkedTokenDistinctSource_requiredMultiplicity
    (checked : CheckedTokenDistinctSource model)
    (hArity : checked.arity = .manyRequired) :
    (checked.first.isAlreadyMany || !checked.rest.isEmpty) = true := by
  have := checked.requiredMultiplicity
  rw [hArity] at this
  simpa [EntityListArity.allowsSole] using this

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
      (CheckedTokenEntityOperand.field source).resolvedPartialValidationSide
        document outer scope directRead starRead =
          .ok (.inl (source.resolvedSideAt .validation directRead))) ∧
    (scope.coversCell model source.declaration.path [] = false →
      (CheckedTokenEntityOperand.field source).resolvedPartialValidationSide
        document outer scope directRead starRead =
          .ok (.inr .nonRelevant)) := by
  constructor <;> intro relevant <;>
    simp [CheckedTokenEntityOperand.resolvedPartialValidationSide, relevant] <;>
    rfl

/-- The checked-document distinct-count route obtains every slot from the shared rich token resolver before applying its existing first-unavailability scan and fold. -/
theorem checkedTokenDistinctSource_checkedDocument_delegates
    (checked : CheckedTokenEntitySource model)
    (document : CheckedDocument model) (outer : Env) :
    checked.evaluateCheckedDocumentDistinctValidation document outer =
      (do
        match ← scanResolvedValueListOperands
            (state := ResolvedValueListSide .token)
            (terminal := NumericOperand)
            (fun operand => do
              let resolved ←
                operand.resolveCheckedValidationOperand document outer
              pure (.inl (resolved.inCapacityValueListSideAt .validation)))
            (fun cause => .unknown cause)
            (fun accumulated _ side => accumulated.append side)
            checked.operands {
              cells := []
              hasUninstantiatedTail := false
              hasHaving := false } with
        | .inl side => pure (evalDistinctCountAggregate side)
        | .inr result => pure result) := by
  rfl

end A12Kernel
