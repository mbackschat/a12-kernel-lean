import A12Kernel.Elaboration.TokenValueCount
import A12Kernel.Proofs.NumericAggregate

/-! # Checked String/Enumeration value-count laws -/

namespace A12Kernel

/-- One present token equal to the authored constant contributes one fixed count through exact token identity. -/
theorem tokenValueCount_singleton_match_fixed (expected : String) :
    evalValueCountAggregate (kind := .token) expected {
      cells := [{
        cell := .present expected
        selectedByHaving := false }]
      hasUninstantiatedTail := false
      hasHaving := false } =
    .value 1 .fixed := by
  simp [evalValueCountAggregate, scanValueCountCells,
    ValueListAtom.equal, pure, Except.pure, NumericFillability.fixed]

/-- A checked typed token count retains the proof that every Enumeration source admits its exact selected stored/category literal. -/
theorem checkedTokenValueCount_expectedAllowed
    (checked : CheckedTokenValueCountSource model) :
    checked.source.allowsValueCountLiteral checked.expected = true :=
  checked.expectedAllowed

/-- String/Enumeration value count always reports the exact integral result scale. -/
theorem checkedTokenValueCount_scaleSummary
    (checked : CheckedTokenValueCountSource model) :
    checked.scaleSummary = NumericScaleSummary.field 0 := by
  rfl

/-- Scalar compatibility refuses a repeatable token source rather than discarding its checked topology. -/
theorem checkedTokenValueCount_direct_none
    (checked : CheckedTokenValueCountSource model)
    (phase : Phase) (read : FieldId → CheckedCell)
    (repeatable : checked.source.directFields? = none) :
    checked.evaluateDirectAt? phase read = none := by
  simp [CheckedTokenValueCountSource.evaluateDirectAt?, repeatable]

/-- Partial validation skips a filtered token count before topology and value reads. -/
theorem checkedTokenValueCount_partialHaving_skips
    (checked : CheckedTokenValueCountSource model)
    (document : Document) (outer : Env)
    (scope : ValidationRelevanceScope)
    (directRead : FieldId → CheckedCell)
    (starRead : Env → FieldId → CheckedCell)
    (filtered : checked.source.hasHaving = true) :
    checked.evaluatePartialValidation document outer scope directRead starRead =
      .ok .skippedHaving := by
  simp [CheckedTokenValueCountSource.evaluatePartialValidation, filtered]
  rfl

/-- A checked `False` count contains only Boolean declarations; Confirm is admitted only by `True`. -/
theorem checkedBooleanValueCount_false_fields_boolean
    (checked : CheckedBooleanValueCountSource model)
    (falseExpected : checked.expected = false)
    (field : FlatFieldDecl) (member : field ∈ checked.fields) :
    field.policy.kind = .boolean := by
  have allowed :=
    List.all_eq_true.mp checked.fieldKindsAllowed field member
  rw [falseExpected] at allowed
  cases kind : field.policy.kind <;>
    simp [booleanValueCountKindAllowed, kind] at allowed ⊢

/-- Boolean/Confirm value count retains the fixed integral result scale of the shared tally. -/
theorem checkedBooleanValueCount_scaleSummary
    (checked : CheckedBooleanValueCountSource model) :
    checked.scaleSummary = NumericScaleSummary.field 0 := by
  rfl

/-- An empty Confirm stays an unfilled value-count cell and cannot become the comparison-only false default. -/
theorem booleanValueCount_confirm_empty :
    booleanValueCountCellAt .validation
        (formalCheck { kind := .confirm } .presentEmpty) =
      .empty := by
  rfl

end A12Kernel
