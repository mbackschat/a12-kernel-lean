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

/-- A checked token-group value count excludes over-capacity cells before computation classifies their declaration-owned token projections. -/
theorem checkedTokenValueCountGroup_checkedComputation_usesCapacityProjection
    (checked : CheckedTokenValueCountGroupSource model)
    (document : CheckedDocument model) (outer : Env) :
    checked.evaluateCheckedDocumentComputation document outer = (do
      let resolved ← (CheckedTokenEntityOperand.group checked.group)
        |>.resolveCheckedValidationOperand document outer
      let side :=
        (ResolvedValueCountSide.empty : ResolvedValueCountSide .token)
          |>.appendResolved
            (resolved.inCapacityValueListSideAt .computation)
      pure (evalValueCountAggregate checked.expected side)) := by
  rfl

/-- Checked token value-count validation narrows group operands and unfiltered starred fields to
    declared capacity, while direct and filtered operands retain their existing projection. -/
theorem checkedTokenValueCount_checkedValidation_usesMeasuredProjection
    (checked : CheckedTokenValueCountSource model)
    (document : CheckedDocument model) (outer : Env) :
    checked.evaluateCheckedDocumentValidation document outer =
      evalResolvedValueCountOperands checked.expected checked.source.operands
        (fun operand => do
          let resolved ←
            operand.resolveCheckedValidationOperand document outer
          match operand with
          | .group _ =>
              pure (.inl (resolved.inCapacityValueListSideAt .validation))
          | .star source =>
              match source.filter, source.operand with
              | none, .string _ =>
                  pure (.inl (resolved.inCapacityValueListSideAt .validation))
              | _, _ =>
                  pure (.inl (resolved.valueListSideAt .validation))
          | .field _ =>
              pure (.inl (resolved.valueListSideAt .validation))) := by
  rfl

/-- Each measured checked Boolean-group computation specializes the shared in-capacity addressed
    projection before applying canonical constant-specific token classification. -/
theorem checkedBooleanValueCountStarredGroup_checkedComputation_usesCapacityProjection
    (checked : CheckedBooleanValueCountStarredGroupSource model expected)
    (document : CheckedDocument model) (outer : Env) :
    checked.evaluateCheckedDocumentComputation document outer = (do
      let core ← document.resolveCheckedGroupEntityOperandCore outer
        checked.group.source.boundLevelCount checked.group.fields
      let resolved : ResolvedValueListSide .token := {
        cells := core.inCapacityAddressedCells.map fun addressed =>
          booleanValueCountCellAt .computation addressed.cell
        hasUninstantiatedTail := core.hasUninstantiatedTail
        hasHaving := core.hasHaving
        hasNonRelevant := core.hasNonRelevant }
      let side :=
        (ResolvedValueCountSide.empty : ResolvedValueCountSide .token)
          |>.appendResolved resolved
      pure (evalValueCountAggregate (booleanValueCountToken expected) side)) := by
  rfl

/-- Each measured fixed Boolean-group computation specializes the shared complete addressed
    projection before applying canonical constant-specific token classification. -/
theorem checkedBooleanValueCountFixedGroup_checkedComputation_usesCompleteProjection
    (checked : CheckedBooleanValueCountFixedGroupSource model expected)
    (document : CheckedDocument model) (outer : Env) :
    checked.evaluateCheckedDocumentComputation document outer = (do
      let core ← document.resolveCheckedGroupEntityOperandCore outer
        checked.group.source.boundLevelCount checked.group.fields
      let resolved : ResolvedValueListSide .token := {
        cells := core.addressedCells.map fun addressed =>
          booleanValueCountCellAt .computation addressed.cell
        hasUninstantiatedTail := core.hasUninstantiatedTail
        hasHaving := core.hasHaving
        hasNonRelevant := core.hasNonRelevant }
      let side :=
        (ResolvedValueCountSide.empty : ResolvedValueCountSide .token)
          |>.appendResolved resolved
      pure (evalValueCountAggregate (booleanValueCountToken expected) side)) := by
  rfl

/-- A retained Boolean/Confirm group omits no descendant: every declaration in the recursive
    subtree is present in its certified expansion. -/
theorem checkedBooleanValueCountGroup_expansion_complete
    (group : CheckedBooleanValueCountGroup model expected)
    (declaration : FlatFieldDecl)
    (member : declaration ∈ model.groupSubtreeFields group.groupPath) :
    ∃ selected,
      declaration.toBooleanValueCountField? expected = some selected ∧
      selected ∈ group.fields := by
  have admitted :
      (declaration.toBooleanValueCountField? expected).isSome = true :=
    List.all_eq_true.mp group.expansionAllAllowed declaration member
  match hField : declaration.toBooleanValueCountField? expected with
  | none => rw [hField] at admitted; simp at admitted
  | some selected =>
      refine ⟨selected, rfl, ?_⟩
      have retained : selected ∈
          (model.groupSubtreeFields group.source.groupPath).filterMap
            (FlatFieldDecl.toBooleanValueCountField? expected) :=
        List.mem_filterMap.mpr ⟨declaration, member, hField⟩
      rw [group.expansionOwned] at retained
      simpa [CheckedBooleanValueCountGroup.fields] using retained

/-- A checked Boolean/Confirm group combines the shared recursive concrete extent with its separate
    hierarchical tail decision before projecting cached cells into the canonical token domain, and
    projects the group's declared-capacity extent rather than its complete formal-cell view. -/
theorem checkedBooleanValueCountGroup_resolvedCheckedValidationSide
    (group : CheckedBooleanValueCountGroup model expected)
    (document : CheckedDocument model) (outer : Env) :
    (CheckedBooleanValueCountOperand.group group).resolvedCheckedValidationSide
        document outer = (do
      let core ← document.resolveCheckedGroupEntityOperandCore outer
        group.source.boundLevelCount group.fields
      let hasUninstantiatedTail ←
        group.resolveCheckedUninstantiatedTail document outer
      pure {
        cells := core.inCapacityAddressedCells.map fun cell =>
          booleanValueCountCellAt .validation cell.cell
        hasUninstantiatedTail
        hasHaving := core.hasHaving
        hasNonRelevant := core.hasNonRelevant }) := by
  rfl

/-- An unfiltered checked Boolean star selects the in-capacity addressed cells before projecting
    their canonical tokens. -/
theorem checkedBooleanValueCount_plainBooleanStar_usesCapacityProjection
    (source : CheckedBooleanValueCountStarSource model expected)
    (document : CheckedDocument model) (outer : Env) :
    source.filter = none →
    source.source.declaration.policy.kind = .boolean →
    (CheckedBooleanValueCountOperand.star source).resolvedCheckedValidationSide
        document outer = (do
      let core ← source.source.resolveCheckedValidationEntityOperandCore
        document outer none
      pure {
        cells := core.inCapacityAddressedCells.map fun cell =>
          booleanValueCountCellAt .validation cell.cell
        hasUninstantiatedTail := core.hasUninstantiatedTail
        hasHaving := core.hasHaving
        hasNonRelevant := core.hasNonRelevant }) := by
  intro unfiltered boolean
  cases resolved : source.source.resolveCheckedValidationEntityOperandCore
      document outer none <;>
    simp [CheckedBooleanValueCountOperand.resolvedCheckedValidationSide,
      unfiltered, boolean, Except.map, resolved] <;>
    rfl

/-- Every declaration retained by an operand admitted under `False` is Boolean; Confirm is
    admitted only by `True`. This is list-valued because a group slot owns its whole expansion. -/
theorem checkedBooleanValueCount_false_fields_boolean
    (operand : CheckedBooleanValueCountOperand model false) :
    ∀ declaration ∈ operand.declarations,
      declaration.policy.kind = .boolean := by
  cases operand with
  | field source =>
      intro declaration member
      simp only [CheckedBooleanValueCountOperand.declarations,
        List.mem_singleton] at member
      subst declaration
      have allowed := source.kindAllowed
      cases kind : source.declaration.policy.kind <;>
        simp [booleanValueCountKindAllowed, kind] at allowed
      rfl
  | star source =>
      intro declaration member
      simp only [CheckedBooleanValueCountOperand.declarations,
        List.mem_singleton] at member
      subst declaration
      have allowed := source.kindAllowed
      cases kind : source.source.declaration.policy.kind <;>
        simp [booleanValueCountKindAllowed, kind] at allowed
      rfl
  | group source =>
      intro declaration member
      have retained : declaration ∈
          (model.groupSubtreeFields source.source.groupPath).filterMap
            (FlatFieldDecl.toBooleanValueCountField? false) := by
        rw [source.expansionOwned]
        simpa [CheckedBooleanValueCountOperand.declarations,
          CheckedBooleanValueCountGroup.fields] using member
      obtain ⟨original, _, selected⟩ := List.mem_filterMap.mp retained
      unfold FlatFieldDecl.toBooleanValueCountField? at selected
      split at selected
      case isTrue allowed =>
        cases selected
        cases kind : declaration.policy.kind <;>
          simp [booleanValueCountKindAllowed, kind] at allowed
        rfl
      case isFalse => simp at selected

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
