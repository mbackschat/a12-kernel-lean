import A12Kernel.Elaboration.CheckedRequired
import A12Kernel.Proofs.Required

/-! # A12Kernel.Proofs.Elaboration — checked flat-elaboration invariants

These theorems eliminate certificates carried by checked values and connect the resolved model declaration to the policy used to check runtime cells. The latter closes the previously admitted boundary between typed core references and caller-supplied checked cells.
-/

namespace A12Kernel

/-- An explicit turning-point label contributes exactly one equality guard on the group reached by parent walking; it cannot search another ancestor or alter the path. -/
theorem groupPath_matchesTurningPoint_some_iff
    (group : GroupPath) (name : String) :
    group.matchesTurningPoint (some name) = true ↔
      group.getLast? = some name := by
  simp [GroupPath.matchesTurningPoint]

/-- Once that equality guard is established, retaining or erasing the authored label has the same resolution-side observation. -/
theorem groupPath_matchingTurningPoint_is_transparent
    (group : GroupPath) (name : String)
    (matching : group.getLast? = some name) :
    group.matchesTurningPoint (some name) =
      group.matchesTurningPoint none := by
  simp [GroupPath.matchesTurningPoint, matching]

/-- Canonical quote reification is accepted for one exact name and erases only its syntax marker. -/
theorem authoredPathName_reified_lower
    (profile : PathKeywordProfile) (name : String) :
    (profile.reifyName name).lower profile = .ok name := by
  unfold PathKeywordProfile.reifyName AuthoredPathName.lower
  cases profile.requiresQuote name <;> rfl

private theorem authoredPathNames_reified_lower
    (profile : PathKeywordProfile) (names : List String) :
    (names.map profile.reifyName).mapM (·.lower profile) = .ok names := by
  induction names with
  | nil => rfl
  | cons name remaining inductionHypothesis =>
      simp only [List.map_cons, List.mapM_cons]
      rw [authoredPathName_reified_lower, inductionHypothesis]
      rfl

/-- Canonical quote reification and quote validation form a left inverse on every structured field path. -/
theorem surfaceFieldPath_reifyQuotes_lower
    (profile : PathKeywordProfile) (path : SurfaceFieldPath) :
    (path.reifyQuotes profile).lower profile = .ok path := by
  cases path with
  | mk base turningPoint groups field =>
      cases turningPoint with
      | none =>
          unfold SurfaceFieldPath.reifyQuotes AuthoredFieldPath.lower
          rw [authoredPathNames_reified_lower,
            authoredPathName_reified_lower]
          rfl
      | some turningPoint =>
          simp only [SurfaceFieldPath.reifyQuotes, Option.map_some,
            AuthoredFieldPath.lower]
          rw [authoredPathName_reified_lower,
            authoredPathNames_reified_lower,
            authoredPathName_reified_lower]
          rfl

/-- An exact selected-language keyword without the grammar's quote marker fails before name lookup. -/
theorem authoredPathName_unquoted_reserved
    (profile : PathKeywordProfile) (name : String)
    (reserved : profile.requiresQuote name = true) :
    ({ text := name } : AuthoredPathName).lower profile =
      .error (.unquotedKeyword name) := by
  simp [AuthoredPathName.lower, reserved]

/-- Canonically reified quote syntax delegates to the existing resolver without changing path identity or diagnostics. -/
theorem resolveAuthoredField_reified_delegates
    (model : FlatModel) (profile : PathKeywordProfile)
    (declaringGroup : GroupPath) (path : SurfaceFieldPath) :
    model.resolveAuthoredField profile declaringGroup
      (path.reifyQuotes profile) =
        (model.resolveField declaringGroup path).mapError .resolve := by
  unfold FlatModel.resolveAuthoredField
  rw [surfaceFieldPath_reifyQuotes_lower]
  rfl

/-- Eliminate the core static-legality certificate carried by a checked flat condition. -/
theorem checkedFlatCondition_wellFormed (checked : CheckedFlatCondition model) :
    checked.core.WellFormed model :=
  checked.wellFormed

/-- Eliminate the model-validity certificate carried by a checked flat condition. -/
theorem checkedFlatCondition_modelWellFormed (checked : CheckedFlatCondition model) :
    model.validate.isOk = true :=
  checked.modelWellFormed

/-- Surface elaboration retains its exact declaring group in the checked certificate. -/
theorem elaborate_checkedFlatCondition_rowGroup
    (model : FlatModel) (declaringGroup : GroupPath)
    (condition : SurfaceCondition) (checked : CheckedFlatCondition model)
    (elaborated : elaborate model declaringGroup condition = .ok checked) :
    checked.rowGroup = declaringGroup := by
  unfold elaborate at elaborated
  split at elaborated
  · contradiction
  · simp only [bind, Except.bind] at elaborated
    split at elaborated
    · contradiction
    · unfold FlatCondition.checkAgainstValidatedModel at elaborated
      split at elaborated
      · cases elaborated
        rfl
      · contradiction

/-- A field admitted by the core well-formedness check has a unique model declaration
    with the same typed field representation and no repeatable scope. -/
theorem admitsField_has_unique_matching_declaration (model : FlatModel) (field : FlatField)
    (admitted : model.admitsField field = true) :
    ∃ declaration,
      model.lookupUniqueId field.id = .ok declaration ∧
      declaration.repeatableScope.isEmpty = true ∧
      field.matchesDecl declaration = true := by
  unfold FlatModel.admitsField at admitted
  generalize lookupEq : model.lookupUniqueId field.id = lookup at admitted
  cases lookup with
  | error error => simp at admitted
  | ok declaration =>
      refine ⟨declaration, rfl, ?_⟩
      cases nonrepeatable : declaration.repeatableScope.isEmpty <;>
        cases matching : field.matchesDecl declaration <;> simp_all

/-- A resolved direct textual profile is available only for a field admitted by the shared typed-field gate. -/
theorem directComparableProfile_admitsField (model : FlatModel)
    (operand : FlatTextFieldOperand) (profile : DirectComparableField)
    (resolved : model.directComparableFor? operand = some profile) :
    model.admitsField operand.field = true := by
  unfold FlatModel.directComparableFor? at resolved
  unfold FlatModel.admitsField
  split at resolved <;> simp_all

/-- A reconstructed checked Enumeration operand necessarily passes the shared typed-field gate. -/
theorem checkedEnumerationOperand_admitsField (model : FlatModel)
    (operand : FlatEnumerationOperand) (checked : CheckedEnumerationProjection)
    (resolved : model.checkedEnumerationOperand? operand = some checked) :
    model.admitsField (.enumeration operand.field) = true := by
  unfold FlatModel.checkedEnumerationOperand? at resolved
  generalize lookupEq : model.lookupUniqueId operand.field.id = lookup at resolved
  cases lookup with
  | error error => simp at resolved
  | ok declaration =>
      generalize gateEq : (declaration.repeatableScope.isEmpty &&
        (FlatField.enumeration operand.field).matchesDecl declaration) = gate at resolved
      cases gate with
      | false => simp [gateEq] at resolved
      | true =>
          simpa [FlatModel.admitsField, FlatField.id, lookupEq] using gateEq

/-- Value-reading admission strengthens, rather than replaces, ordinary String presence admission. -/
theorem admitsStringValueField_admitsField (model : FlatModel)
    (field : FlatStringField)
    (admitted : model.admitsStringValueField field = true) :
    model.admitsField (.string field) = true := by
  unfold FlatModel.admitsStringValueField at admitted
  unfold FlatModel.admitsField
  generalize lookupEq : model.lookupUniqueId field.id = lookup at admitted ⊢
  cases lookup with
  | error error => simp at admitted
  | ok declaration =>
      cases kindEq : declaration.policy.kind <;>
        cases modeEq : declaration.stringValueMode
      all_goals try simp_all [FlatFieldDecl.toStringValueField?,
        FlatFieldDecl.toPresenceField, FlatField.matchesDecl, FlatField.id]

/-- Every field read by an admitted comparison independently passes the shared typed-field admission check. -/
theorem admitsComparison_fields_admitted (model : FlatModel)
    (comparison : FlatComparison) (admitted : model.admitsComparison comparison = true) :
    ∀ field, field ∈ comparison.fields → model.admitsField field = true := by
  intro field member
  cases comparison with
  | number op target expected =>
      rcases List.mem_singleton.mp member with rfl
      simpa [FlatModel.admitsComparison, FlatComparison.fields,
        List.all_eq_true] using admitted
  | boolean op target expected =>
      rcases List.mem_singleton.mp member with rfl
      simpa [FlatModel.admitsComparison, FlatComparison.fields,
        List.all_eq_true] using admitted
  | string op target expected =>
      rcases List.mem_singleton.mp member with rfl
      exact admitsStringValueField_admitsField model target (by
        simpa [FlatModel.admitsComparison] using admitted)
  | stringLength op target expected =>
      rcases List.mem_singleton.mp member with rfl
      exact admitsStringValueField_admitsField model target (by
        simpa [FlatModel.admitsComparison] using admitted)
  | confirm op target =>
      rcases List.mem_singleton.mp member with rfl
      simpa [FlatModel.admitsComparison, FlatComparison.fields,
        List.all_eq_true] using admitted
  | enumeration op operand expected =>
      rcases List.mem_singleton.mp member with rfl
      unfold FlatModel.admitsComparison at admitted
      generalize resolved : model.checkedEnumerationOperand? operand = checked at admitted
      cases checked with
      | none => simp [resolved] at admitted
      | some checked =>
          exact checkedEnumerationOperand_admitsField model operand checked resolved
  | textFields op left right =>
      unfold FlatModel.admitsComparison at admitted
      generalize leftEq : model.directComparableFor? left = leftProfile at admitted
      generalize rightEq : model.directComparableFor? right = rightProfile at admitted
      cases leftProfile <;> cases rightProfile <;> simp_all
      simp [FlatComparison.fields] at member
      rcases member with rfl | rfl
      · exact directComparableProfile_admitsField model left _ leftEq
      · exact directComparableProfile_admitsField model right _ rightEq
  | temporal op left right =>
      simp [FlatModel.admitsComparison, List.all_eq_true] at admitted
      exact admitted.2 field member

/-- Model-derived context construction checks a resolved cell with exactly the policy
    carried by its unique declaration. -/
theorem checkContext_lookup_coherent (model : FlatModel) (raw : RawFlatContext)
    (id : FieldId) (declaration : FlatFieldDecl)
    (lookup : model.lookupUniqueId id = .ok declaration) :
    (model.checkContext raw).read id = declaration.checkRaw (raw.read id) := by
  simp only [FlatModel.checkContext, lookup]

/-- A core-admitted reference therefore reads a cell checked by a unique matching model
    declaration, rather than by caller-supplied field metadata. -/
theorem checkContext_admittedField_coherent (model : FlatModel) (raw : RawFlatContext)
    (field : FlatField) (admitted : model.admitsField field = true) :
    ∃ declaration,
      model.lookupUniqueId field.id = .ok declaration ∧
      declaration.repeatableScope.isEmpty = true ∧
      field.matchesDecl declaration = true ∧
      (model.checkContext raw).read field.id = declaration.checkRaw (raw.read field.id) := by
  obtain ⟨declaration, lookup, nonrepeatable, matching⟩ :=
    admitsField_has_unique_matching_declaration model field admitted
  exact ⟨declaration, lookup, nonrepeatable, matching,
    checkContext_lookup_coherent model raw field.id declaration lookup⟩

/-- Every field read by a core-admitted comparison therefore receives the policy of its own unique compatible declaration. -/
theorem checkContext_admittedComparison_field_coherent (model : FlatModel)
    (raw : RawFlatContext) (comparison : FlatComparison)
    (admitted : model.admitsComparison comparison = true)
    (field : FlatField) (member : field ∈ comparison.fields) :
    ∃ declaration,
      model.lookupUniqueId field.id = .ok declaration ∧
      declaration.repeatableScope.isEmpty = true ∧
      field.matchesDecl declaration = true ∧
      (model.checkContext raw).read field.id = declaration.checkRaw (raw.read field.id) := by
  exact checkContext_admittedField_coherent model raw field
    (admitsComparison_fields_admitted model comparison admitted field member)

/-- Missing or ambiguous identifiers fail closed at the raw-to-checked boundary. -/
theorem checkContext_lookup_error_is_malformed (model : FlatModel) (raw : RawFlatContext)
    (id : FieldId) (error : ResolveError)
    (lookup : model.lookupUniqueId id = .error error) :
    (model.checkContext raw).read id = malformedCheckedCell := by
  simp only [FlatModel.checkContext, lookup]

/-- The fail-closed cell has the ordinary validation face of malformed input. -/
theorem checkContext_lookup_error_observes_unknown (model : FlatModel)
    (raw : RawFlatContext) (id : FieldId) (error : ResolveError)
    (lookup : model.lookupUniqueId id = .error error) :
    (model.checkContext raw).observeValidationAt id = .unknown .malformed := by
  simp [FlatContext.observeValidationAt, checkContext_lookup_error_is_malformed,
    lookup, malformedCheckedCell, observeCell]

namespace DocumentData

@[simp] theorem toDocument_instantiatedRows (data : DocumentData) :
    data.toDocument.instantiatedRows = data.instantiatedRows := rfl

end DocumentData

namespace CheckedDocument

theorem model_is_well_formed
    (checked : CheckedDocument model) :
    model.validate.isOk = true :=
  checked.modelWellFormed

theorem groupPresenceInput_preserves_relevance
    (checked : CheckedDocument model) (groupPath : GroupPath)
    (environment : Env) (relevance : GroupRelevance)
    (structuralError : Bool) :
    (checked.groupPresenceInput groupPath environment relevance structuralError).map
        (fun input => input.relevance) =
      (checked.groupPresenceInput groupPath environment relevance structuralError).map
        (fun _ => relevance) := by
  cases result :
      checked.groupPresenceInput groupPath environment relevance structuralError with
  | error error => rfl
  | ok input =>
      simp only [Except.map]
      unfold CheckedDocument.groupPresenceInput at result
      unfold CheckedDocument.groupPresenceInputFromCells at result
      unfold CheckedDocument.groupPresenceInputFromSlice at result
      split at result
      · contradiction
      · split at result
        · contradiction
        · injection result with result
          subst input
          rfl

/-- Parent-relative requiredness retains the exact declared parent group as its gate. -/
@[simp] theorem requirednessScopeFor_relativeToParent
    (model : FlatModel) (declaration : FlatFieldDecl) :
    model.requirednessScopeFor {
      declaration with requiredness := some .relativeToParent
    } = .ok (some (.relativeTo declaration.groupPath)) := by
  rfl

/-- The default requiredness mode is genuinely absolute when no repeatable ancestor exists. -/
theorem requirednessScopeFor_absolute
    (model : FlatModel) (declaration : FlatFieldDecl)
    (nonrepeatable : declaration.repeatableScope = []) :
    model.requirednessScopeFor {
      declaration with
      requiredness := some .absoluteOrNearestRepeatableAncestor
    } = .ok (some .absolute) := by
  simp [FlatModel.requirednessScopeFor, nonrepeatable]

/-- The same default mode retains the nearest repeatable ancestor rather than collapsing a repeatable field to an unsupported reference. -/
theorem requirednessScopeFor_nearestRepeatable
    (model : FlatModel) (declaration : FlatFieldDecl)
    (level : RepeatableLevel) (group : RepeatableGroupDecl)
    (nearest : declaration.repeatableScope.getLast? = some level)
    (resolved : model.repeatableGroupAtLevel? level = some group) :
    model.requirednessScopeFor {
      declaration with
      requiredness := some .absoluteOrNearestRepeatableAncestor
    } = .ok (some (.relativeTo group.path)) := by
  simp [FlatModel.requirednessScopeFor, nearest, resolved]

/-- The model-certified required adapter preserves the base computation observation while returning its separate authored-validation view. -/
theorem applyAbsoluteRequiredAt_preserves_computation
    (checked : CheckedDocument model) (field id : FieldId) :
    (checked.applyAbsoluteRequiredAt field).map
        (fun result =>
          observeCell .computation (result.authoredContext.read id)) =
      (checked.applyAbsoluteRequiredAt field).map
        (fun _ => observeCell .computation (checked.flatContext.read id)) := by
  unfold CheckedDocument.applyAbsoluteRequiredAt
  generalize declarationEq : model.lookupUniqueId field = declarationResult
  cases declarationResult with
  | error error => rfl
  | ok declaration =>
      simp only [Except.mapError, bind, Except.bind]
      generalize scopeEq :
        model.requirednessScopeFor declaration = scopeResult
      cases scopeResult with
      | error error => rfl
      | ok scope =>
          cases scope with
          | none => rfl
          | some scope =>
              cases scope with
              | absolute =>
                  simp only [Except.map]
                  exact congrArg Except.ok
                    (applyAbsoluteRequired_preserves_computation
                      declaration.toPresenceField checked.flatContext id)
              | relativeTo groupPath => rfl

end CheckedDocument

end A12Kernel
