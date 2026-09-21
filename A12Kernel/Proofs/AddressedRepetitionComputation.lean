import A12Kernel.Elaboration.AddressedRepetitionComputation

namespace A12Kernel

/-- A unique lookup answers with the declaration carrying the id it was asked for. Needed because
    several admission arms name the source by id and report the *found* declaration's id, so without
    this the two are formally unrelated. -/
private theorem lookupUniqueId_id {model : FlatModel} {id : FieldId}
    {declaration : FlatFieldDecl} (found : model.lookupUniqueId id = .ok declaration) :
    declaration.id = id := by
  unfold FlatModel.lookupUniqueId at found
  split at found
  case h_1 => simp at found
  case h_2 filtered =>
    have member : declaration ∈ model.fields.filter (fun d => d.id == id) := by
      simp_all
    simpa using (List.mem_filter.mp member).2
  case h_3 => simp at found

/-- A certified conversion source's recovered declaration carries that source's own field id. -/
private theorem certifiedFieldValueAsNumberDeclaration_id {model : FlatModel}
    {source : ResolvedFieldValueAsNumberSource} {owned : FlatFieldDecl}
    (found : model.certifiedFieldValueAsNumberDeclaration? source = some owned) :
    owned.id = source.fieldId := by
  unfold FlatModel.certifiedFieldValueAsNumberDeclaration? at found
  split at found
  case h_1 => simp at found
  case h_2 declaration lookup =>
    split at found
    case h_1 => simp at found
    case h_2 =>
      split at found
      case isTrue => simp at found; subst found; exact lookupUniqueId_id lookup
      case isFalse => simp at found

/-- Neither endpoint of an admitted completed-period difference is the target itself. -/
private theorem admitsDateDifferenceEndpoint_not_target {model : FlatModel}
    {target : CheckedAddressedNumericTarget model} {operand : ResolvedDateDifferenceOperand}
    (admitted : target.admitsDateDifferenceEndpoint operand = true) :
    operand.references target.targetField = false := by
  cases operand with
  | baseYear _ _ => rfl
  | field source =>
      simp only [CheckedAddressedNumericTarget.admitsDateDifferenceEndpoint,
        CheckedAddressedNumericTarget.admitsSourceField] at admitted
      cases found : model.lookupUniqueId source.id with
      | error _ => simp [found] at admitted
      | ok owned =>
          simp [found] at admitted
          simp [ResolvedDateDifferenceOperand.references, admitted.1.2]

/-- A structural group containing the target does not create a self-dependency. Every real field
    dependency remains a separately certified atom, excluded from the target at admission. -/
theorem addressedRepetitionComputation_excludes_target
    (operation : CheckedAddressedRepetitionComputation model) :
    operation.referencesField operation.target.targetField = false := by
  let refers : AddressedRepetitionOperand operation.target → Bool := fun atom =>
    atom.val.referencesField model operation.target.targetField
  have absent (source : AddressedRepetitionOperand operation.target) : refers source = false := by
    rcases source with ⟨atom, admitted⟩
    simp only [refers, NumericComputationAtom.referencesField]
    -- Every field-bearing arm's admission is a `match` on the model lookup, so the split is what
    -- turns "this id is owned and is not the target" into a usable disequality.
    cases atom
    -- The conversion source names its field by id while admission reports the *found* declaration's
    -- id, so this arm needs the certificate's own identity rather than a split.
    case fieldValueAsNumber conversion =>
      simp only [CheckedAddressedNumericTarget.admitsRepetitionOperand] at admitted
      simp only [ResolvedNumericAtom.referencesFieldWith]
      cases found : model.certifiedFieldValueAsNumberDeclaration? conversion with
      | none => simp [found] at admitted
      | some owned =>
          simp [found] at admitted
          simp [← certifiedFieldValueAsNumberDeclaration_id found, admitted.1]
    -- Two endpoints, each carrying its own certificate, so the pair is closed by the endpoint lemma
    -- twice rather than by unfolding a single lookup.
    case dateDifference _ left right =>
      simp only [CheckedAddressedNumericTarget.admitsRepetitionOperand,
        Bool.and_eq_true] at admitted
      simp only [ResolvedNumericAtom.referencesFieldWith]
      simp [admitsDateDifferenceEndpoint_not_target admitted.1.2,
        admitsDateDifferenceEndpoint_not_target admitted.2]
    all_goals
      simp_all [CheckedAddressedNumericTarget.admitsRepetitionOperand,
        CheckedAddressedNumericTarget.admitsSourceField,
        ResolvedNumericAtom.referencesFieldWith] <;>
      (split at admitted <;> simp_all)
  have walk (expression : AuthoredNumericExpr (AddressedRepetitionOperand operation.target)) :
      expression.anyAtom refers = false := by
    induction expression <;> simp_all [AuthoredNumericExpr.anyAtom]
  exact walk operation.expression

/-- A checked completed-period difference reads no cell outside the target's row binding, on
    **either** endpoint. The pair gate is what makes this worth stating separately from the
    single-field rule: a two-operand source can satisfy its own component agreement while one
    endpoint sits on an unbound level, and this rules that out for both positions at once. The
    Base-Year endpoint reads nothing, so it carries no obligation and none is claimed for it. -/
theorem addressedRepetitionComputation_differenceEndpoints_rowBound
    {model : FlatModel} {target : CheckedAddressedNumericTarget model}
    {unit : DateDifferenceUnit} {left right : ResolvedDateDifferenceOperand}
    (admitted : target.admitsRepetitionOperand (.dateDifference unit left right) = true)
    {source : FlatTemporalField} (endpoint : left = .field source ∨ right = .field source) :
    ∃ owned, model.lookupUniqueId source.id = .ok owned ∧
      owned.repetitionBoundBy target.targetDeclaration.repeatableScope = true := by
  have bound : ∀ operand : ResolvedDateDifferenceOperand, operand = .field source →
      target.admitsDateDifferenceEndpoint operand = true →
      ∃ owned, model.lookupUniqueId source.id = .ok owned ∧
        owned.repetitionBoundBy target.targetDeclaration.repeatableScope = true := by
    rintro _ rfl endpointAdmitted
    simp only [CheckedAddressedNumericTarget.admitsDateDifferenceEndpoint,
      CheckedAddressedNumericTarget.admitsSourceField] at endpointAdmitted
    cases owned : model.lookupUniqueId source.id with
    | error _ => simp [owned] at endpointAdmitted
    | ok declaration =>
        refine ⟨declaration, rfl, ?_⟩
        simp [owned] at endpointAdmitted
        exact endpointAdmitted.2
  simp only [CheckedAddressedNumericTarget.admitsRepetitionOperand, Bool.and_eq_true] at admitted
  rcases endpoint with rfl | rfl
  · exact bound _ rfl admitted.1.2
  · exact bound _ rfl admitted.2

end A12Kernel
