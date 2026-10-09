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

/-- A certified conversion source's recovered declaration is the one a unique lookup on that
    source's own field id answers with. The id equality alone is weaker than every consumer needs:
    the row-bound law has to reach the *lookup*, because that is what carries the binding. -/
private theorem certifiedFieldValueAsNumberDeclaration_lookup {model : FlatModel}
    {source : ResolvedFieldValueAsNumberSource} {owned : FlatFieldDecl}
    (found : model.certifiedFieldValueAsNumberDeclaration? source = some owned) :
    model.lookupUniqueId source.fieldId = .ok owned := by
  unfold FlatModel.certifiedFieldValueAsNumberDeclaration? at found
  split at found
  case h_1 => simp at found
  case h_2 declaration lookup =>
    split at found
    case h_1 => simp at found
    case h_2 =>
      split at found
      case isTrue => simp at found; subst found; exact lookup
      case isFalse => simp at found

private theorem certifiedFieldValueAsNumberDeclaration_id {model : FlatModel}
    {source : ResolvedFieldValueAsNumberSource} {owned : FlatFieldDecl}
    (found : model.certifiedFieldValueAsNumberDeclaration? source = some owned) :
    owned.id = source.fieldId :=
  lookupUniqueId_id (certifiedFieldValueAsNumberDeclaration_lookup found)

/-- An admitted source id is not the target's own field. The row-bound half of the same certificate
    is stated separately below, because the two theorems here need opposite halves of it. -/
theorem admitsSourceField_notTarget {model : FlatModel}
    {target : CheckedAddressedNumericTarget model} {id : FieldId} {certify : FlatFieldDecl → Bool}
    (admitted : target.admitsSourceField id certify = true) :
    (id == target.targetField) = false := by
  simp only [CheckedAddressedNumericTarget.admitsSourceField] at admitted
  cases found : model.lookupUniqueId id with
  | error _ => simp [found] at admitted
  | ok _ => simp [found] at admitted; simpa using admitted.1.2

/-- A direct field list references only members the shared scope rule certified. The list walk is
    done once here because the self-exclusion and row-binding theorems consume different halves of
    that certificate. -/
private theorem admitsAggregateMember {model : FlatModel}
    {target : CheckedAddressedNumericTarget model} {source : ResolvedNumericAggregateFields}
    (admitted : source.fields.all (fun field =>
      target.admitsSourceField field.id fun owned => owned.toNumberField? == some field) = true)
    {field : FieldId} (referenced : source.referencesField field = true) :
    ∃ member : FlatNumberField, member.id = field ∧
      target.admitsSourceField member.id
        (fun owned => owned.toNumberField? == some member) = true := by
  simp only [ResolvedNumericAggregateFields.referencesField, List.any_eq_true] at referenced
  obtain ⟨member, mem, isField⟩ := referenced
  exact ⟨member, by simpa using isField, (List.all_eq_true.mp admitted) member mem⟩

/-- Neither endpoint of an admitted completed-period difference is the target itself. -/
private theorem admitsDateDifferenceEndpoint_not_target {model : FlatModel}
    {target : CheckedAddressedNumericTarget model} {operand : ResolvedDateDifferenceOperand}
    (admitted : target.admitsDateDifferenceEndpoint operand = true) :
    operand.references target.targetField = false := by
  cases operand with
  | baseYear _ _ | literal _ _ | today _ => rfl
  | field source =>
      simp only [CheckedAddressedNumericTarget.admitsDateDifferenceEndpoint,
        CheckedAddressedNumericTarget.admitsSourceField] at admitted
      cases found : model.lookupUniqueId source.id with
      | error _ => simp [found] at admitted
      | ok owned =>
          simp [found] at admitted
          simp [ResolvedDateDifferenceOperand.references, admitted.1.2]

/-- Neither endpoint of an admitted sub-day difference is the target itself. -/
private theorem admitsSubdayEndpoint_not_target {model : FlatModel}
    {target : CheckedAddressedNumericTarget model} {operand : FlatTemporalOperand}
    (admitted : target.admitsSubdayEndpoint operand = true) :
    operand.dateTimeDifferenceReferences target.targetField = false := by
  cases operand
  case fieldValue source =>
    simp only [CheckedAddressedNumericTarget.admitsSubdayEndpoint,
      CheckedAddressedNumericTarget.admitsSourceField] at admitted
    cases found : model.lookupUniqueId source.id with
    | error _ => simp [found] at admitted
    | ok owned =>
        simp [found] at admitted
        simpa [FlatTemporalOperand.dateTimeDifferenceReferences, FlatTemporalOperand.fields, FlatTemporalOperand.fieldValues,
          FlatField.id] using admitted.1.2
  all_goals simp [CheckedAddressedNumericTarget.admitsSubdayEndpoint] at admitted

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
    case dayDifference _ left right =>
      simp only [CheckedAddressedNumericTarget.admitsRepetitionOperand,
        Bool.and_eq_true] at admitted
      simp only [ResolvedNumericAtom.referencesFieldWith]
      simp [admitsDateDifferenceEndpoint_not_target admitted.1.2,
        admitsDateDifferenceEndpoint_not_target admitted.2]
    case dateTimeDifference _ left right =>
      simp only [CheckedAddressedNumericTarget.admitsRepetitionOperand] at admitted
      simp only [ResolvedNumericAtom.referencesFieldWith]
      split at admitted
      case h_1 =>
        simp only [Bool.and_eq_true] at admitted
        simp [admitsSubdayEndpoint_not_target admitted.1.2,
          admitsSubdayEndpoint_not_target admitted.2]
      case h_2 => simp at admitted
    case aggregate _ source =>
      simp only [CheckedAddressedNumericTarget.admitsRepetitionOperand,
        Bool.and_eq_true] at admitted
      simp only [ResolvedNumericAtom.referencesFieldWith]
      cases referenced : source.referencesField operation.target.targetField with
      | false => rfl
      | true =>
          obtain ⟨_, isField, member⟩ :=
            admitsAggregateMember (by simpa using admitted.2) referenced
          simp [isField] at member
          simpa using admitsSourceField_notTarget member
    all_goals
      simp_all [CheckedAddressedNumericTarget.admitsRepetitionOperand,
        CheckedAddressedNumericTarget.admitsSourceField,
        ResolvedNumericAtom.referencesFieldWith] <;>
      (split at admitted <;> simp_all)
  have walk (expression : AuthoredNumericExpr (AddressedRepetitionOperand operation.target)) :
      expression.anyAtom refers = false := by
    induction expression <;> simp_all [AuthoredNumericExpr.anyAtom]
  exact walk operation.expression

/-- The scope rule's own consequence: whatever else a caller certifies, an admitted source id names a
    model-owned declaration the target's repeatable scope binds. Every arm that reads a cell reaches
    this predicate, so the universal law below is its walk, not a second argument. -/
theorem admitsSourceField_rowBound {model : FlatModel}
    {target : CheckedAddressedNumericTarget model} {id : FieldId} {certify : FlatFieldDecl → Bool}
    (admitted : target.admitsSourceField id certify = true) :
    ∃ owned, model.lookupUniqueId id = .ok owned ∧
      owned.repetitionBoundBy target.targetDeclaration.repeatableScope = true := by
  simp only [CheckedAddressedNumericTarget.admitsSourceField] at admitted
  cases found : model.lookupUniqueId id with
  | error _ => simp [found] at admitted
  | ok declaration =>
      refine ⟨declaration, rfl, ?_⟩
      simp [found] at admitted
      exact admitted.2

/-- An admitted completed-period or day endpoint that reads a field reads a row-bound one. The
    Base-Year endpoint reads nothing, which is why the hypothesis is the reference rather than the
    constructor: an unreferenced endpoint carries no obligation and none is claimed. -/
private theorem admitsDateDifferenceEndpoint_rowBound {model : FlatModel}
    {target : CheckedAddressedNumericTarget model} {operand : ResolvedDateDifferenceOperand}
    {field : FieldId} (admitted : target.admitsDateDifferenceEndpoint operand = true)
    (referenced : operand.references field = true) :
    ∃ owned, model.lookupUniqueId field = .ok owned ∧
      owned.repetitionBoundBy target.targetDeclaration.repeatableScope = true := by
  cases operand with
  | baseYear _ _ | literal _ _ | today _ => simp [ResolvedDateDifferenceOperand.references] at referenced
  | field source =>
      simp only [ResolvedDateDifferenceOperand.references] at referenced
      cases (by simpa using referenced : source.id = field)
      exact admitsSourceField_rowBound admitted

private theorem admitsSubdayEndpoint_rowBound {model : FlatModel}
    {target : CheckedAddressedNumericTarget model} {operand : FlatTemporalOperand}
    {field : FieldId} (admitted : target.admitsSubdayEndpoint operand = true)
    (referenced : operand.dateTimeDifferenceReferences field = true) :
    ∃ owned, model.lookupUniqueId field = .ok owned ∧
      owned.repetitionBoundBy target.targetDeclaration.repeatableScope = true := by
  cases operand
  case fieldValue source =>
    simp only [FlatTemporalOperand.dateTimeDifferenceReferences, FlatTemporalOperand.fields, FlatTemporalOperand.fieldValues,
      FlatField.id] at referenced
    cases (by simpa using referenced : source.id = field)
    exact admitsSourceField_rowBound admitted
  all_goals simp [CheckedAddressedNumericTarget.admitsSubdayEndpoint] at admitted

/-- **Every field an admitted operand reads is bound by the target's own repeatable scope.** This is
    the statement the per-atom certification exists for, and stating it once over the dependency walk
    replaces the per-family versions: the two-endpoint families need no separate law, because a pair
    that satisfies its own component agreement while one endpoint sits on an unbound level is already
    excluded here, in whichever position it sits. Constants read nothing and structural repetition
    references carry a path rather than a field, so both are vacuous rather than exceptions. -/
theorem admitsRepetitionOperand_rowBound {model : FlatModel}
    {target : CheckedAddressedNumericTarget model} {atom : NumericComputationAtom}
    {field : FieldId} (admitted : target.admitsRepetitionOperand atom = true)
    (referenced : atom.referencesField model field = true) :
    ∃ owned, model.lookupUniqueId field = .ok owned ∧
      owned.repetitionBoundBy target.targetDeclaration.repeatableScope = true := by
  simp only [NumericComputationAtom.referencesField,
    ResolvedNumericAtom.referencesFieldWith] at referenced
  cases atom
  -- The plain field arm carries its own declaration rather than reaching the shared predicate, so
  -- the model-owned one has to be recovered from the equality the arm certifies.
  case field declaration =>
    simp only [CheckedAddressedNumericTarget.admitsRepetitionOperand] at admitted
    cases found : model.lookupUniqueId declaration.id with
    | error _ => simp [found] at admitted
    | ok owned =>
        simp only [found, Bool.and_eq_true, beq_iff_eq] at admitted
        cases (by simpa using referenced : declaration.id = field)
        exact ⟨owned, found, by simpa [admitted.1.1.1] using admitted.2⟩
  case fieldValueAsNumber source =>
    simp only [CheckedAddressedNumericTarget.admitsRepetitionOperand] at admitted
    cases found : model.certifiedFieldValueAsNumberDeclaration? source with
    | none => simp [found] at admitted
    | some owned =>
        simp only [found, Bool.and_eq_true] at admitted
        cases (by simpa using referenced : source.fieldId = field)
        exact ⟨owned, certifiedFieldValueAsNumberDeclaration_lookup found, admitted.2⟩
  case dateDifference _ left right =>
    simp only [CheckedAddressedNumericTarget.admitsRepetitionOperand,
      Bool.and_eq_true] at admitted
    rcases Bool.or_eq_true _ _ |>.mp referenced with reads | reads
    · exact admitsDateDifferenceEndpoint_rowBound admitted.1.2 reads
    · exact admitsDateDifferenceEndpoint_rowBound admitted.2 reads
  case dayDifference _ left right =>
    simp only [CheckedAddressedNumericTarget.admitsRepetitionOperand,
      Bool.and_eq_true] at admitted
    rcases Bool.or_eq_true _ _ |>.mp referenced with reads | reads
    · exact admitsDateDifferenceEndpoint_rowBound admitted.1.2 reads
    · exact admitsDateDifferenceEndpoint_rowBound admitted.2 reads
  case dateTimeDifference _ left right =>
    simp only [CheckedAddressedNumericTarget.admitsRepetitionOperand] at admitted
    split at admitted
    case h_2 => simp at admitted
    case h_1 =>
      simp only [Bool.and_eq_true] at admitted
      rcases Bool.or_eq_true _ _ |>.mp referenced with reads | reads
      · exact admitsSubdayEndpoint_rowBound admitted.1.2 reads
      · exact admitsSubdayEndpoint_rowBound admitted.2 reads
  case aggregate _ source =>
    simp only [CheckedAddressedNumericTarget.admitsRepetitionOperand, Bool.and_eq_true] at admitted
    obtain ⟨_, isField, member⟩ := admitsAggregateMember (by simpa using admitted.2) referenced
    subst isField
    exact admitsSourceField_rowBound member
  -- The four arms that reach the shared predicate directly. Their certify closures differ, which is
  -- exactly what the predicate abstracts over, so each is one rewrite plus the shared law.
  case stringLength source =>
    cases (by simpa using referenced : source.id = field)
    simp only [CheckedAddressedNumericTarget.admitsRepetitionOperand] at admitted
    exact admitsSourceField_rowBound admitted
  case stringRange source _ _ =>
    cases (by simpa using referenced : source.id = field)
    simp only [CheckedAddressedNumericTarget.admitsRepetitionOperand, Bool.and_eq_true] at admitted
    exact admitsSourceField_rowBound admitted.2
  case dateRangeBoundPart source _ _ =>
    cases (by simpa using referenced : source.id = field)
    simp only [CheckedAddressedNumericTarget.admitsRepetitionOperand] at admitted
    exact admitsSourceField_rowBound admitted
  case temporalFieldPart source _ _ =>
    cases (by simpa using referenced : source.id = field)
    simp only [CheckedAddressedNumericTarget.admitsRepetitionOperand] at admitted
    exact admitsSourceField_rowBound admitted
  -- Constants and structural references reference nothing; aggregates and group counts are refused
  -- outright, so every remaining arm is closed by one of its two hypotheses being absurd.
  all_goals simp_all [CheckedAddressedNumericTarget.admitsRepetitionOperand]

/-- A checked repetition computation reads no cell outside its target's row binding, anywhere in its
    expression. Together with the self-exclusion law above this closes the addressing question an
    Analyze consumer actually asks of this carrier: the dependency edges it reports are exactly
    row-local fields other than the target. -/
theorem addressedRepetitionComputation_rowBound
    (operation : CheckedAddressedRepetitionComputation model) {field : FieldId}
    (referenced : operation.referencesField field = true) :
    ∃ owned, model.lookupUniqueId field = .ok owned ∧
      owned.repetitionBoundBy operation.target.targetDeclaration.repeatableScope = true := by
  have walk : ∀ expression : AuthoredNumericExpr (AddressedRepetitionOperand operation.target),
      expression.anyAtom (fun atom => atom.val.referencesField model field) = true →
      ∃ owned, model.lookupUniqueId field = .ok owned ∧
        owned.repetitionBoundBy operation.target.targetDeclaration.repeatableScope = true := by
    intro expression
    induction expression with
    | atom source =>
        intro reads
        exact admitsRepetitionOperand_rowBound source.property
          (by simpa [AuthoredNumericExpr.anyAtom] using reads)
    | literal _ => intro reads; simp [AuthoredNumericExpr.anyAtom] at reads
    | binary _ _ _ leftBound rightBound | power _ _ leftBound rightBound
    | extremum _ _ _ leftBound rightBound =>
        intro reads
        rcases Bool.or_eq_true _ _ |>.mp (by simpa [AuthoredNumericExpr.anyAtom] using reads)
          with reads | reads
        · exact leftBound reads
        · exact rightBound reads
    | group _ bound => intro reads; exact bound (by simpa [AuthoredNumericExpr.anyAtom] using reads)
    | abs _ bound => intro reads; exact bound (by simpa [AuthoredNumericExpr.anyAtom] using reads)
    | extremumCall _ _ bound =>
        intro reads; exact bound (by simpa [AuthoredNumericExpr.anyAtom] using reads)
    | round _ _ _ bound =>
        intro reads; exact bound (by simpa [AuthoredNumericExpr.anyAtom] using reads)
  exact walk operation.expression
    (by simpa [CheckedAddressedRepetitionComputation.referencesField] using referenced)

end A12Kernel
