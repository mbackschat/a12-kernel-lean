import A12Kernel.Proofs.EnumerationValueList
import A12Kernel.Proofs.FlatNumberValueList
import A12Kernel.Proofs.ValueList
import A12Kernel.Semantics.PartialValidation

/-! # A12Kernel.Proofs.PartialValidation — flat relevance laws

These laws characterize only the admitted nonrepeatable rule instance and its supplied rule-level filter marker. The filter gate precedes the independent error-field and condition-leaf relevance decisions; no theorem derives that marker or lifts the flat predicate to groups, wildcard repetitions, aggregates, or whole-document validation.
-/

namespace A12Kernel

private def Verdict.truth : Verdict → K
  | .notFired => .fls
  | .fired _ => .tru
  | .unknown => .unknown

private theorem Verdict.truth_conj (left right : Verdict) :
    truth (conj left right) = K.and (truth left) (truth right) := by
  cases left <;> cases right <;> simp [truth, conj, K.and]
  case fired.fired leftPolarity rightPolarity =>
    cases leftPolarity <;> cases rightPolarity <;> rfl

private theorem Verdict.truth_disj (left right : Verdict) :
    truth (disj left right) = K.or (truth left) (truth right) := by
  cases left <;> cases right <;> simp [truth, disj, K.or]
  case notFired.fired polarity | fired.notFired polarity |
      fired.unknown polarity | unknown.fired polarity => cases polarity <;> rfl
  case fired.fired leftPolarity rightPolarity =>
      cases leftPolarity <;> cases rightPolarity <;> rfl

private theorem Verdict.truth_eq_tru_iff (verdict : Verdict) :
    truth verdict = .tru ↔ ∃ polarity, verdict = .fired polarity := by
  cases verdict <;> simp [truth]

private theorem K.and_eq_tru_iff (left right : K) :
    K.and left right = .tru ↔ left = .tru ∧ right = .tru := by
  cases left <;> cases right <;> decide

private theorem K.or_eq_tru_iff (left right : K) :
    K.or left right = .tru ↔ left = .tru ∨ right = .tru := by
  cases left <;> cases right <;> decide

private theorem filter_eq_self_of_any_not_false (items : List α)
    (predicate : α → Bool)
    (complete : (items.any fun item => !predicate item) = false) :
    items.filter predicate = items := by
  apply List.filter_eq_self.mpr
  intro item member
  have itemComplete := List.any_eq_false.mp complete item member
  cases equation : predicate item with
  | false =>
      exfalso
      exact itemComplete (by simp [equation])
  | true => rfl

private theorem selectedAnd_eq_conj (left right : FlatCondition)
    (context : FlatContext) (isRelevant : FlatRelevance) :
    FlatCondition.evalSelected context isRelevant (.and left right) =
      Verdict.conj (left.evalSelected context isRelevant)
        (right.evalSelected context isRelevant) := by
  unfold FlatCondition.evalSelected
  rw [ConditionTree.evalVerdict]
  generalize leftEq :
    left.evalVerdict (fun leaf => leaf.evalSelected context isRelevant) = leftVerdict
  cases leftVerdict <;> rfl

private theorem selectedOr_eq_disj (left right : FlatCondition)
    (context : FlatContext) (isRelevant : FlatRelevance) :
    FlatCondition.evalSelected context isRelevant (.or left right) =
      Verdict.disj (left.evalSelected context isRelevant)
        (right.evalSelected context isRelevant) := by
  unfold FlatCondition.evalSelected
  rw [ConditionTree.evalVerdict]
  generalize leftEq :
    left.evalVerdict (fun leaf => leaf.evalSelected context isRelevant) = leftVerdict
  cases leftVerdict with
  | notFired => rfl
  | unknown => rfl
  | fired polarity =>
      cases polarity <;> rfl

private theorem temporalOperand_resolve_agreesOn
    (operand : FlatTemporalOperand) (left right : FlatContext)
    (isRelevant : FlatRelevance) (worldAgreement : left.world = right.world)
    (agreement : ∀ field, isRelevant field = true → left.read field = right.read field)
    (relevant : (operand.fields.map FlatField.id).all isRelevant = true) :
    operand.resolve left = operand.resolve right := by
  cases operand with
  | fieldValue field =>
      have readEq := agreement field.id (by
        simpa [FlatTemporalOperand.fields, FlatField.id] using relevant)
      simp_all [FlatTemporalOperand.resolve,
        FlatContext.resolveTemporalComparisonOperand,
        FlatContext.observeValidationAt]
  | literalValue instant => rfl
  | todayValue zoneId =>
      simp [FlatTemporalOperand.resolve, worldAgreement]
  | baseYearValue zoneId year =>
      simp [FlatTemporalOperand.resolve,
        FlatContext.resolveLocalDateComparisonOperand, worldAgreement]
  | baseYearRangeValue zoneId year endpoint =>
      simp [FlatTemporalOperand.resolve,
        FlatContext.resolveLocalDateComparisonOperand, worldAgreement]
  | nowValue =>
      simp [FlatTemporalOperand.resolve, worldAgreement]

private theorem textFieldOperand_resolve_agreesOn
    (operand : FlatTextFieldOperand) (left right : FlatContext)
    (isRelevant : FlatRelevance)
    (agreement : ∀ field, isRelevant field = true → left.read field = right.read field)
    (relevant : isRelevant operand.field.id = true) :
    operand.resolve left = operand.resolve right := by
  cases operand with
  | string field =>
      have readEq := agreement field.id (by
        simpa [FlatTextFieldOperand.field, FlatField.id] using relevant)
      simp_all [FlatTextFieldOperand.resolve,
        FlatContext.resolveDirectStringComparisonOperand,
        FlatContext.observeValidationAt]
  | enumeration operand =>
      have readEq := agreement operand.field.id (by
        simpa [FlatTextFieldOperand.field, FlatField.id] using relevant)
      simp_all [FlatTextFieldOperand.resolve, FlatEnumerationOperand.resolve,
        FlatContext.observeValidationAt]

private theorem tokenValueListSide_agreesOn
    (operands : List FlatTextFieldOperand) (left right : FlatContext)
    (isRelevant : FlatRelevance)
    (agreement : ∀ field, isRelevant field = true → left.read field = right.read field)
    (relevant : operands.all (fun operand => isRelevant operand.field.id) = true) :
    flatTokenValueListSide operands left =
      flatTokenValueListSide operands right := by
  unfold flatTokenValueListSide
  congr 1
  apply List.map_congr_left
  intro operand member
  have relevantOperand : isRelevant operand.field.id = true := by
    exact List.all_eq_true.mp relevant operand member
  simp only [FlatTextFieldOperand.valueListCell]
  rw [textFieldOperand_resolve_agreesOn operand left right isRelevant
    agreement relevantOperand]

private theorem tokenValueSide_agreesOn
    (values : FlatTokenValueSide) (left right : FlatContext)
    (isRelevant : FlatRelevance)
    (agreement : ∀ field, isRelevant field = true → left.read field = right.read field)
    (relevant : values.operands.all (fun operand => isRelevant operand.field.id) = true) :
    values.resolve left = values.resolve right := by
  cases values with
  | literals literals => rfl
  | fields operands =>
      exact tokenValueListSide_agreesOn operands left right isRelevant
        agreement relevant

private theorem selectedTokenValueListSide_agreesOn
    (operands : List FlatTextFieldOperand) (left right : FlatContext)
    (isRelevant : FlatRelevance)
    (agreement : ∀ field, isRelevant field = true → left.read field = right.read field) :
    selectedFlatTokenValueListSide operands left isRelevant =
      selectedFlatTokenValueListSide operands right isRelevant := by
  unfold selectedFlatTokenValueListSide
  congr 1
  apply tokenValueListSide_agreesOn
  · exact agreement
  · apply List.all_eq_true.mpr
    intro operand member
    exact (List.mem_filter.mp member).2

private theorem selectedTokenValueSide_agreesOn
    (values : FlatTokenValueSide) (left right : FlatContext)
    (isRelevant : FlatRelevance)
    (agreement : ∀ field, isRelevant field = true → left.read field = right.read field) :
    values.resolveSelected left isRelevant =
      values.resolveSelected right isRelevant := by
  cases values with
  | literals literals => rfl
  | fields operands =>
      exact selectedTokenValueListSide_agreesOn operands left right isRelevant
        agreement

private theorem numberValueListSide_agreesOn
    (operands : List FlatNumberField) (left right : FlatContext)
    (isRelevant : FlatRelevance)
    (agreement : ∀ field, isRelevant field = true → left.read field = right.read field)
    (relevant : operands.all (fun operand => isRelevant operand.id) = true) :
    flatNumberValueListSide operands left =
      flatNumberValueListSide operands right := by
  unfold flatNumberValueListSide
  congr 1
  apply List.map_congr_left
  intro operand member
  have relevantOperand : isRelevant operand.id = true := by
    exact List.all_eq_true.mp relevant operand member
  have readEq := agreement operand.id relevantOperand
  simp_all [FlatNumberField.valueListCell, FlatContext.observeValidationAt]

private theorem numberValueSide_agreesOn
    (values : FlatNumberValueSide) (left right : FlatContext)
    (isRelevant : FlatRelevance)
    (agreement : ∀ field, isRelevant field = true → left.read field = right.read field)
    (relevant : values.operands.all (fun operand => isRelevant operand.id) = true) :
    values.resolve left = values.resolve right := by
  cases values with
  | literals literals => rfl
  | fields operands =>
      exact numberValueListSide_agreesOn operands left right isRelevant
        agreement relevant

private theorem selectedNumberValueListSide_agreesOn
    (operands : List FlatNumberField) (left right : FlatContext)
    (isRelevant : FlatRelevance)
    (agreement : ∀ field, isRelevant field = true → left.read field = right.read field) :
    selectedFlatNumberValueListSide operands left isRelevant =
      selectedFlatNumberValueListSide operands right isRelevant := by
  unfold selectedFlatNumberValueListSide
  congr 1
  apply numberValueListSide_agreesOn
  · exact agreement
  · apply List.all_eq_true.mpr
    intro operand member
    exact (List.mem_filter.mp member).2

private theorem selectedNumberValueSide_agreesOn
    (values : FlatNumberValueSide) (left right : FlatContext)
    (isRelevant : FlatRelevance)
    (agreement : ∀ field, isRelevant field = true → left.read field = right.read field) :
    values.resolveSelected left isRelevant =
      values.resolveSelected right isRelevant := by
  cases values with
  | literals literals => rfl
  | fields operands =>
      exact selectedNumberValueListSide_agreesOn operands left right isRelevant
        agreement

private theorem selectedTokenValueListSide_cells_sublist
    (operands : List FlatTextFieldOperand) (context : FlatContext)
    (isRelevant : FlatRelevance) :
    (selectedFlatTokenValueListSide operands context isRelevant).side.cells.Sublist
      (flatTokenValueListSide operands context).cells := by
  change ((operands.filter fun operand => isRelevant operand.field.id).map
      (fun operand => operand.valueListCell context)).Sublist
    (operands.map fun operand => operand.valueListCell context)
  exact List.filter_sublist.map _

private theorem selectedTokenValueListSide_complete
    (operands : List FlatTextFieldOperand) (context : FlatContext)
    (isRelevant : FlatRelevance)
    (complete :
      (selectedFlatTokenValueListSide operands context isRelevant).hasNonRelevant = false) :
    (selectedFlatTokenValueListSide operands context isRelevant).side =
      flatTokenValueListSide operands context := by
  change (operands.any fun operand => !isRelevant operand.field.id) = false at complete
  change flatTokenValueListSide
      (operands.filter fun operand => isRelevant operand.field.id) context =
    flatTokenValueListSide operands context
  rw [filter_eq_self_of_any_not_false operands
    (fun operand => isRelevant operand.field.id) complete]

private theorem selectedTokenValueSide_cells_sublist
    (values : FlatTokenValueSide) (context : FlatContext)
    (isRelevant : FlatRelevance) :
    (values.resolveSelected context isRelevant).side.cells.Sublist
      (values.resolve context).cells := by
  cases values with
  | literals literals => exact List.Sublist.refl _
  | fields operands =>
      exact selectedTokenValueListSide_cells_sublist operands context isRelevant

private theorem selectedTokenValueSide_complete
    (values : FlatTokenValueSide) (context : FlatContext)
    (isRelevant : FlatRelevance)
    (complete : (values.resolveSelected context isRelevant).hasNonRelevant = false) :
    (values.resolveSelected context isRelevant).side = values.resolve context := by
  cases values with
  | literals literals => rfl
  | fields operands =>
      exact selectedTokenValueListSide_complete operands context isRelevant complete

private theorem selectedNumberValueListSide_cells_sublist
    (operands : List FlatNumberField) (context : FlatContext)
    (isRelevant : FlatRelevance) :
    (selectedFlatNumberValueListSide operands context isRelevant).side.cells.Sublist
      (flatNumberValueListSide operands context).cells := by
  change ((operands.filter fun operand => isRelevant operand.id).map
      (fun operand => operand.valueListCell context)).Sublist
    (operands.map fun operand => operand.valueListCell context)
  exact List.filter_sublist.map _

private theorem selectedNumberValueListSide_complete
    (operands : List FlatNumberField) (context : FlatContext)
    (isRelevant : FlatRelevance)
    (complete :
      (selectedFlatNumberValueListSide operands context isRelevant).hasNonRelevant = false) :
    (selectedFlatNumberValueListSide operands context isRelevant).side =
      flatNumberValueListSide operands context := by
  change (operands.any fun operand => !isRelevant operand.id) = false at complete
  change flatNumberValueListSide
      (operands.filter fun operand => isRelevant operand.id) context =
    flatNumberValueListSide operands context
  rw [filter_eq_self_of_any_not_false operands
    (fun operand => isRelevant operand.id) complete]

private theorem selectedNumberValueSide_cells_sublist
    (values : FlatNumberValueSide) (context : FlatContext)
    (isRelevant : FlatRelevance) :
    (values.resolveSelected context isRelevant).side.cells.Sublist
      (values.resolve context).cells := by
  cases values with
  | literals literals => exact List.Sublist.refl _
  | fields operands =>
      exact selectedNumberValueListSide_cells_sublist operands context isRelevant

private theorem selectedNumberValueSide_complete
    (values : FlatNumberValueSide) (context : FlatContext)
    (isRelevant : FlatRelevance)
    (complete : (values.resolveSelected context isRelevant).hasNonRelevant = false) :
    (values.resolveSelected context isRelevant).side = values.resolve context := by
  cases values with
  | literals literals => rfl
  | fields operands =>
      exact selectedNumberValueListSide_complete operands context isRelevant complete

private theorem fullTokenValueList_eval
    (quantifier : ValueListQuantifier) (operands : List FlatTextFieldOperand)
    (values : FlatTokenValueSide) (context : FlatContext) :
    quantifier.evalClassified
        (selectedFlatTokenValueListSide operands context fun _ => true)
        (values.resolveSelected context fun _ => true) =
      quantifier.eval (flatTokenValueListSide operands context)
        (values.resolve context) := by
  rw [selectedFlatTokenValueListSide_full,
    flatTokenValueSide_resolveSelected_full]
  rfl

private theorem fullNumberValueList_eval
    (quantifier : ValueListQuantifier) (operands : List FlatNumberField)
    (values : FlatNumberValueSide) (context : FlatContext) :
    quantifier.evalClassified
        (selectedFlatNumberValueListSide operands context fun _ => true)
        (values.resolveSelected context fun _ => true) =
      quantifier.eval (flatNumberValueListSide operands context)
        (values.resolve context) := by
  rw [selectedFlatNumberValueListSide_full,
    flatNumberValueSide_resolveSelected_full]
  rfl

/-- Masked partial evaluation depends only on the flat fields marked relevant. -/
theorem partialSelected_agreesOn
    (condition : FlatCondition) (left right : FlatContext)
    (isRelevant : FlatRelevance) (agreement : left.AgreesOn right isRelevant) :
    condition.evalSelected left isRelevant =
      condition.evalSelected right isRelevant := by
  rcases agreement with ⟨worldAgreement, agreement⟩
  induction condition with
  | leaf leaf =>
    cases leaf with
    | compare comparison =>
      simp only [FlatCondition.evalSelected, ConditionTree.evalVerdict,
        FlatConditionLeaf.evalSelected]
      split
      · rename_i relevant
        cases comparison with
        | number op field expected =>
            have readEq := agreement field.id (by
              simpa [FlatComparison.allRelevant, FlatComparison.fieldIds,
                FlatComparison.fields, FlatField.id] using relevant)
            simp_all [FlatComparison.eval, FlatContext.resolveNumberComparisonOperand,
              FlatContext.resolveNumberComparisonOperandAt, FlatContext.observeAt]
        | boolean op field expected =>
            have readEq := agreement field.id (by
              simpa [FlatComparison.allRelevant, FlatComparison.fieldIds,
                FlatComparison.fields, FlatField.id] using relevant)
            simp_all [FlatComparison.eval, FlatContext.resolveBooleanComparisonOperand,
              FlatContext.observeValidationAt]
        | confirm op field =>
            have readEq := agreement field.id (by
              simpa [FlatComparison.allRelevant, FlatComparison.fieldIds,
                FlatComparison.fields, FlatField.id] using relevant)
            simp_all [FlatComparison.eval, FlatContext.resolveConfirmComparisonOperand,
              FlatContext.observeValidationAt]
        | string op field expected =>
            have readEq := agreement field.id (by
              simpa [FlatComparison.allRelevant, FlatComparison.fieldIds,
                FlatComparison.fields, FlatField.id] using relevant)
            simp_all [FlatComparison.eval,
              FlatContext.resolveDirectStringComparisonOperand,
              FlatContext.observeValidationAt]
        | stringLength op field expected =>
            have readEq := agreement field.id (by
              simpa [FlatComparison.allRelevant, FlatComparison.fieldIds,
                FlatComparison.fields, FlatField.id] using relevant)
            simp_all [FlatComparison.eval, FlatContext.resolveStringLengthOperand,
              FlatContext.observeValidationAt]
        | enumeration op operand expected =>
            have readEq := agreement operand.field.id (by
              simpa [FlatComparison.allRelevant, FlatComparison.fieldIds,
                FlatComparison.fields, FlatField.id] using relevant)
            simp_all [FlatComparison.eval, FlatContext.observeValidationAt]
        | textFields op leftOperand rightOperand =>
            have bothRelevant :
                isRelevant leftOperand.field.id = true ∧
                isRelevant rightOperand.field.id = true := by
              simpa [FlatComparison.allRelevant, FlatComparison.fieldIds,
                FlatComparison.fields, FlatTextFieldOperand.field,
                FlatField.id] using relevant
            simp only [FlatComparison.eval]
            rw [textFieldOperand_resolve_agreesOn leftOperand left right isRelevant
                agreement bothRelevant.left,
              textFieldOperand_resolve_agreesOn rightOperand left right isRelevant
                agreement bothRelevant.right]
        | temporal op leftOperand rightOperand =>
            have bothRelevant :
                (leftOperand.fields.map FlatField.id).all isRelevant = true ∧
                (rightOperand.fields.map FlatField.id).all isRelevant = true := by
              simpa [FlatComparison.allRelevant, FlatComparison.fieldIds,
                FlatComparison.fields] using relevant
            simp only [FlatComparison.eval]
            rw [temporalOperand_resolve_agreesOn leftOperand left right isRelevant
                worldAgreement agreement bothRelevant.left,
              temporalOperand_resolve_agreesOn rightOperand left right isRelevant
                worldAgreement agreement bothRelevant.right]
      · rfl
    | tokenValueList quantifier operands values =>
      simp only [FlatCondition.evalSelected, ConditionTree.evalVerdict,
        FlatConditionLeaf.evalSelected]
      rw [selectedTokenValueListSide_agreesOn operands left right isRelevant
          agreement,
        selectedTokenValueSide_agreesOn values left right isRelevant agreement]
    | numberValueList quantifier operands values =>
      simp only [FlatCondition.evalSelected, ConditionTree.evalVerdict,
        FlatConditionLeaf.evalSelected]
      rw [selectedNumberValueListSide_agreesOn operands left right isRelevant
          agreement,
        selectedNumberValueSide_agreesOn values left right isRelevant agreement]
    | fieldFilled field | fieldNotFilled field =>
      simp only [FlatCondition.evalSelected, ConditionTree.evalVerdict,
        FlatConditionLeaf.evalSelected]
      split
      · have readEq := agreement field.id (by assumption)
        cases field <;>
          simp_all [FlatField.id, FlatField.evalFilled, FlatField.evalNotFilled,
            FlatField.observeValidation, FlatContext.observeValidationAt]
      · rfl
  | and leftTree rightTree leftIH rightIH | or leftTree rightTree leftIH rightIH =>
      change leftTree.evalVerdict (fun leaf => leaf.evalSelected left isRelevant) =
        leftTree.evalVerdict (fun leaf => leaf.evalSelected right isRelevant) at leftIH
      change rightTree.evalVerdict (fun leaf => leaf.evalSelected left isRelevant) =
        rightTree.evalVerdict (fun leaf => leaf.evalSelected right isRelevant) at rightIH
      simp only [FlatCondition.evalSelected, ConditionTree.evalVerdict]
      rw [leftIH]
      split
      · rfl
      · rw [rightIH]

private theorem partialSelected_true_persists_full
    (condition : FlatCondition) (context : FlatContext) (isRelevant : FlatRelevance)
    (partialTrue : Verdict.truth (condition.evalSelected context isRelevant) = .tru) :
    Verdict.truth (condition.evalSelected context) = .tru := by
  induction condition with
  | leaf leaf =>
    cases leaf with
    | compare comparison =>
      simp only [FlatCondition.evalSelected, ConditionTree.evalVerdict,
        FlatConditionLeaf.evalSelected] at partialTrue ⊢
      split at partialTrue
      · simpa [FlatComparison.allRelevant] using partialTrue
      · simp [Verdict.truth] at partialTrue
    | tokenValueList quantifier operands values =>
      simp only [FlatCondition.evalSelected, ConditionTree.evalVerdict,
        FlatConditionLeaf.evalSelected] at partialTrue ⊢
      rcases (Verdict.truth_eq_tru_iff _).1 partialTrue with
        ⟨partialPolarity, partialFired⟩
      rcases valueList_classified_fired_implies_resolved_fired quantifier
          (selectedFlatTokenValueListSide operands context isRelevant)
          (values.resolveSelected context isRelevant)
          (flatTokenValueListSide operands context) (values.resolve context)
          (selectedTokenValueListSide_cells_sublist operands context isRelevant)
          (selectedTokenValueSide_cells_sublist values context isRelevant)
          (selectedTokenValueListSide_complete operands context isRelevant)
          (selectedTokenValueSide_complete values context isRelevant)
          partialPolarity partialFired with ⟨fullPolarity, fullFired⟩
      apply (Verdict.truth_eq_tru_iff _).2
      exact ⟨fullPolarity, by
        rw [fullTokenValueList_eval]
        exact fullFired⟩
    | numberValueList quantifier operands values =>
      simp only [FlatCondition.evalSelected, ConditionTree.evalVerdict,
        FlatConditionLeaf.evalSelected] at partialTrue ⊢
      rcases (Verdict.truth_eq_tru_iff _).1 partialTrue with
        ⟨partialPolarity, partialFired⟩
      rcases valueList_classified_fired_implies_resolved_fired quantifier
          (selectedFlatNumberValueListSide operands context isRelevant)
          (values.resolveSelected context isRelevant)
          (flatNumberValueListSide operands context) (values.resolve context)
          (selectedNumberValueListSide_cells_sublist operands context isRelevant)
          (selectedNumberValueSide_cells_sublist values context isRelevant)
          (selectedNumberValueListSide_complete operands context isRelevant)
          (selectedNumberValueSide_complete values context isRelevant)
          partialPolarity partialFired with ⟨fullPolarity, fullFired⟩
      apply (Verdict.truth_eq_tru_iff _).2
      exact ⟨fullPolarity, by
        rw [fullNumberValueList_eval]
        exact fullFired⟩
    | fieldFilled field | fieldNotFilled field =>
      simp only [FlatCondition.evalSelected, ConditionTree.evalVerdict,
        FlatConditionLeaf.evalSelected] at partialTrue ⊢
      split at partialTrue
      · simpa using partialTrue
      · simp [Verdict.truth] at partialTrue
  | and left right leftIH rightIH =>
      rw [selectedAnd_eq_conj left right context isRelevant,
        Verdict.truth_conj] at partialTrue
      rw [selectedAnd_eq_conj left right context (fun _ => true),
        Verdict.truth_conj]
      rw [K.and_eq_tru_iff] at partialTrue ⊢
      exact ⟨leftIH partialTrue.1, rightIH partialTrue.2⟩
  | or left right leftIH rightIH =>
      rw [selectedOr_eq_disj left right context isRelevant,
        Verdict.truth_disj] at partialTrue
      rw [selectedOr_eq_disj left right context (fun _ => true),
        Verdict.truth_disj]
      rw [K.or_eq_tru_iff] at partialTrue ⊢
      cases partialTrue with
      | inl leftTrue => exact .inl (leftIH leftTrue)
      | inr rightTrue => exact .inr (rightIH rightTrue)

/-- Kernel 30.8.1's rule-level filter gate precedes error-field relevance and every condition read. -/
theorem partialFilteredRule_skipped
    (condition : FlatCondition) (context : FlatContext)
    (errorField : FieldId) (isRelevant : FlatRelevance) :
    condition.evalPartial context errorField isRelevant .filtered = .skipped := by
  rfl

/-- If partial validation fires, every content-bearing completion agreeing on the
    relevant flat fields also fires. Completion may change the firing polarity. -/
theorem partialRule_fired_implies_fullWithContent_fired_of_agreesOn
    (condition : FlatCondition) (partialContext completionContext : FlatContext)
    (errorField : FieldId) (isRelevant : FlatRelevance) (partialPolarity : Polarity)
    (agreement : partialContext.AgreesOn completionContext isRelevant)
    (relevant : isRelevant errorField = true)
    (partialFired :
      condition.evalPartial partialContext errorField isRelevant .unfiltered =
        .evaluated (.fired partialPolarity)) :
    ∃ fullPolarity,
      condition.evalFull completionContext true = .fired fullPolarity := by
  have partialSelectedFired :
      condition.evalSelected completionContext isRelevant = .fired partialPolarity := by
    rw [← partialSelected_agreesOn condition partialContext completionContext
      isRelevant agreement]
    simpa [FlatCondition.evalPartial, relevant] using partialFired
  have fullTrue := partialSelected_true_persists_full condition completionContext
    isRelevant (by simp [partialSelectedFired, Verdict.truth])
  rcases (Verdict.truth_eq_tru_iff _).1 fullTrue with ⟨fullPolarity, fullFired⟩
  exact ⟨fullPolarity, by simpa [FlatCondition.evalFull] using fullFired⟩

end A12Kernel
