import A12Kernel.Proofs.Information
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
              FlatContext.observeValidationAt]
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
      split
      · rename_i relevant
        have bothRelevant :
            operands.all (fun operand => isRelevant operand.field.id) = true ∧
            values.operands.all (fun operand => isRelevant operand.field.id) = true := by
          simpa [FlatTokenValueSide.allOperands] using relevant
        rw [tokenValueListSide_agreesOn operands left right isRelevant
            agreement bothRelevant.left,
          tokenValueSide_agreesOn values left right isRelevant
            agreement bothRelevant.right]
      · rfl
    | numberValueList quantifier operands values =>
      simp only [FlatCondition.evalSelected, ConditionTree.evalVerdict,
        FlatConditionLeaf.evalSelected]
      split
      · rename_i relevant
        have bothRelevant :
            operands.all (fun operand => isRelevant operand.id) = true ∧
            values.operands.all (fun operand => isRelevant operand.id) = true := by
          simpa [FlatNumberValueSide.allOperands] using relevant
        rw [numberValueListSide_agreesOn operands left right isRelevant
            agreement bothRelevant.left,
          numberValueSide_agreesOn values left right isRelevant
            agreement bothRelevant.right]
      · rfl
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

private theorem partialSelected_truth_refines_full
    (condition : FlatCondition) (context : FlatContext) (isRelevant : FlatRelevance) :
    K.InformationRefines
      (Verdict.truth (condition.evalSelected context isRelevant))
      (Verdict.truth (condition.evalSelected context)) := by
  induction condition with
  | leaf leaf =>
    cases leaf with
    | compare comparison =>
      have fullRelevant : comparison.allRelevant (fun _ => true) = true := by
        simp [FlatComparison.allRelevant]
      simp only [FlatCondition.evalSelected, ConditionTree.evalVerdict,
        FlatConditionLeaf.evalSelected, fullRelevant, ↓reduceIte]
      split
      · exact K.informationRefines_refl _
      · trivial
    | tokenValueList quantifier operands values =>
      have fullRelevant :
          (values.allOperands operands).all (fun _ => true) = true := by simp
      simp only [FlatCondition.evalSelected, ConditionTree.evalVerdict,
        FlatConditionLeaf.evalSelected, fullRelevant, ↓reduceIte]
      split
      · exact K.informationRefines_refl _
      · trivial
    | numberValueList quantifier operands values =>
      have fullRelevant :
          (values.allOperands operands).all (fun _ => true) = true := by simp
      simp only [FlatCondition.evalSelected, ConditionTree.evalVerdict,
        FlatConditionLeaf.evalSelected, fullRelevant, ↓reduceIte]
      split
      · exact K.informationRefines_refl _
      · trivial
    | fieldFilled field | fieldNotFilled field =>
      simp only [FlatCondition.evalSelected, ConditionTree.evalVerdict,
        FlatConditionLeaf.evalSelected]
      split
      · exact K.informationRefines_refl _
      · trivial
  | and left right leftIH rightIH =>
      rw [selectedAnd_eq_conj left right context isRelevant,
        selectedAnd_eq_conj left right context (fun _ => true),
        Verdict.truth_conj, Verdict.truth_conj]
      exact K.and_information_monotone leftIH rightIH
  | or left right leftIH rightIH =>
      rw [selectedOr_eq_disj left right context isRelevant,
        selectedOr_eq_disj left right context (fun _ => true),
        Verdict.truth_disj, Verdict.truth_disj]
      exact K.or_information_monotone leftIH rightIH

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
  have refinement := partialSelected_truth_refines_full condition completionContext isRelevant
  rw [show condition.evalSelected completionContext isRelevant = .fired partialPolarity by
    rw [← partialSelected_agreesOn condition partialContext completionContext
      isRelevant agreement]
    simpa [FlatCondition.evalPartial, relevant] using partialFired] at refinement
  generalize fullEq : condition.evalSelected completionContext = fullVerdict at refinement
  cases fullVerdict with
  | notFired => contradiction
  | unknown => contradiction
  | fired fullPolarity =>
      exact ⟨fullPolarity, by
        simpa [FlatCondition.evalFull] using fullEq⟩

end A12Kernel
