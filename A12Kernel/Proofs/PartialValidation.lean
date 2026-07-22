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
    (FlatCondition.and left right).evalSelected context isRelevant =
      Verdict.conj (left.evalSelected context isRelevant)
        (right.evalSelected context isRelevant) := by
  simp only [FlatCondition.evalSelected]
  generalize leftEq : left.evalSelected context isRelevant = leftVerdict
  cases leftVerdict <;> rfl

private theorem selectedOr_eq_disj (left right : FlatCondition)
    (context : FlatContext) (isRelevant : FlatRelevance) :
    (FlatCondition.or left right).evalSelected context isRelevant =
      Verdict.disj (left.evalSelected context isRelevant)
        (right.evalSelected context isRelevant) := by
  simp only [FlatCondition.evalSelected]
  generalize leftEq : left.evalSelected context isRelevant = leftVerdict
  cases leftVerdict with
  | notFired => rfl
  | unknown => rfl
  | fired polarity => cases polarity <;> rfl

/-- Masked partial evaluation depends only on the flat fields marked relevant. -/
theorem partialSelected_agreesOn
    (condition : FlatCondition) (left right : FlatContext)
    (isRelevant : FlatRelevance) (agreement : left.AgreesOn right isRelevant) :
    condition.evalSelected left isRelevant =
      condition.evalSelected right isRelevant := by
  induction condition with
  | compare comparison =>
      simp only [FlatCondition.evalSelected]
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
        | temporal op leftOperand rightOperand =>
            cases leftOperand with
            | literalValue leftInstant =>
                cases rightOperand with
                | literalValue rightInstant => rfl
                | fieldValue rightField =>
                    have rightReadEq := agreement rightField.id (by
                      simpa [FlatComparison.allRelevant, FlatComparison.fieldIds,
                        FlatComparison.fields, FlatTemporalOperand.fields,
                        FlatField.id] using relevant)
                    simp_all [FlatComparison.eval, FlatTemporalOperand.resolve,
                      FlatContext.resolveTemporalComparisonOperand,
                      FlatContext.observeValidationAt]
            | fieldValue leftField =>
                cases rightOperand with
                | literalValue rightInstant =>
                    have leftReadEq := agreement leftField.id (by
                      simpa [FlatComparison.allRelevant, FlatComparison.fieldIds,
                        FlatComparison.fields, FlatTemporalOperand.fields,
                        FlatField.id] using relevant)
                    simp_all [FlatComparison.eval, FlatTemporalOperand.resolve,
                      FlatContext.resolveTemporalComparisonOperand,
                      FlatContext.observeValidationAt]
                | fieldValue rightField =>
                    have bothRelevant : isRelevant leftField.id = true ∧
                        isRelevant rightField.id = true := by
                      simpa [FlatComparison.allRelevant, FlatComparison.fieldIds,
                        FlatComparison.fields, FlatTemporalOperand.fields,
                        FlatField.id] using relevant
                    have leftReadEq := agreement leftField.id bothRelevant.left
                    have rightReadEq := agreement rightField.id bothRelevant.right
                    simp_all [FlatComparison.eval, FlatTemporalOperand.resolve,
                      FlatContext.resolveTemporalComparisonOperand,
                      FlatContext.observeValidationAt]
      · rfl
  | fieldFilled field | fieldNotFilled field =>
      simp only [FlatCondition.evalSelected]
      split
      · have readEq := agreement field.id (by assumption)
        cases field <;>
          simp_all [FlatField.id, FlatField.evalFilled, FlatField.evalNotFilled,
            FlatField.observeValidation, FlatContext.observeValidationAt]
      · rfl
  | and left right leftIH rightIH | or left right leftIH rightIH =>
      simp only [FlatCondition.evalSelected]
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
  | compare comparison =>
      have fullRelevant : comparison.allRelevant (fun _ => true) = true := by
        simp [FlatComparison.allRelevant]
      simp only [FlatCondition.evalSelected, fullRelevant, ↓reduceIte]
      split
      · exact K.informationRefines_refl _
      · trivial
  | fieldFilled field | fieldNotFilled field =>
      simp only [FlatCondition.evalSelected]
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
