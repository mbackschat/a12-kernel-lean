import A12Kernel.Proofs.ConditionNegation
import A12Kernel.Semantics.NumericComparison
import A12Kernel.Semantics.ScalarEquality
import A12Kernel.Semantics.ValidationFillQuantifier
import A12Kernel.Semantics.GroupPresence
import A12Kernel.Semantics.FlatValidation

/-! # Firing regions of the complement pairs

Each predicate pair rule negation uses has three regions: where the original fires, where its
complement fires, and where neither does. The tree laws in `ConditionNegation` need the first two to
be disjoint, and exhaustiveness holds exactly outside the third. These are the pairs whose members
share one evaluator; the String pattern pair's facts are `stringPattern_evalResolved_value_complement`
and its empty and unknown neighbours. The polarities of a pair are not related: `AllFieldsFilled`
fires with VALUE where `NotAllFieldsFilled` fires with OMISSION.
-/

namespace A12Kernel

namespace NumericComparisonOp

theorem holds_complement (op : NumericComparisonOp) (left right : Rat) :
    op.complement.holds left right = !op.holds left right := by
  cases op <;> simp [complement, holds] <;> grind

/-- A comparison and its complement never both fire, and both are silent exactly when an operand is
unknown. -/
theorem eval_complement_regions (op : NumericComparisonOp) (left right : NumericOperand) :
    ¬ ((op.eval left right).fires ∧ (op.complement.eval left right).fires) ∧
      (((op.eval left right).fires || (op.complement.eval left right).fires) = false ↔
        (∃ cause, left = .unknown cause) ∨ (∃ cause, right = .unknown cause)) := by
  cases left <;> cases right <;> simp only [eval, holds_complement]
  all_goals (repeat' split) <;> simp_all [Verdict.fires]

end NumericComparisonOp

namespace EqualityOp

theorem evalSimple_complement_regions (op : EqualityOp) (equivalent : α → α → Bool)
    (operand : SimpleComparisonOperand α) (expected : α) :
    ¬ ((op.evalSimple equivalent operand expected).fires ∧
        (op.complement.evalSimple equivalent operand expected).fires) ∧
      (((op.evalSimple equivalent operand expected).fires ||
          (op.complement.evalSimple equivalent operand expected).fires) = false ↔
        ∀ actual given, operand ≠ .value actual given) := by
  cases op <;> cases operand <;> simp only [evalSimple, complement, holds]
  all_goals (repeat' split) <;> simp_all [Verdict.fires]

/-- Direct String equality and its complement never both fire, and both are silent exactly when the
field holds no value or the literal is empty, which the String reader suppresses. -/
theorem evalDirectString_complement_regions (op : EqualityOp)
    (operand : SimpleComparisonOperand String) (expected : String) :
    ¬ ((operand.evalDirectString op expected).fires ∧
        (operand.evalDirectString op.complement expected).fires) ∧
      (((operand.evalDirectString op expected).fires ||
          (operand.evalDirectString op.complement expected).fires) = false ↔
        expected.isEmpty ∨ ∀ actual given, operand ≠ .value actual given) := by
  cases op <;> cases operand <;>
    simp only [SimpleComparisonOperand.evalDirectString, evalSimple, complement, holds]
  all_goals (repeat' split) <;> simp_all [Verdict.fires]

end EqualityOp

namespace CellObservation

/-- `FieldFilled` and `FieldNotFilled` never both fire, and both are silent exactly on a formally
unavailable or poisoned cell. -/
theorem fieldFilled_complement_regions (observation : CellObservation) :
    ¬ (observation.evalValidationFilled.fires ∧ observation.evalValidationNotFilled.fires) ∧
      ((observation.evalValidationFilled.fires || observation.evalValidationNotFilled.fires) = false ↔
        observation ≠ .empty ∧ ∀ value, observation ≠ .value value) := by
  cases observation <;> simp [Verdict.fires]

end CellObservation

namespace GroupPresenceState

/-- `GroupFilled` and `GroupNotFilled` never both fire, and both are silent exactly where no member is
relevant, or where no content is seen and either an error or partial relevance keeps absence from
being proved. -/
theorem groupFilled_complement_regions (state : GroupPresenceState) :
    ¬ (state.groupFilled.fires ∧ state.groupNotFilled.fires) ∧
      ((state.groupFilled.fires || state.groupNotFilled.fires) = false ↔
        state.relevance = .noneRelevant ∨
          (state.content = false ∧ (state.erroneous = true ∨ state.relevance ≠ .fullyRelevant))) := by
  rcases state with ⟨content, erroneous, relevance⟩
  cases content <;> cases erroneous <;> cases relevance <;>
    simp [groupFilled, groupNotFilled, definitelyFilled, Verdict.fires]

end GroupPresenceState

namespace FieldFillQuantifier

private abbrev fires (op : FieldFillQuantifier) (tally : ValidationFillTally) : Bool :=
  (op.evalValidation tally).asConservativeVerdict.fires

/-- `AllFieldsFilled` and `NotAllFieldsFilled` never both fire, and both are silent exactly when
every slot is filled or unknown with at least one unknown. -/
theorem allFieldsFilled_complement_regions (tally : ValidationFillTally) :
    ¬ (fires .allFieldsFilled tally ∧ fires .notAllFieldsFilled tally) ∧
      ((fires .allFieldsFilled tally || fires .notAllFieldsFilled tally) = false ↔
        tally.empty = 0 ∧ tally.uninstantiated = 0 ∧ 0 < tally.unknown) := by
  simp only [fires, evalValidation]
  all_goals (repeat' split) <;> simp [ValidationFillOutcome.asConservativeVerdict, Verdict.fires] at * <;>
    omega

/-- `AtLeastOneFieldFilled` and `NoFieldFilled` never both fire, and both are silent exactly when
nothing is filled and something is unknown. -/
theorem atLeastOneFieldFilled_complement_regions (tally : ValidationFillTally) :
    ¬ (fires .atLeastOneFieldFilled tally ∧ fires .noFieldFilled tally) ∧
      ((fires .atLeastOneFieldFilled tally || fires .noFieldFilled tally) = false ↔
        tally.filled = 0 ∧ 0 < tally.unknown) := by
  simp only [fires, evalValidation]
  all_goals (repeat' split) <;> simp [ValidationFillOutcome.asConservativeVerdict, Verdict.fires] at * <;>
    omega

/-- `FieldsNotCollectivelyFilled` fires with neither member of its complement `AllFieldsFilled Or
NoFieldFilled`. -/
theorem fieldsNotCollectivelyFilled_excludes_complement (tally : ValidationFillTally) :
    fires .fieldsNotCollectivelyFilled tally →
      fires .allFieldsFilled tally = false ∧ fires .noFieldFilled tally = false := by
  simp only [fires, evalValidation]
  all_goals (repeat' split) <;> simp [ValidationFillOutcome.asConservativeVerdict, Verdict.fires] at * <;>
    omega

end FieldFillQuantifier

namespace GroupFillQuantifier

private abbrev fires (op : GroupFillQuantifier) (tally : GroupListPresenceTally) : Bool :=
  (op.evalTally tally).asConservativeVerdict.fires

theorem allGroupsFilled_complement_regions (tally : GroupListPresenceTally) :
    ¬ (fires .allGroupsFilled tally ∧ fires .notAllGroupsFilled tally) ∧
      ((fires .allGroupsFilled tally || fires .notAllGroupsFilled tally) = false ↔
        tally.empty = 0 ∧ 0 < tally.unavailable) := by
  simp only [fires, evalTally]
  all_goals (repeat' split) <;> simp [ValidationFillOutcome.asConservativeVerdict, Verdict.fires] at * <;>
    omega

theorem atLeastOneGroupFilled_complement_regions (tally : GroupListPresenceTally) :
    ¬ (fires .atLeastOneGroupFilled tally ∧ fires .noGroupFilled tally) ∧
      ((fires .atLeastOneGroupFilled tally || fires .noGroupFilled tally) = false ↔
        tally.filled = 0 ∧ 0 < tally.unavailable) := by
  simp only [fires, evalTally]
  all_goals (repeat' split) <;> simp [ValidationFillOutcome.asConservativeVerdict, Verdict.fires] at * <;>
    omega

theorem groupsNotCollectivelyFilled_excludes_complement (tally : GroupListPresenceTally) :
    fires .groupsNotCollectivelyFilled tally →
      fires .allGroupsFilled tally = false ∧ fires .noGroupFilled tally = false := by
  simp only [fires, evalTally]
  all_goals (repeat' split) <;> simp [ValidationFillOutcome.asConservativeVerdict, Verdict.fires] at * <;>
    omega

end GroupFillQuantifier

end A12Kernel
