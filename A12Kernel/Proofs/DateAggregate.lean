import A12Kernel.Proofs.DateComparison
import A12Kernel.Semantics.DateAggregate

/-! # Resolved stored-Date extremum laws -/

namespace A12Kernel

/-- On a strict chronological pair, minimum selects the earlier Date and maximum the later Date. -/
theorem dateExtremum_select_of_before (left right : FullDate)
    (before : left.before right = true) :
    DateExtremumOp.minimum.select left right = left ∧
      DateExtremumOp.maximum.select left right = right := by
  have reverse : right.before left = false := by
    simpa [DateComparisonOp.holds] using
      dateComparison_before_excludes_after left right before
  simp [DateExtremumOp.select, before, reverse]

/-- Selection never manufactures a Date outside its two inputs. -/
theorem dateExtremum_select_eq_left_or_right (op : DateExtremumOp)
    (left right : FullDate) :
    op.select left right = left ∨ op.select left right = right := by
  cases op <;> simp only [DateExtremumOp.select] <;>
    split <;> simp_all

/-- A Date extremum over no resolved operands has no synthetic identity value. -/
theorem dateExtremum_empty (op : DateExtremumOp)
    (hasUninstantiatedTail hasHaving : Bool) :
    evalDateExtremumAggregate op {
      operands := []
      hasUninstantiatedTail
      hasHaving
    } = .notEvaluated := by
  rfl

/-- A reached formally unavailable operand aborts before every suffix. -/
theorem dateExtremum_unknown_head (op : DateExtremumOp)
    (cause : FormalCause) (operands : List (SimpleComparisonOperand FullDate))
    (hasUninstantiatedTail hasHaving : Bool) :
    evalDateExtremumAggregate op {
      operands := .unknown cause :: operands
      hasUninstantiatedTail
      hasHaving
    } = .unknown cause := by
  rfl

/-- One fixed value with no missing structural source remains fixed for either selector. -/
theorem dateExtremum_fixed_singleton (op : DateExtremumOp)
    (value : FullDate) :
    evalDateExtremumAggregate op {
      operands := [.value value true]
      hasUninstantiatedTail := false
      hasHaving := false
    } = .value value true := by
  rfl

/-- An empty operand is skipped from selection but makes a later selected value symmetrically missing. -/
theorem dateExtremum_empty_prefix_marks_missing (op : DateExtremumOp)
    (value : FullDate) :
    evalDateExtremumAggregate op {
      operands := [.notEvaluated, .value value true]
      hasUninstantiatedTail := false
      hasHaving := false
    } = .value value false := by
  rfl

/-- Omitted-tail missingness reaches the established Date comparison polarity without another truth evaluator. -/
theorem dateExtremum_tail_comparison_firing (op : DateExtremumOp)
    (comparison : DateComparisonOp) (selected expected : FullDate)
    (holds : comparison.holds selected expected = true) :
    comparison.eval
        (evalDateExtremumAggregate op {
          operands := [.value selected true]
          hasUninstantiatedTail := true
          hasHaving := false
        })
        (.value expected true) = .fired .omission := by
  simpa [evalDateExtremumAggregate, scanDateExtremumOperands] using
    dateComparison_eval_missing_firing comparison selected expected false true
      (by decide) holds

end A12Kernel
