import A12Kernel.Proofs.DateComparison
import A12Kernel.Semantics.DateAggregate

/-! # Resolved stored-Date extremum laws -/

namespace A12Kernel

/-- A temporal extremum over no resolved operands has no synthetic identity value. -/
theorem temporalExtremum_empty (select : α → α → α)
    (hasUninstantiatedTail hasHaving : Bool) :
    evalTemporalExtremumAggregate select {
      operands := []
      hasUninstantiatedTail
      hasHaving
    } = .notEvaluated := by
  rfl

/-- A reached formally unavailable temporal operand aborts before every suffix. -/
theorem temporalExtremum_unknown_head (select : α → α → α)
    (cause : FormalCause) (operands : List (SimpleComparisonOperand α))
    (hasUninstantiatedTail hasHaving : Bool) :
    evalTemporalExtremumAggregate select {
      operands := .unknown cause :: operands
      hasUninstantiatedTail
      hasHaving
    } = .unknown cause := by
  rfl

/-- One fixed temporal value with no structural missing source remains fixed. -/
theorem temporalExtremum_fixed_singleton (select : α → α → α)
    (value : α) :
    evalTemporalExtremumAggregate select {
      operands := [.value value true]
      hasUninstantiatedTail := false
      hasHaving := false
    } = .value value true := by
  rfl

/-- An empty temporal operand is skipped from selection but makes a later selected value symmetrically missing. -/
theorem temporalExtremum_empty_prefix_marks_missing
    (select : α → α → α) (value : α) :
    evalTemporalExtremumAggregate select {
      operands := [.notEvaluated, .value value true]
      hasUninstantiatedTail := false
      hasHaving := false
    } = .value value false := by
  rfl

/-- On a strict chronological pair, minimum selects the earlier Date and maximum the later Date. -/
theorem dateExtremum_select_of_before (left right : FullDate)
    (before : left.before right = true) :
    TemporalExtremumOp.minimum.select left right = left ∧
      TemporalExtremumOp.maximum.select left right = right := by
  have reverse : right.before left = false := by
    simpa [DateComparisonOp.holds] using
      dateComparison_before_excludes_after left right before
  simp [TemporalExtremumOp.select, before, reverse]

/-- Selection never manufactures a Date outside its two inputs. -/
theorem dateExtremum_select_eq_left_or_right (op : TemporalExtremumOp)
    (left right : FullDate) :
    op.select left right = left ∨ op.select left right = right := by
  cases op <;> simp only [TemporalExtremumOp.select] <;>
    split <;> simp_all

/-- A Date extremum over no resolved operands has no synthetic identity value. -/
theorem dateExtremum_empty (op : TemporalExtremumOp)
    (hasUninstantiatedTail hasHaving : Bool) :
    evalDateExtremumAggregate op {
      operands := []
      hasUninstantiatedTail
      hasHaving
    } = .notEvaluated := by
  exact temporalExtremum_empty op.select hasUninstantiatedTail hasHaving

/-- A reached formally unavailable operand aborts before every suffix. -/
theorem dateExtremum_unknown_head (op : TemporalExtremumOp)
    (cause : FormalCause) (operands : List (SimpleComparisonOperand FullDate))
    (hasUninstantiatedTail hasHaving : Bool) :
    evalDateExtremumAggregate op {
      operands := .unknown cause :: operands
      hasUninstantiatedTail
      hasHaving
    } = .unknown cause := by
  exact temporalExtremum_unknown_head op.select cause operands
    hasUninstantiatedTail hasHaving

/-- One fixed value with no missing structural source remains fixed for either selector. -/
theorem dateExtremum_fixed_singleton (op : TemporalExtremumOp)
    (value : FullDate) :
    evalDateExtremumAggregate op {
      operands := [.value value true]
      hasUninstantiatedTail := false
      hasHaving := false
    } = .value value true := by
  exact temporalExtremum_fixed_singleton op.select value

/-- An empty operand is skipped from selection but makes a later selected value symmetrically missing. -/
theorem dateExtremum_empty_prefix_marks_missing (op : TemporalExtremumOp)
    (value : FullDate) :
    evalDateExtremumAggregate op {
      operands := [.notEvaluated, .value value true]
      hasUninstantiatedTail := false
      hasHaving := false
    } = .value value false := by
  exact temporalExtremum_empty_prefix_marks_missing op.select value

/-- Omitted-tail missingness reaches the established Date comparison polarity without another truth evaluator. -/
theorem dateExtremum_tail_comparison_firing (op : TemporalExtremumOp)
    (comparison : DateComparisonOp) (selected expected : FullDate)
    (holds : comparison.holds selected expected = true) :
    comparison.eval
        (evalDateExtremumAggregate op {
          operands := [.value selected true]
          hasUninstantiatedTail := true
          hasHaving := false
        })
        (.value expected true) = .fired .omission := by
  simpa [evalDateExtremumAggregate, evalTemporalExtremumAggregate,
    scanDateExtremumOperands, scanTemporalExtremumOperands] using
    dateComparison_eval_missing_firing comparison selected expected false true
      (by decide) holds

end A12Kernel
