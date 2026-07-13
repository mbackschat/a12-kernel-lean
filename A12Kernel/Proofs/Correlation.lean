import A12Kernel.Semantics.Correlation

/-! # Proofs for explicit inner/outer Having correlation -/

namespace A12Kernel

private theorem K.and_eq_tru_iff (left right : K) :
    K.and left right = .tru ↔ left = .tru ∧ right = .tru := by
  cases left <;> cases right <;> decide

/-- An outer numeric reference is stable when only the candidate/inner row changes. -/
theorem outer_number_reference_stable (rows : SingleGroupValidationContext)
    (field : FlatNumberField) (outerRow inner₁ inner₂ : RowIndex) :
    ({ origin := HavingOrigin.outer, field } : HavingNumberRef).resolve rows
        { innerRow := inner₁, outerRow } =
      ({ origin := HavingOrigin.outer, field } : HavingNumberRef).resolve rows
        { innerRow := inner₂, outerRow } := by
  rfl

/-- An inner numeric reference is local to its candidate and stable when only the
    captured outer row changes. -/
theorem inner_number_reference_local (rows : SingleGroupValidationContext)
    (field : FlatNumberField) (innerRow outer₁ outer₂ : RowIndex) :
    ({ origin := HavingOrigin.inner, field } : HavingNumberRef).resolve rows
        { innerRow, outerRow := outer₁ } =
      ({ origin := HavingOrigin.inner, field } : HavingNumberRef).resolve rows
        { innerRow, outerRow := outer₂ } := by
  rfl

/-- Executable correlated-filter truth agrees with the independently stated structural
    predicate. -/
theorem correlatedHaving_truth_iff_holds (condition : CorrelatedHaving)
    (rows : SingleGroupValidationContext) (frame : SingleGroupFilterFrame) :
    condition.evalTruth rows frame = .tru ↔ condition.Holds rows frame := by
  induction condition with
  | compareNumbers op left right =>
      cases leftResolved : left.resolve rows frame <;>
        cases rightResolved : right.resolve rows frame <;>
        simp [CorrelatedHaving.evalTruth, CorrelatedHaving.Holds,
          CorrelationComparisonOp.evalOperands, leftResolved, rightResolved]
  | compareRepetitions op left right =>
      simp [CorrelatedHaving.evalTruth, CorrelatedHaving.Holds]
  | and left right leftInduction rightInduction =>
      change K.and (left.evalTruth rows frame) (right.evalTruth rows frame) = .tru ↔
        left.Holds rows frame ∧ right.Holds rows frame
      rw [K.and_eq_tru_iff, leftInduction, rightInduction]

private theorem correlatedKeeps_eq_true_iff (star : SingleCorrelatedStar)
    (context : CapturedSingleGroupContext) (row : RowIndex) :
    star.keeps context row = true ↔
      star.having.condition.Holds context.rows (context.frame row) := by
  simp only [SingleCorrelatedStar.keeps]
  rw [← correlatedHaving_truth_iff_holds]
  cases star.having.condition.evalTruth context.rows (context.frame row) <;> decide

private theorem selectCorrelatedRows_sound_on (star : SingleCorrelatedStar)
    (context : CapturedSingleGroupContext) (rows : List RowIndex) :
    SelectCorrelatedRows star context rows (rows.filter (star.keeps context)) := by
  induction rows with
  | nil => exact .nil
  | cons row rows tail =>
      by_cases kept : star.having.condition.Holds context.rows (context.frame row)
      · have keepBool := (correlatedKeeps_eq_true_iff star context row).2 kept
        simpa [keepBool] using SelectCorrelatedRows.keep kept tail
      · cases keepBool : star.keeps context row with
        | false => simpa [keepBool] using SelectCorrelatedRows.drop kept tail
        | true =>
            exact False.elim
              (kept ((correlatedKeeps_eq_true_iff star context row).1 keepBool))

private theorem selectCorrelatedRows_complete_on {star : SingleCorrelatedStar}
    {context : CapturedSingleGroupContext} {rows selected : List RowIndex}
    (derivation : SelectCorrelatedRows star context rows selected) :
    rows.filter (star.keeps context) = selected := by
  induction derivation with
  | nil => rfl
  | @keep row rows selected kept tail inductionHypothesis =>
      have keepBool := (correlatedKeeps_eq_true_iff star context row).2 kept
      simp [keepBool, inductionHypothesis]
  | @drop row rows selected dropped tail inductionHypothesis =>
      cases keepBool : star.keeps context row with
      | false => simp [keepBool, inductionHypothesis]
      | true =>
          exact False.elim
            (dropped ((correlatedKeeps_eq_true_iff star context row).1 keepBool))

/-- Exact ordered agreement between the naive correlated selector and its declarative
    keep/drop relation. -/
theorem selectCorrelatedRows_iff (star : SingleCorrelatedStar)
    (context : CapturedSingleGroupContext) (selected : List RowIndex) :
    star.select context = selected ↔
      SelectCorrelatedRows star context context.rows.candidates selected := by
  constructor
  · intro execution
    rw [← execution]
    exact selectCorrelatedRows_sound_on star context context.rows.candidates
  · intro derivation
    exact selectCorrelatedRows_complete_on derivation

/-- `CurrentRepetition(inner) != CurrentRepetition($outer)` is false on the outer row
    itself. Self-exclusion is therefore explicit and structural. -/
theorem currentRepetition_selfExclusion_false
    (rows : SingleGroupValidationContext) (outerRow : RowIndex) :
    (CorrelatedHaving.compareRepetitions .notEqual .inner .outer).evalTruth rows
      { innerRow := outerRow, outerRow } = .fls := by
  simp [CorrelatedHaving.evalTruth, CorrelationComparisonOp.holdsRow,
    SingleGroupFilterFrame.rowAt]

/-- Adding explicit repetition inequality in front of any rest condition removes the
    captured outer row from the executable selection. -/
theorem explicitSelfExclusion_drops_outer (star : SingleCorrelatedStar)
    (rows : SingleGroupValidationContext) (outerRow : RowIndex)
    (rest : CorrelatedHaving)
    (condition : star.having.condition =
      .and (.compareRepetitions .notEqual .inner .outer) rest) :
    outerRow ∉ star.select { rows, outerRow } := by
  simp [SingleCorrelatedStar.select, SingleCorrelatedStar.keeps, condition,
    CapturedSingleGroupContext.frame, CorrelatedHaving.evalTruth,
    CorrelationComparisonOp.holdsRow,
    SingleGroupFilterFrame.rowAt, K.and]

/-- A candidate with a usable numeric cell is selected by reflexive inner/outer field
    equality. No implicit exclusion is present. -/
theorem sameFieldEquality_selfMatches (star : SingleCorrelatedStar)
    (rows : SingleGroupValidationContext) (row : RowIndex)
    (field : FlatNumberField) (value : Rat)
    (condition : star.having.condition = .compareNumbers .equal
      { origin := .inner, field } { origin := .outer, field })
    (candidate : row ∈ rows.candidates)
    (usable : ({ origin := HavingOrigin.inner, field } : HavingNumberRef).resolve rows
      { innerRow := row, outerRow := row } = .value value) :
    row ∈ star.select { rows, outerRow := row } := by
  have outerUsable :
      ({ origin := HavingOrigin.outer, field } : HavingNumberRef).resolve rows
        { innerRow := row, outerRow := row } = .value value := by
    simpa [HavingNumberRef.resolve, SingleGroupFilterFrame.rowAt] using usable
  simp [SingleCorrelatedStar.select, candidate, SingleCorrelatedStar.keeps, condition,
    CapturedSingleGroupContext.frame, CorrelatedHaving.evalTruth,
    CorrelationComparisonOp.evalOperands, usable, outerUsable,
    CorrelationComparisonOp.holdsRat]

end A12Kernel
