import A12Kernel.Semantics.Correlation

/-! # Proofs for explicit inner/outer Having correlation -/

namespace A12Kernel

private theorem K.and_eq_tru_iff (left right : K) :
    K.and left right = .tru ↔ left = .tru ∧ right = .tru := by
  cases left <;> cases right <;> decide

private theorem anyFilledTruth_congr (field : FlatNumberField)
    (left right : SingleGroupValidationContext) (rows : List RowIndex)
    (agree : ∀ row, row ∈ rows →
      observeCell .validation (left.read row field.id) =
        observeCell .validation (right.read row field.id)) :
    field.anyFilledTruth left rows = field.anyFilledTruth right rows := by
  induction rows with
  | nil => rfl
  | cons row rows inductionHypothesis =>
      have headAgreement := agree row (by simp)
      have tailAgreement : ∀ tailRow, tailRow ∈ rows →
          observeCell .validation (left.read tailRow field.id) =
            observeCell .validation (right.read tailRow field.id) := by
        intro tailRow member
        exact agree tailRow (by simp [member])
      simp only [FlatNumberField.anyFilledTruth]
      rw [show field.filledTruthAt left row = field.filledTruthAt right row by
        unfold FlatNumberField.filledTruthAt
        rw [headAgreement]]
      rw [inductionHypothesis tailAgreement]

/-- A captured numeric reference is independent of the candidate environment. -/
theorem outer_number_reference_stableIn (context : CorrelationContext)
    (field : FlatNumberField) (outerEnv inner₁ inner₂ : Env) :
    ({ origin := HavingOrigin.outer, field } : HavingNumberRef).resolveIn context
        { innerEnv := inner₁, outerEnv } =
      ({ origin := HavingOrigin.outer, field } : HavingNumberRef).resolveIn context
        { innerEnv := inner₂, outerEnv } := by
  rfl

/-- A captured repetition reference reads its named level from the outer environment,
    independently of the candidate environment. -/
theorem outer_repetition_reference_stableIn (outerEnv inner₁ inner₂ : Env)
    (level : RepeatableLevel) :
    ({ innerEnv := inner₁, outerEnv } : CorrelationFrame).rowAt?
        ({ origin := .outer, level } : HavingRepetitionRef) =
      ({ innerEnv := inner₂, outerEnv } : CorrelationFrame).rowAt?
        ({ origin := .outer, level } : HavingRepetitionRef) := by
  rfl

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

/-- The shared environment-indexed evaluator agrees with its independently stated
    structural predicate. -/
theorem correlatedHaving_truthIn_iff_holdsIn (condition : CorrelatedHaving)
    (context : CorrelationContext) (frame : CorrelationFrame) :
    condition.evalTruthIn context frame = .tru ↔
      condition.HoldsIn context frame := by
  induction condition with
  | compareNumbers op left right =>
      cases leftResolved : left.resolveIn context frame <;>
        cases rightResolved : right.resolveIn context frame <;>
        simp [CorrelatedHaving.evalTruthIn, CorrelatedHaving.HoldsIn,
          CorrelationComparisonOp.evalOperands, leftResolved, rightResolved]
  | compareRepetitions op left right =>
      cases leftResolved : frame.rowAt? left <;>
        cases rightResolved : frame.rowAt? right <;>
        simp [CorrelatedHaving.evalTruthIn, CorrelatedHaving.HoldsIn,
          CorrelationComparisonOp.evalRows, leftResolved, rightResolved]
  | and left right leftInduction rightInduction =>
      change K.and (left.evalTruthIn context frame) (right.evalTruthIn context frame) =
          .tru ↔
        left.HoldsIn context frame ∧ right.HoldsIn context frame
      rw [K.and_eq_tru_iff, leftInduction, rightInduction]

/-- The established one-group wrapper inherits the shared evaluator/relation bridge. -/
theorem correlatedHaving_truth_iff_holds (condition : CorrelatedHaving)
    (rows : SingleGroupValidationContext) (frame : SingleGroupFilterFrame) :
    condition.evalTruth rows frame = .tru ↔ condition.Holds rows frame := by
  exact correlatedHaving_truthIn_iff_holdsIn condition rows.asCorrelationContext
    (frame.toCorrelationFrame rows)

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

/-- Once correlated selection agrees, the guarded presence consumer observes only the
    outer guard cell and consumer cells in the selected rows. -/
theorem evalGuardedAnyFilledOn_filter_before_consumer
    (star : SingleCorrelatedStar) (guardField : FlatNumberField)
    (left right : CapturedSingleGroupContext)
    (sameSelection : star.select left = star.select right)
    (agreeGuard :
      observeCell .validation (left.rows.read left.outerRow guardField.id) =
        observeCell .validation (right.rows.read right.outerRow guardField.id))
    (agreeSelected : ∀ row, row ∈ star.select left →
      observeCell .validation (left.rows.read row star.valueField.id) =
        observeCell .validation (right.rows.read row star.valueField.id)) :
    star.evalGuardedAnyFilledOn guardField left =
      star.evalGuardedAnyFilledOn guardField right := by
  have guardTruth :
      guardField.filledTruthAt left.rows left.outerRow =
        guardField.filledTruthAt right.rows right.outerRow := by
    unfold FlatNumberField.filledTruthAt
    rw [agreeGuard]
  have selectedTruth := anyFilledTruth_congr star.valueField left.rows right.rows
    (star.select left) agreeSelected
  simp only [SingleCorrelatedStar.evalGuardedAnyFilledOn,
    SingleCorrelatedStar.evalSelectedAnyFilled]
  rw [guardTruth, ← sameSelection, selectedTruth]

/-- `CurrentRepetition(inner) != CurrentRepetition($outer)` is false on the outer row
    itself. Self-exclusion is therefore explicit and structural. -/
theorem currentRepetition_selfExclusion_false
    (rows : SingleGroupValidationContext) (outerRow : RowIndex) :
    (CorrelatedHaving.compareRepetitions .notEqual
      { origin := .inner, level := rows.group }
      { origin := .outer, level := rows.group }).evalTruth rows
      { innerRow := outerRow, outerRow } = .fls := by
  simp [CorrelatedHaving.evalTruth, CorrelatedHaving.evalTruthIn,
    CorrelationComparisonOp.evalRows, CorrelationFrame.rowAt?,
    CorrelationFrame.envAt, SingleGroupFilterFrame.toCorrelationFrame,
    SingleGroupValidationContext.envAt, Env.uniqueRowAt?,
    CorrelationComparisonOp.holdsRow]

/-- Adding explicit repetition inequality in front of any rest condition removes the
    captured outer row from the executable selection. -/
theorem explicitSelfExclusion_drops_outer (star : SingleCorrelatedStar)
    (rows : SingleGroupValidationContext) (outerRow : RowIndex)
    (rest : CorrelatedHaving)
    (condition : star.having.condition =
      .and (.compareRepetitions .notEqual
        { origin := .inner, level := rows.group }
        { origin := .outer, level := rows.group }) rest) :
    outerRow ∉ star.select { rows, outerRow } := by
  simp [SingleCorrelatedStar.select, SingleCorrelatedStar.keeps, condition,
    CapturedSingleGroupContext.frame, CorrelatedHaving.evalTruth,
    CorrelatedHaving.evalTruthIn, CorrelationComparisonOp.evalRows,
    CorrelationFrame.rowAt?, CorrelationFrame.envAt,
    SingleGroupFilterFrame.toCorrelationFrame, SingleGroupValidationContext.envAt,
    Env.uniqueRowAt?, CorrelationComparisonOp.holdsRow, K.and]

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
  have innerUsableIn :
      ({ origin := HavingOrigin.inner, field } : HavingNumberRef).resolveIn
        rows.asCorrelationContext
        (({ innerRow := row, outerRow := row } :
          SingleGroupFilterFrame).toCorrelationFrame rows) = .value value := by
    exact usable
  have outerUsable :
      ({ origin := HavingOrigin.outer, field } : HavingNumberRef).resolve rows
        { innerRow := row, outerRow := row } = .value value := by
    simpa [HavingNumberRef.resolve, HavingNumberRef.resolveIn,
      SingleGroupFilterFrame.toCorrelationFrame, CorrelationFrame.envAt] using usable
  have outerUsableIn :
      ({ origin := HavingOrigin.outer, field } : HavingNumberRef).resolveIn
        rows.asCorrelationContext
        (({ innerRow := row, outerRow := row } :
          SingleGroupFilterFrame).toCorrelationFrame rows) = .value value := by
    exact outerUsable
  simp [SingleCorrelatedStar.select, candidate, SingleCorrelatedStar.keeps, condition,
    CapturedSingleGroupContext.frame, CorrelatedHaving.evalTruth,
    CorrelatedHaving.evalTruthIn, CorrelationComparisonOp.evalOperands,
    innerUsableIn, outerUsableIn,
    CorrelationComparisonOp.holdsRat, NumericComparisonOp.holds]

end A12Kernel
