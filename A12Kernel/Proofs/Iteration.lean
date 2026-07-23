import A12Kernel.Semantics.Iteration

/-! # Proofs for ordered single-level Having selection -/

namespace A12Kernel

private theorem keeps_eq_true_iff (star : SingleStar)
    (context : SingleGroupValidationContext) (row : RowIndex) :
    star.keeps context row = true ↔ star.KeepsRow context row := by
  cases having : star.having with
  | none => simp [SingleStar.keeps, SingleStar.KeepsRow, having]
  | some condition =>
      simp only [SingleStar.keeps, SingleStar.KeepsRow, having]
      cases verdict : condition.evalFull (context.atRow row) true with
      | notFired => simp [Verdict.keepsHaving]
      | fired polarity => simp [Verdict.keepsHaving]
      | unknown => simp [Verdict.keepsHaving]

private theorem selectRows_sound_on (star : SingleStar)
    (context : SingleGroupValidationContext) (rows : List RowIndex) :
    SelectRows star context rows (rows.filter (star.keeps context)) := by
  induction rows with
  | nil => exact .nil
  | cons row rows tail =>
      by_cases kept : star.KeepsRow context row
      · have keepBool := (keeps_eq_true_iff star context row).2 kept
        simpa [keepBool] using SelectRows.keep kept tail
      · cases keepBool : star.keeps context row with
        | false => simpa [keepBool] using SelectRows.drop kept tail
        | true => exact False.elim (kept ((keeps_eq_true_iff star context row).1 keepBool))

private theorem selectRows_complete_on {star : SingleStar}
    {context : SingleGroupValidationContext} {rows selected : List RowIndex}
    (derivation : SelectRows star context rows selected) :
    rows.filter (star.keeps context) = selected := by
  induction derivation with
  | nil => rfl
  | @keep row rows selected kept tail inductionHypothesis =>
      have keepBool := (keeps_eq_true_iff star context row).2 kept
      simp [keepBool, inductionHypothesis]
  | @drop row rows selected dropped tail inductionHypothesis =>
      cases keepBool : star.keeps context row with
      | false =>
          simp [keepBool, inductionHypothesis]
      | true => exact False.elim (dropped ((keeps_eq_true_iff star context row).1 keepBool))

/-- The executable ordered selector and the independent keep/drop relation agree on the
    exact output list, not merely on set membership. -/
theorem selectRows_iff (star : SingleStar) (context : SingleGroupValidationContext)
    (selected : List RowIndex) :
    star.select context = selected ↔
      SelectRows star context context.candidates selected := by
  constructor
  · intro execution
    rw [← execution]
    exact selectRows_sound_on star context context.candidates
  · intro derivation
    exact selectRows_complete_on derivation

private theorem NumberFold.classifyRows_congr
    (left right : SingleGroupValidationContext)
    (field : FlatNumberField) (rows : List RowIndex)
    (agree : ∀ row, row ∈ rows → left.read row field.id = right.read row field.id) :
    rows.map (NumberFold.classifyRow left field) =
      rows.map (NumberFold.classifyRow right field) := by
  induction rows with
  | nil => rfl
  | cons row rows tail =>
      have headAgree := agree row (by simp)
      have tailAgree : ∀ next, next ∈ rows →
          left.read next field.id = right.read next field.id := by
        intro next member
        exact agree next (by simp [member])
      have headClassified :
          NumberFold.classifyRow left field row =
            NumberFold.classifyRow right field row := by
        unfold NumberFold.classifyRow FlatNumberField.valueListCell
          FlatNumberField.valueListCellAt
          SingleGroupValidationContext.atRow FlatContext.observeAt
        change
          (observeCell .validation (left.read row field.id)).asNumberValueListCell =
            (observeCell .validation (right.read row field.id)).asNumberValueListCell
        rw [headAgree]
      rw [List.map_cons, List.map_cons, headClassified, tail tailAgree]

private theorem NumberFold.sumRows_congr (left right : SingleGroupValidationContext)
    (field : FlatNumberField) (rows : List RowIndex)
    (agree : ∀ row, row ∈ rows → left.read row field.id = right.read row field.id) :
    NumberFold.sumRows left field rows = NumberFold.sumRows right field rows := by
  unfold NumberFold.sumRows
  rw [NumberFold.classifyRows_congr left right field rows agree]

/-- Selection is a real read boundary: once two evaluations select the same ordered
    rows, their sums need agree only on consumed cells in those selected rows. Consumed
    cells in every filter-dropped row may differ arbitrarily. -/
theorem sumSelected_filter_before_consumer (star : SingleStar)
    (left right : SingleGroupValidationContext)
    (sameSelection : star.select left = star.select right)
    (agreeSelected : ∀ row, row ∈ star.select left →
      left.read row star.valueField.id = right.read row star.valueField.id) :
    star.sumSelected left = star.sumSelected right := by
  unfold SingleStar.sumSelected
  calc
    NumberFold.sumRows left star.valueField (star.select left) =
        NumberFold.sumRows right star.valueField (star.select left) :=
      NumberFold.sumRows_congr left right star.valueField (star.select left) agreeSelected
    _ = NumberFold.sumRows right star.valueField (star.select right) := by
      rw [sameSelection]

end A12Kernel
