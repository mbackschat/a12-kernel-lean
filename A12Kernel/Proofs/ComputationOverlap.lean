import A12Kernel.Semantics.ComputationOverlap

namespace A12Kernel.ComputationOverlapSearch

/-- The scalar slot can settle the computation without invoking even a structurally failing list. -/
theorem scalarUsing_empty (scanList : ComputationOverlapSearch α → Except error ComputationConditionResult) :
    scalarUsing .empty scanList = .ok .notTrue := rfl

/-- The plural state never accumulates list values, so list-internal overlap cannot decide it. -/
theorem against_miss (overlaps : α → α → Bool) (scalar value : α)
    (miss : overlaps scalar value = false) :
    step overlaps (.against scalar) (.value value) = .inl (.against scalar) := by
  simp [step, miss]

/-- A deciding read excludes every later operand effect on the actual unfiltered evaluator. -/
theorem scan_deciding_prefix (overlaps : α → α → Bool)
    (read : slot → Except error (CellObservation α)) (first : slot) (rest : List slot)
    (state : ComputationOverlapSearch α) (cell : CellObservation α) (outcome : ComputationConditionResult)
    (observed : read first = .ok cell) (decides : state.step overlaps cell = .inr outcome) :
    scan overlaps read (first :: rest) state = .ok (.terminated outcome) := by
  simp [scan, observed, decides, bind, Except.bind, pure, Except.pure]

/-- Empty observations preserve both the scalar and any-pair search states. -/
theorem scan_emptyCells (overlaps : α → α → Bool)
    (read : slot → Except error (CellObservation α)) (slots : List slot)
    (state : ComputationOverlapSearch α)
    (emptyCells : ∀ slot ∈ slots, read slot = .ok .empty) :
    scan overlaps read slots state = .ok (.exhausted state) := by
  induction slots with
  | nil => rfl
  | cons first rest ih =>
      simp only [scan, emptyCells first (by simp), bind, Except.bind, step]
      exact ih (fun slot member => emptyCells slot (by simp [member]))

end A12Kernel.ComputationOverlapSearch
