import A12Kernel.Semantics.RuleIterationDomain

namespace A12Kernel.RuleIterationDomain

/-- A small declared space does not consult document occupancy. -/
theorem axis_dense (occupied : List (List Nat)) (stem : List Nat) (capacity : Nat) :
    axis false occupied stem capacity = (List.range capacity).map (· + 1) := by
  simp [axis]

/-- Every axis reset keeps its initial slot, even without any occupied prefix. -/
theorem axis_first (sparse : Bool) (occupied : List (List Nat))
    (stem : List Nat) (capacity : Nat) (positive : 0 < capacity) :
    1 ∈ axis sparse occupied stem capacity := by
  simp only [axis, List.mem_filter, List.mem_map]
  exact ⟨⟨0, by simpa using positive, rfl⟩, by simp⟩

/-- The occupancy-independent account composes through every nesting level. -/
theorem descend_dense (left right : List (List Nat)) (stem bounds : List Nat) :
    descend false left stem bounds = descend false right stem bounds := by
  induction bounds generalizing stem with
  | nil => rfl
  | cons capacity rest ih =>
      simp only [descend, axis_dense]
      congr 1
      funext i
      exact ih (stem ++ [i])

/-- No child fallback can manufacture a root the dispatcher did not select. -/
theorem no_dispatched_roots (bounds : List Nat) (occupied : List (List Nat)) :
    coordinates bounds occupied [] = [] := by
  cases bounds <;> simp [coordinates]

end A12Kernel.RuleIterationDomain
