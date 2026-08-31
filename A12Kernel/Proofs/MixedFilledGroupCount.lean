import A12Kernel.Elaboration.NumericValidation.Resolution

/-! # Mixed validation `NumberOfFilledGroups` laws

Both laws say the same thing from two sides: the widened carrier agrees with the established
fixed-only one exactly on fixed-only input, and a star is precisely what makes it differ. The pair
exists because the neighbouring field count shipped a movement rule keyed on the quantity that
coincides with the right one on every star-free fixture.
-/

namespace A12Kernel

private theorem validationOperandFold_fixed :
    ∀ (states : List GroupPresenceState) (accumulated : Nat),
      (states.map ValidationGroupCountOperand.fixed).foldl
        (fun total operand => total + operand.contribution) accumulated
        = accumulated + states.countP fun state => state.content := by
  intro states
  induction states with
  | nil => intro accumulated; simp
  | cons head tail ih =>
      intro accumulated
      simp only [List.map_cons, List.foldl_cons, List.countP_cons]
      rw [ih]
      simp only [ValidationGroupCountOperand.contribution]
      by_cases hContent : head.content
      · simp [hContent]; omega
      · simp [hContent]

/-- On a fixed-only list the widened count is exactly the established one, unknown arm included. So
this generalizes the fixed-only clause rather than competing with it, and no consumer of the old
carrier changes meaning by being routed through the new one. -/
theorem numberOfFilledGroupsForValidationOperands_fixed
    (states : List GroupPresenceState) :
    numberOfFilledGroupsForValidationOperands
        (states.map ValidationGroupCountOperand.fixed) =
      numberOfFilledGroups states := by
  simp only [numberOfFilledGroupsForValidationOperands, numberOfFilledGroups,
    List.any_map, Function.comp_def, ValidationGroupCountOperand.unavailable]
  by_cases hAny :
      states.any fun state => state.erroneous || !(state.relevance == .fullyRelevant)
  · simp [hAny]
  · simp only [hAny, if_false, Bool.false_eq_true]
    simp [validationOperandFold_fixed states 0]

private theorem sumOfOnes {α : Type} :
    ∀ items : List α, (items.map fun _ => 1).sum = items.length := by
  intro items
  induction items with
  | nil => rfl
  | cons _ tail ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; omega

/-- The declared extent is the operand list's length exactly on a fixed-only list. A starred member
contributes its declared row maximum instead, so the two quantities part company as soon as one star
carries a maximum above one — which is why the list length must not be reused as the extent once the
carrier is widened. -/
theorem mixedGroupCountExtent_fixed
    {model : FlatModel} (references : List ResolvedGroupReference) :
    ((references.map CheckedGroupCountOperand.fixed).mapM
        (CheckedGroupCountOperand.declaredExtent? (model := model))).map List.sum =
      some references.length := by
  have extents :
      (references.map CheckedGroupCountOperand.fixed).mapM
        (CheckedGroupCountOperand.declaredExtent? (model := model))
        = some (references.map fun _ => 1) := by
    induction references with
    | nil => rfl
    | cons _ tail ih =>
        simp [CheckedGroupCountOperand.declaredExtent?, ih]
  rw [extents]
  simp only [Option.map_some, sumOfOnes]

end A12Kernel
