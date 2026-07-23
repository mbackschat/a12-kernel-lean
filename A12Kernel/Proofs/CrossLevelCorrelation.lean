import A12Kernel.Proofs.Correlation
import A12Kernel.Semantics.CrossLevelCorrelation

/-! # Proofs for one-star correlation with a two-level captured environment -/

namespace A12Kernel

/-- Both positive coordinates of an environment with two distinct named levels resolve uniquely. -/
theorem crossLevelCorrelation_outer_levels_resolve
    (context : CapturedTwoLevelOuterStarContext)
    (distinct : context.rows.starLevel ≠ context.rows.descendantLevel)
    (starPositive : context.outerStarRow ≠ 0)
    (descendantPositive : context.outerDescendantRow ≠ 0) :
    context.outerEnv.uniqueRowAt? context.rows.starLevel =
        some context.outerStarRow ∧
      context.outerEnv.uniqueRowAt? context.rows.descendantLevel =
        some context.outerDescendantRow := by
  have reverse : context.rows.descendantLevel ≠ context.rows.starLevel :=
    Ne.symm distinct
  simp [CapturedTwoLevelOuterStarContext.outerEnv, Env.uniqueRowAt?,
    Env.bindingAt, Except.toOption, distinct, reverse, starPositive,
    descendantPositive]

/-- When the captured rows differ, the full outer environment cannot be represented by
    one row value shared by both named levels. -/
theorem crossLevelCorrelation_no_single_outer_row
    (context : CapturedTwoLevelOuterStarContext)
    (distinctLevels : context.rows.starLevel ≠ context.rows.descendantLevel)
    (distinctRows : context.outerStarRow ≠ context.outerDescendantRow)
    (starPositive : context.outerStarRow ≠ 0)
    (descendantPositive : context.outerDescendantRow ≠ 0) :
    ¬∃ row,
      context.outerEnv.uniqueRowAt? context.rows.starLevel = some row ∧
        context.outerEnv.uniqueRowAt? context.rows.descendantLevel = some row := by
  rcases crossLevelCorrelation_outer_levels_resolve context distinctLevels
    starPositive descendantPositive with
    ⟨starResolved, descendantResolved⟩
  have reverseRows : context.outerDescendantRow ≠ context.outerStarRow :=
    Ne.symm distinctRows
  simp [starResolved, descendantResolved, reverseRows]

end A12Kernel
