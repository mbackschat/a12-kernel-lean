import A12Kernel.Semantics.TemporalExpression

/-! # Temporal expression dependencies

An Analyze or Translate consumer may replace the read environment when every authored atom keeps
its classified value. The expression then retains the same value and missing provenance.
-/

namespace A12Kernel

theorem temporalExpression_evalWith_congr
    (expression : TemporalExpressionOf Atom)
    (select : TemporalExtremumOp → α → α → α)
    (left right : Atom → SimpleComparisonOperand α)
    (agree : ∀ atom ∈ expression.atoms, left atom = right atom) :
    expression.evalWith select left = expression.evalWith select right := by
  cases expression with
  | atom source =>
      simpa only [TemporalExpressionOf.evalWith] using
        agree source (by simp [TemporalExpressionOf.atoms])
  | extremum operator first rest =>
      have hfirst := temporalExpression_evalWith_congr first select left right (by
        intro atom member
        apply agree atom
        simp only [TemporalExpressionOf.atoms, List.mem_append]
        exact Or.inl member)
      have hrest : rest.map (TemporalExpressionOf.evalWith select left) =
          rest.map (TemporalExpressionOf.evalWith select right) := by
        apply List.map_congr_left
        intro expression member
        apply temporalExpression_evalWith_congr expression select left right
        intro atom atomMember
        apply agree atom
        simp only [TemporalExpressionOf.atoms, List.mem_append, List.mem_flatMap]
        exact Or.inr ⟨expression, member, atomMember⟩
      simp only [TemporalExpressionOf.evalWith, hfirst, hrest]
termination_by sizeOf expression
decreasing_by
  all_goals subst_vars
  · simp_wf; omega
  · have := List.sizeOf_lt_of_mem member
    simp_wf
    omega

end A12Kernel
