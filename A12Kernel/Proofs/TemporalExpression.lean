import A12Kernel.Semantics.TemporalExpression

/-! # Temporal expression dependencies

An Analyze or Translate consumer may replace atom reads when every authored atom keeps its
classified value and the transformation evaluator stays fixed. Transformations may read additional
checked numeric operands; this law does not permit changing that environment without a separate
agreement argument. The expression retains the same value and missing provenance.
-/

namespace A12Kernel

theorem temporalExpression_evalWith_congr
    (expression : TemporalExpressionOf Atom Transform)
    (select : TemporalExtremumOp → α → α → α)
    (left right : Atom → Except Error (SimpleComparisonOperand α))
    (apply : Transform → SimpleComparisonOperand α → Except Error (SimpleComparisonOperand α))
    (agree : ∀ atom ∈ expression.atoms, left atom = right atom) :
    expression.evalWithResult select left apply = expression.evalWithResult select right apply := by
  cases expression with
  | atom source =>
      simpa only [TemporalExpressionOf.evalWithResult] using
        agree source (by simp [TemporalExpressionOf.atoms])
  | extremum operator first rest =>
      have hfirst := temporalExpression_evalWith_congr first select left right apply (by
        intro atom member
        apply agree atom
        simp only [TemporalExpressionOf.atoms, List.mem_append]
        exact Or.inl member)
      have hrest : rest.map (TemporalExpressionOf.evalWithResult select left apply) =
          rest.map (TemporalExpressionOf.evalWithResult select right apply) := by
        apply List.map_congr_left
        intro expression member
        apply temporalExpression_evalWith_congr expression select left right apply
        intro atom atomMember
        apply agree atom
        simp only [TemporalExpressionOf.atoms, List.mem_append, List.mem_flatMap]
        exact Or.inr ⟨expression, member, atomMember⟩
      have hrestM : rest.mapM (TemporalExpressionOf.evalWithResult select left apply) =
          rest.mapM (TemporalExpressionOf.evalWithResult select right apply) := by
        simpa only [List.mapM_map, Function.comp_def, id] using
          congrArg (fun results : List (Except Error (SimpleComparisonOperand α)) => results.mapM id) hrest
      simp only [TemporalExpressionOf.evalWithResult, hfirst, hrestM]
  | transform operation source =>
      have same := temporalExpression_evalWith_congr source select left right apply (by
        intro atom member
        exact agree atom (by simpa only [TemporalExpressionOf.atoms] using member))
      simp only [TemporalExpressionOf.evalWithResult, same]
termination_by sizeOf expression
decreasing_by
  all_goals subst_vars
  · simp_wf; omega
  · have := List.sizeOf_lt_of_mem member
    simp_wf
    omega
  · simp_wf

/-- A source evaluation failure crosses every unary transform without being reclassified as a
missing or poisoned operand. Computation consumers retain the failure's separate result channel. -/
theorem temporalExpression_evalWithResult_transform_error
    (source : TemporalExpressionOf Atom Transform) (operation : Transform)
    (select : TemporalExtremumOp → α → α → α)
    (read : Atom → Except Error (SimpleComparisonOperand α))
    (apply : Transform → SimpleComparisonOperand α → Except Error (SimpleComparisonOperand α))
    (cause : Error) (failed : source.evalWithResult select read apply = .error cause) :
    (TemporalExpressionOf.transform operation source).evalWithResult select read apply =
      .error cause := by
  simp only [TemporalExpressionOf.evalWithResult, failed]
  rfl

end A12Kernel
