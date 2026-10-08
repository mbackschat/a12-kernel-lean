import A12Kernel.Semantics.TemporalExpression
import A12Kernel.Semantics.ScalarTemporalDifference

/-! # Temporal expression dependencies and argument evaluation

An Analyze or Translate consumer may replace atom reads when every authored atom keeps its
classified result and the operation evaluator stays fixed. Extra operands read by an operation
require a separate environment agreement. Strict application preserves reached failure order.
-/

namespace A12Kernel

theorem temporalExpression_evalWith_congr
    (expression : TemporalExpressionOf Atom Operation)
    (left right : Atom → Except Error Operand)
    (apply : Operation → List Operand → Except Error Operand)
    (agree : ∀ atom ∈ expression.atoms, left atom = right atom) :
    expression.evalWithResult left apply = expression.evalWithResult right apply := by
  cases expression with
  | atom source =>
      simpa only [TemporalExpressionOf.evalWithResult_atom, TemporalExpressionOf.evalWithResult_apply] using
        agree source (by simp [TemporalExpressionOf.atoms])
  | apply operation first rest =>
      have hfirst := temporalExpression_evalWith_congr first left right apply (by
        intro atom member
        apply agree atom
        simp only [TemporalExpressionOf.atoms, List.mem_append]
        exact Or.inl member)
      have hrest : rest.map (TemporalExpressionOf.evalWithResult left apply) =
          rest.map (TemporalExpressionOf.evalWithResult right apply) := by
        apply List.map_congr_left
        intro expression member
        apply temporalExpression_evalWith_congr expression left right apply
        intro atom atomMember
        apply agree atom
        simp only [TemporalExpressionOf.atoms, List.mem_append, List.mem_flatMap]
        exact Or.inr ⟨expression, member, atomMember⟩
      have hrestM : rest.mapM (TemporalExpressionOf.evalWithResult left apply) =
          rest.mapM (TemporalExpressionOf.evalWithResult right apply) := by
        simpa only [List.mapM_map, Function.comp_def, id] using
          congrArg (fun results : List (Except Error Operand) => results.mapM id) hrest
      simp only [TemporalExpressionOf.evalWithResult_apply, hfirst, hrestM]
termination_by sizeOf expression
decreasing_by
  all_goals subst_vars
  · simp_wf; omega
  · have := List.sizeOf_lt_of_mem member
    simp_wf
    omega

/-- The first reached failure prevents later argument evaluation and the operation itself. -/
theorem temporalExpression_evalWithResult_apply_head_error
    (source : TemporalExpressionOf Atom Operation) (rest : List (TemporalExpressionOf Atom Operation))
    (operation : Operation) (read : Atom → Except Error Operand)
    (apply : Operation → List Operand → Except Error Operand)
    (cause : Error) (failed : source.evalWithResult read apply = .error cause) :
    (TemporalExpressionOf.apply operation source rest).evalWithResult read apply = .error cause := by
  simp only [TemporalExpressionOf.evalWithResult_apply, failed]
  rfl

/-- Any successful first result still reaches later arguments, including an absent or non-relevant
value supplied by a temporal consumer. Its representation must not make the application skip them. -/
theorem temporalExpression_evalWithResult_apply_tail_error
    (source : TemporalExpressionOf Atom Operation) (rest : List (TemporalExpressionOf Atom Operation))
    (operation : Operation) (read : Atom → Except Error Operand)
    (apply : Operation → List Operand → Except Error Operand)
    (value : Operand) (cause : Error)
    (reached : source.evalWithResult read apply = .ok value)
    (failed : rest.mapM (TemporalExpressionOf.evalWithResult read apply) = .error cause) :
    (TemporalExpressionOf.apply operation source rest).evalWithResult read apply = .error cause := by
  simp only [TemporalExpressionOf.evalWithResult_apply, reached, failed]
  rfl

/-- Unary transformations specialize the same ordered-application failure law. -/
theorem temporalExpression_evalWithResult_transform_error
    (source : TemporalExpressionOf Atom Operation) (operation : Operation)
    (read : Atom → Except Error Operand)
    (apply : Operation → List Operand → Except Error Operand)
    (cause : Error) (failed : source.evalWithResult read apply = .error cause) :
    (TemporalExpressionOf.apply operation source []).evalWithResult read apply = .error cause :=
  temporalExpression_evalWithResult_apply_head_error source [] operation read apply cause failed

/-- A formal first operand suppresses any later computation read, independently of its result. -/
theorem readTemporalPair_computation_first_formal
    (read : Source → Except Error Operand) (formalCause? : Operand → Option FormalCause)
    (left right : Source) (value : Operand) (cause : FormalCause)
    (first : read left = .ok value) (formal : formalCause? value = some cause) :
    readTemporalPair .computation read formalCause? left right = .ok (.error cause) := by
  simp [readTemporalPair, readTemporalPairWith, bind, Except.bind, pure, Except.pure, first, formal]

/-- Validation retains a later structural failure even when the first result has a formal cause. -/
theorem readTemporalPair_validation_second_fault
    (read : Source → Except Error Operand) (formalCause? : Operand → Option FormalCause)
    (left right : Source) (value : Operand) (fault : Error)
    (first : read left = .ok value) (second : read right = .error fault) :
    readTemporalPair .validation read formalCause? left right = .error fault := by
  simp [readTemporalPair, readTemporalPairWith, bind, Except.bind, first, second]

end A12Kernel
