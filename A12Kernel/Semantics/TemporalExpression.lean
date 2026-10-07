import A12Kernel.Semantics.DateAggregate

/-! # Compositional temporal values

Atoms retain their caller's typed source. Extrema reuse the classified temporal fold, including
missing provenance and unavailable operands; a consumer supplies its calendar or instant domain.
-/

namespace A12Kernel

/-- Nonempty ordered application models generated argument evaluation for constructors,
selectors and shifts alike. Operator arity and source types are checked by elaboration. -/
inductive TemporalExpressionOf (Atom : Type) (Operation : Type := Empty) where
  | atom (source : Atom)
  | apply (operation : Operation) (first : TemporalExpressionOf Atom Operation)
      (rest : List (TemporalExpressionOf Atom Operation))

namespace TemporalExpressionOf

private def format [Repr Atom] [Repr Operation] :
    TemporalExpressionOf Atom Operation → Std.Format
  | .atom source => "atom (" ++ repr source ++ ")"
  | .apply operation first rest =>
      "apply (" ++ repr operation ++ ") (" ++ format first ++ ") [" ++
        Std.Format.joinSep (rest.map format) ", " ++ "]"

instance [Repr Atom] [Repr Operation] : Repr (TemporalExpressionOf Atom Operation) where
  reprPrec expression _ := format expression

mutual
private def decideEqual [DecidableEq Atom] [DecidableEq Operation]
    (left right : TemporalExpressionOf Atom Operation) : Decidable (left = right) :=
  match left, right with
  | .atom a, .atom b => decidable_of_iff (a = b) (by simp)
  | .atom _, .apply _ _ _ | .apply _ _ _, .atom _ => isFalse (by intro h; cases h)
  | .apply op first rest, .apply other next remaining =>
      letI := decideEqual first next
      letI := decideListEqual rest remaining
      decidable_of_iff (op = other ∧ first = next ∧ rest = remaining) (by simp)
private def decideListEqual [DecidableEq Atom] [DecidableEq Operation]
    (left right : List (TemporalExpressionOf Atom Operation)) : Decidable (left = right) :=
  match left, right with
  | [], [] => isTrue rfl
  | [], _ :: _ | _ :: _, [] => isFalse (by intro h; cases h)
  | first :: rest, next :: remaining =>
      letI := decideEqual first next
      letI := decideListEqual rest remaining
      decidable_of_iff (first = next ∧ rest = remaining) (by simp)
end

instance [DecidableEq Atom] [DecidableEq Operation] : DecidableEq (TemporalExpressionOf Atom Operation) :=
  decideEqual

/-- Authored occurrence order, including repeated occurrences in distinct expressions. -/
def atoms : TemporalExpressionOf Atom Operation → List Atom
  | .atom source => [source]
  | .apply _ first rest => first.atoms ++ rest.flatMap atoms

/-- Additional operator operands, such as a shift amount, follow the temporal arguments. -/
def dependencies (atom : Atom → List Dependency) (operation : Operation → List Dependency) :
    TemporalExpressionOf Atom Operation → List Dependency
  | .atom source => atom source
  | .apply op first rest => first.dependencies atom operation ++
      rest.flatMap (dependencies atom operation) ++ operation op

/-- Ordered application with bounds for recursively embedded numeric operands. The proof arguments
let both expression families share this evaluator without fuel or partial definitions. -/
@[simp]
def evalWithResultSubterm [SizeOf Atom] [SizeOf Operation]
    (expression : TemporalExpressionOf Atom Operation)
    (read : (atom : Atom) → sizeOf atom < sizeOf expression → Except Error Operand)
    (apply : (operation : Operation) → sizeOf operation < sizeOf expression →
      List Operand → Except Error Operand) : Except Error Operand :=
  match expression with
  | .atom source => read source (by simp)
  | .apply operation first rest => do
      let firstValue ← first.evalWithResultSubterm
        (fun atom h => read atom (by simp_all; omega))
        (fun op h => apply op (by simp_all; omega))
      let restValues ← rest.attach.mapM fun ⟨expression, member⟩ =>
        expression.evalWithResultSubterm
          (fun atom h => read atom (by have := List.sizeOf_lt_of_mem member; simp_all; omega))
          (fun op h => apply op (by have := List.sizeOf_lt_of_mem member; simp_all; omega))
      apply operation (by simp; omega) (firstValue :: restValues)

/-- Arguments are reached in authored order before their operator runs. A caller can abort a
reached computation poison through the error channel while retaining cause-free non-relevance as
an operand, so it does not suppress a later argument's failure (stamp-construction grid, 2026-10-04). -/
def evalWithResult (read : Atom → Except Error Operand)
    (apply : Operation → List Operand → Except Error Operand)
    (expression : TemporalExpressionOf Atom Operation) : Except Error Operand :=
  expression.evalWithResultSubterm (fun atom _ => read atom) (fun operation _ => apply operation)

@[simp] theorem evalWithResult_atom (read : Atom → Except Error Operand)
    (apply : Operation → List Operand → Except Error Operand) (source : Atom) :
    (TemporalExpressionOf.atom source).evalWithResult read apply = read source := by
  simp [evalWithResult]

@[simp] theorem evalWithResult_apply (read : Atom → Except Error Operand)
    (apply : Operation → List Operand → Except Error Operand) (operation : Operation)
    (first : TemporalExpressionOf Atom Operation) (rest : List (TemporalExpressionOf Atom Operation)) :
    (TemporalExpressionOf.apply operation first rest).evalWithResult read apply = (do
      let first ← first.evalWithResult read apply
      let rest ← rest.mapM (evalWithResult read apply)
      apply operation (first :: rest)) := by
  simp [evalWithResult, evalWithResultSubterm]
  rfl

end TemporalExpressionOf

end A12Kernel
