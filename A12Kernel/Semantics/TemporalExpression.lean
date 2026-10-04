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

/-- Arguments are reached in authored order before their operator runs. A caller can abort a
reached computation poison through the error channel while retaining cause-free non-relevance as
an operand, so it does not suppress a later argument's failure (stamp-construction grid, 2026-10-04). -/
def evalWithResult (read : Atom → Except Error Operand)
    (apply : Operation → List Operand → Except Error Operand) :
    TemporalExpressionOf Atom Operation → Except Error Operand
  | .atom source => read source
  | .apply operation first rest => do
      let first ← first.evalWithResult read apply
      let rest ← rest.mapM (evalWithResult read apply)
      apply operation (first :: rest)

end TemporalExpressionOf

end A12Kernel
