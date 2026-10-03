import A12Kernel.Semantics.DateAggregate

/-! # Compositional temporal values

Atoms retain their caller's typed source. Extrema reuse the classified temporal fold, including
missing provenance and unavailable operands; a consumer supplies its calendar or instant domain.
-/

namespace A12Kernel

inductive TemporalExpressionOf (Atom : Type) (Transform : Type := Empty) where
  | atom (source : Atom)
  | extremum (operator : TemporalExtremumOp)
      (first : TemporalExpressionOf Atom Transform) (rest : List (TemporalExpressionOf Atom Transform))
  | transform (operation : Transform) (source : TemporalExpressionOf Atom Transform)

namespace TemporalExpressionOf

/-- Authored occurrence order, including repeated occurrences in distinct expressions. -/
def atoms : TemporalExpressionOf Atom Transform → List Atom
  | .atom source => [source]
  | .extremum _ first rest => first.atoms ++ rest.flatMap atoms
  | .transform _ source => source.atoms

/-- A transform's additional operands are reached after its source, in authored order. -/
def dependencies (atom : Atom → List Dependency) (transform : Transform → List Dependency) :
    TemporalExpressionOf Atom Transform → List Dependency
  | .atom source => atom source
  | .extremum _ first rest => first.dependencies atom transform ++
      rest.flatMap (dependencies atom transform)
  | .transform operation source => source.dependencies atom transform ++ transform operation

/-- Operand expressions are evaluated before the classified extrema fold. A runtime failure is
distinct from a successfully evaluated unknown operand; generated Java/Groovy operation-list calls
evaluate their arguments before entering the selector. -/
def evalWithResult (select : TemporalExtremumOp → α → α → α)
    (read : Atom → Except Error (SimpleComparisonOperand α))
    (apply : Transform → SimpleComparisonOperand α → Except Error (SimpleComparisonOperand α)) :
    TemporalExpressionOf Atom Transform → Except Error (SimpleComparisonOperand α)
  | .atom source => read source
  | .extremum operator first rest => do
      let first ← first.evalWithResult select read apply
      let rest ← rest.mapM (evalWithResult select read apply)
      pure (evalTemporalExtremumAggregate (select operator)
        { operands := first :: rest
          hasUninstantiatedTail := false, hasHaving := false })
  | .transform operation source => do
      apply operation (← source.evalWithResult select read apply)

end TemporalExpressionOf

end A12Kernel
