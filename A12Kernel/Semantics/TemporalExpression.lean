import A12Kernel.Semantics.DateAggregate

/-! # Compositional temporal values

Atoms retain their caller's typed source. Extrema reuse the classified temporal fold, including
missing provenance and unavailable operands; a consumer supplies its calendar or instant domain.
-/

namespace A12Kernel

inductive TemporalExpressionOf (Atom : Type) where
  | atom (source : Atom)
  | extremum (operator : TemporalExtremumOp)
      (first : TemporalExpressionOf Atom) (rest : List (TemporalExpressionOf Atom))

namespace TemporalExpressionOf

/-- Authored occurrence order, including repeated occurrences in distinct expressions. -/
def atoms : TemporalExpressionOf Atom → List Atom
  | .atom source => [source]
  | .extremum _ first rest => first.atoms ++ rest.flatMap atoms

/-- Resolve atoms once per occurrence and preserve the fold's unavailable and missing states. -/
def evalWith (select : TemporalExtremumOp → α → α → α)
    (read : Atom → SimpleComparisonOperand α) :
    TemporalExpressionOf Atom → SimpleComparisonOperand α
  | .atom source => read source
  | .extremum operator first rest =>
      evalTemporalExtremumAggregate (select operator)
        { operands := first.evalWith select read :: rest.map (evalWith select read)
          hasUninstantiatedTail := false, hasHaving := false }

end TemporalExpressionOf

end A12Kernel
