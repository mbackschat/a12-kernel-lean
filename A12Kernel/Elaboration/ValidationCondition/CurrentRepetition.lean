import A12Kernel.Semantics.NumericComparison

/-! # Closed CurrentRepetition comparison domains -/

namespace A12Kernel

/-- The only two comparisons established for `CurrentRepetition` over a nonrepeatable root. The compared literal is structurally fixed to one. -/
inductive RootCurrentRepetitionComparison where
  | equalOne
  | notEqualOne
  deriving Repr, DecidableEq

def RootCurrentRepetitionComparison.numericOperator :
    RootCurrentRepetitionComparison → NumericComparisonOp
  | .equalOne => .equal
  | .notEqualOne => .notEqual

/-- Evaluate the closed comparison through the shared numeric comparison owner. Both operands are structural fixed values, so a firing is VALUE. -/
def RootCurrentRepetitionComparison.eval
    (comparison : RootCurrentRepetitionComparison) : Verdict :=
  comparison.numericOperator.evalFixedRight (.value 1 .fixed) 1

/-- The three same-group repeatable comparisons retained by the maintained row-index matrix. Each tag fixes both operator and bound, so checked clients cannot widen the measured surface through a generic numeric expression. -/
inductive RepeatableCurrentRepetitionComparison where
  | greaterThanOne
  | greaterThanTwo
  | greaterEqualOne
  deriving Repr, DecidableEq

def RepeatableCurrentRepetitionComparison.numericOperator :
    RepeatableCurrentRepetitionComparison → NumericComparisonOp
  | .greaterThanOne | .greaterThanTwo => .greater
  | .greaterEqualOne => .greaterEqual

def RepeatableCurrentRepetitionComparison.bound :
    RepeatableCurrentRepetitionComparison → Rat
  | .greaterThanOne | .greaterEqualOne => 1
  | .greaterThanTwo => 2

/-- Compare one checked positive row coordinate through the shared fixed numeric owner. -/
def RepeatableCurrentRepetitionComparison.eval
    (comparison : RepeatableCurrentRepetitionComparison)
    (coordinate : Nat) : Verdict :=
  comparison.numericOperator.evalFixedRight
    (.value coordinate .fixed) comparison.bound

end A12Kernel
