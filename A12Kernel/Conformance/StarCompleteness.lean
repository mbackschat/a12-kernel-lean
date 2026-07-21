import A12Kernel.Semantics.StarCompleteness
import A12Kernel.Semantics.NumericAggregate

/-! # Reopened-star completeness executable locks

These cases start after the first-star binding decision. They distinguish hierarchical
per-parent completeness from a shallow or flattened row count and lock the bridge into
resolved aggregate missingness without adding path parsing or Cartesian enumeration.
-/

namespace A12Kernel.Conformance.StarCompleteness

open A12Kernel

private def leaf : ReopenedStarDomain := .selectedLeaf

private def one (child : ReopenedStarDomain) : ReopenedStarRows :=
  .cons 1 child .nil

private def two (first second : ReopenedStarDomain) : ReopenedStarRows :=
  .cons 1 first (.cons 2 second .nil)

private def finiteTwo (rows : ReopenedStarRows) : ReopenedStarDomain :=
  .repeatable (some 2) rows

private def fullC : ReopenedStarDomain := finiteTwo (two leaf leaf)
private def fullB : ReopenedStarDomain := finiteTwo (two fullC fullC)
private def fullA : ReopenedStarDomain := finiteTwo (two fullB fullB)

/- Checked lowering supplies one positive, unique coordinate per actual sibling row. -/
example : fullA.wellFormed = true := by native_decide
example :
    (finiteTwo (.cons 1 leaf (.cons 1 leaf .nil))).wellFormed = false ∧
      (finiteTwo (.cons 0 leaf .nil)).wellFormed = false := by
  native_decide

/- Missing capacity at the first reopened level remains open. -/
example : (finiteTwo (one fullB)).hasOpenTail = true := by native_decide

/- One dense branch cannot hide missing middle capacity under another actual parent. -/
example :
    (finiteTwo (two fullB (finiteTwo (one fullC)))).hasOpenTail = true := by
  native_decide

/- Complete outer and middle levels cannot hide a missing deepest repetition. -/
example :
    (finiteTwo (two fullB (finiteTwo (two fullC (finiteTwo (one leaf)))))).hasOpenTail =
      true := by
  native_decide

/- Exhausting every finite reopened level closes the structural tail. -/
example : fullA.hasOpenTail = false := by native_decide

/- A level above the first star is absent from the reopened tree; a complete B/C subtree
   is fixed regardless of unused A capacity outside the bound row. -/
example : fullB.hasOpenTail = false := by native_decide

/- Any unbounded reopened level stays open after every finite set of actual rows. -/
example : (ReopenedStarDomain.repeatable none (two leaf leaf)).hasOpenTail = true := by
  native_decide

/- Structural completeness and selected-cell emptiness compose at the existing resolved
   operand boundary instead of duplicating leaf state in the repetition tree. -/
example :
    (fullA.toResolvedSide (kind := .number) [.present 8, .empty]).hasMissingPotential =
      true ∧
    (fullA.toResolvedSide (kind := .number) [.present 8]).hasMissingPotential = false := by
  native_decide

/- The derived tail bit is consumed unchanged by the existing aggregate direction. -/
example :
    evalNumericSumAggregate false
        ((finiteTwo (one fullB)).toResolvedSide (kind := .number) [.present 8]) =
      .value (NumericArithmeticOp.add.eval 0 8) .growOnly ∧
    evalNumericSumAggregate false
        (fullA.toResolvedSide (kind := .number) [.present 8]) =
      .value (NumericArithmeticOp.add.eval 0 8) .fixed := by
  native_decide

end A12Kernel.Conformance.StarCompleteness
