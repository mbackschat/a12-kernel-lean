import A12Kernel.Elaboration.ArithmeticShape

/-! # Laws of the arithmetic shape gates

The gate a consumer most easily gets wrong is the division limit, because the natural reading — count
the divisions — is refuted by the Kernel's own compatibility behaviour. The laws below say what the
count actually ranges over.

`divisionScan_boundary_contributes_nothing` is the scoping statement: every boundary constructor reports
zero open divisions upward, whatever it contains. `grouped_division_admitted` turns that into the
compatibility quirk itself, and `divisions_across_addition_admitted` into the additive case.

`powerRefusal_grouped_left_admits` records that grouping the left operand defeats the power gate, so
the class cannot be read as forbidding nesting. Both power laws carry the hypothesis that the base is not
*itself* directly a power — dropped from a first draft, where it made them false, since a base that is a
clean power still trips the gate one level up.
-/

namespace A12Kernel

/-- **The scoping law.** Each boundary constructor contributes no open divisions to its enclosing
region, so a region's count never crosses one of them. -/
theorem divisionScan_boundary_contributes_nothing (left right inner : CalcExpr) :
    (divisionScan (.addSub left right)).1 = 0 ∧
      (divisionScan (.grouped inner)).1 = 0 ∧
      (divisionScan (.power left right)).1 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [divisionScan]

/-- **The compatibility quirk, as a law.** One division whose divisor is a grouped division is admitted,
where the same two divisions ungrouped are refused. The Kernel keeps this deliberately, so a consumer
counting divisions globally is stricter than the Kernel. -/
theorem grouped_division_admitted (leaf : CalcExpr) (h : divisionScan leaf = (0, false)) :
    divisionRefusal (.divide leaf (.grouped (.divide leaf leaf))) = none ∧
      divisionRefusal (.divide (.divide leaf leaf) leaf) =
        some .tooManyDivisionsInRegion := by
  constructor <;> simp [divisionRefusal, divisionScan, h]

/-- One division on each side of an addition is admitted, for the same scoping reason. -/
theorem divisions_across_addition_admitted (leaf : CalcExpr)
    (h : divisionScan leaf = (0, false)) :
    divisionRefusal (.addSub (.divide leaf leaf) (.divide leaf leaf)) = none := by
  simp [divisionRefusal, divisionScan, h]

/-- Multiplication does **not** open a fresh region: it combines its children's open divisions, so a
division on each side of a product is refused. This is the boundary law's exact complement. -/
theorem multiplication_combines_regions (leaf : CalcExpr) (h : divisionScan leaf = (0, false)) :
    divisionRefusal (.multiply (.divide leaf leaf) (.divide leaf leaf)) =
      some .tooManyDivisionsInRegion := by
  simp [divisionRefusal, divisionScan, h]

/-- **Grouping the left operand defeats the power gate**, so the class is about the ungrouped chain and
not about nesting. -/
theorem powerRefusal_grouped_left_admits (base exponent : CalcExpr)
    (hBase : powerRefusal base = none) (hExponent : powerRefusal exponent = none)
    (hNotPower : base.isDirectPower = false) :
    powerRefusal (.power (.grouped (.power base exponent)) exponent) = none ∧
      powerRefusal (.power (.power base exponent) exponent) = some .nestedPowerOnLeft := by
  refine ⟨?_, by simp [powerRefusal]⟩
  cases base <;> simp_all [powerRefusal, CalcExpr.isDirectPower]

/-- A power on the right is admitted, which separates the gate from a symmetric nesting rule. -/
theorem powerRefusal_right_nesting_admits (base exponent : CalcExpr)
    (hBase : powerRefusal base = none) (hExponent : powerRefusal exponent = none)
    (hNotPower : base.isDirectPower = false) :
    powerRefusal (.power base (.power base exponent)) = none := by
  cases base <;> simp_all [powerRefusal, CalcExpr.isDirectPower]

/-- The exponent gate admits exactly the known whole scale, so an unknown scale is refused on the same
footing as a positive one rather than deferred. -/
theorem exponentRefusal_admits_only_zero (scale : Option Nat) :
    exponentRefusal scale = none ↔ scale = some 0 := by
  cases scale with
  | none => simp [exponentRefusal]
  | some value => cases value <;> simp [exponentRefusal]

/-- The constant limit depends on how many constants a list holds and not on its length. -/
theorem constantListRefusal_counts_constants (operands : List Bool) :
    constantListRefusal operands = some .tooManyConstantsInOperandList ↔
      2 ≤ (operands.filter id).length := by
  simp [constantListRefusal]

end A12Kernel
