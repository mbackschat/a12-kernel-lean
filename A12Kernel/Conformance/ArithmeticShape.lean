import A12Kernel.Elaboration.ArithmeticShape

/-! # Locks on the arithmetic shape gates

Every case below replays a measured row ([checkpoint](../../docs/SOURCES.md#src-arithmetic-shape-gates));
each refusing row was taken beside an admitted control on the same model, so no class is attributed to
the route or the fixture.

The matrix separates the division region's four boundaries from each other and from the multiplicative
chain that combines, the power gate's left-only reading against its grouped twin, the exponent gate
across literal, declared, unknown and compound scales, and the constant limit at two list lengths.
-/

namespace A12Kernel.Conformance.ArithmeticShape

open A12Kernel

private def key? (expression : CalcExpr) : Option String :=
  (divisionRefusal expression).map KernelStaticDiagnostic.kernelCode

private def powKey? (expression : CalcExpr) : Option String :=
  (powerRefusal expression).map KernelStaticDiagnostic.kernelCode

private def expKey? (scale : Option Nat) : Option String :=
  (exponentRefusal scale).map KernelStaticDiagnostic.kernelCode

private def constKey? (operands : List Bool) : Option String :=
  (constantListRefusal operands).map KernelStaticDiagnostic.kernelCode

private def a : CalcExpr := .operand

/- **Two divisions in one region refuse; one is admitted.** Replays the measured chain and its control. -/
example :
    key? (.divide (.divide a a) a) = some "MVK_TOO_MANY_DIV_FOR_CALC" ∧
      key? (.divide a a) = none := by
  native_decide

/- **Multiplication combines, so a division on each side of a product still refuses.** The measured
   `a / b * c / d` row, which is what stops the region being read as "one operator deep". -/
example :
    key? (.divide (.multiply (.divide a a) a) a) = some "MVK_TOO_MANY_DIV_FOR_CALC" := by
  native_decide

/- **Addition and subtraction each start a fresh region**, so one division on either side is admitted —
   both measured, and both would refuse under a global count. -/
example :
    key? (.addSub (.divide a a) (.divide a a)) = none ∧
      key? (.addSub (.divide (.divide a a) a) a) = some "MVK_TOO_MANY_DIV_FOR_CALC" := by
  native_decide

/- **Grouping starts a fresh region too, which is the old-parser compatibility quirk.** `a / {b / c}` is
   **admitted** on the real Kernel while the ungrouped `a / b / c` above is refused, and two grouped
   divisions multiplied together are admitted as well. The second row is the one that keeps the first
   from reading as an accident of depth. -/
example :
    key? (.divide a (.grouped (.divide a a))) = none ∧
      key? (.multiply (.grouped (.divide a a)) (.grouped (.divide a a))) = none := by
  native_decide

/- **A region closed inside a group is still checked**, so grouping resets the count without hiding a
   violation already inside it. -/
example :
    key? (.grouped (.divide (.divide a a) a)) = some "MVK_TOO_MANY_DIV_FOR_CALC" ∧
      key? (.multiply a (.grouped (.divide (.divide a a) a))) =
        some "MVK_TOO_MANY_DIV_FOR_CALC" := by
  native_decide

/- **A power boundary closes the region on both sides.** -/
example :
    key? (.power (.divide a a) (.divide a a)) = none ∧
      key? (.power (.divide (.divide a a) a) a) = some "MVK_TOO_MANY_DIV_FOR_CALC" := by
  native_decide

/- **The power gate reads the left operand only, and grouping it defeats the gate.** Both measured: the
   ungrouped chain refuses, the left-grouped form is admitted, and a power on the *right* is admitted —
   so the class is not about nesting as such. -/
example :
    powKey? (.power (.power a a) a) = some "MVK_TOO_MANY_POW_FOR_CALC" ∧
      powKey? (.power (.grouped (.power a a)) a) = none ∧
      powKey? (.power a (.power a a)) = none ∧
      powKey? (.power a a) = none := by
  native_decide

/- **The gate still finds a nested power buried in a larger expression**, so it is a traversal rather
   than a check on the outermost node. -/
example :
    powKey? (.addSub a (.multiply a (.power (.power a a) a))) =
      some "MVK_TOO_MANY_POW_FOR_CALC" := by
  native_decide

/- **The exponent gate admits a whole scale and refuses both a positive and an unknown one.** The three
   measured shapes: an integer literal, a field declared with fractional digits, and a division. -/
example :
    expKey? (some 0) = none ∧
      expKey? (some 2) = some "MVK_INVALID_NUMBER_FOR_EXP" ∧
      expKey? none = some "MVK_INVALID_NUMBER_FOR_EXP" ∧
      expKey? (some 1) = some "MVK_INVALID_NUMBER_FOR_EXP" := by
  native_decide

/- **The constant limit counts the whole list, at two lengths.** A two-operand list of constants refuses,
   one constant beside a field is admitted, and a three-operand list flips on its second constant — the
   rows that keep the rule from being read as a property of list length. -/
example :
    constKey? [true, true] = some "MVK_TOO_MANY_CONST_FOR_CALC_OP" ∧
      constKey? [false, true] = none ∧
      constKey? [false, false] = none ∧
      constKey? [false, false, true] = none ∧
      constKey? [false, true, true] = some "MVK_TOO_MANY_CONST_FOR_CALC_OP" := by
  native_decide

end A12Kernel.Conformance.ArithmeticShape
