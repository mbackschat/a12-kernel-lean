import A12Kernel.Elaboration.NumericExpression
import A12Kernel.Semantics.NumericComparison

/-! # Numeric-expression lowering separating cases -/

namespace A12Kernel.Conformance.NumericExpression

open A12Kernel

private abbrev Expr := AuthoredNumericExpr Nat
private abbrev Lowered := LoweredNumericExpr Nat

private def literal (value : Rat) (authoredScale : Int) : Expr :=
  .literal { value, authoredScale }

private def noAtoms (_ : Nat) : NumericScaleSummary :=
  NumericScaleSummary.field 0

private def oneThird : Expr :=
  .group (.binary .divide (literal 1 0) (literal 3 0))

private def fourFifths : Expr :=
  .group (.binary .divide (literal 4 0) (literal 5 0))

/- Equal numeric values retain distinct authored scales. -/
example : (literal 0 0).summary? noAtoms =
    some { scale := .exact 0, canExpandScale := true } := by
  native_decide

example : (literal 0 2).summary? noAtoms =
    some { scale := .exact 2, canExpandScale := true } := by
  native_decide

/- Grouping is summary-transparent but blocks the narrow simple-constant power case. -/
example : (.power (literal 2 0) (literal 2 0) : Expr).summary? noAtoms =
    some { scale := .exact 0, canExpandScale := false } := by
  native_decide

example : (.power (literal 2 0) (.group (literal 2 0)) : Expr).summary? noAtoms =
    some { scale := .unknown, canExpandScale := false } := by
  native_decide

private def threeTimesOneThird : Expr :=
  .binary .multiply (literal 3 0) oneThird

private def normalizedThreeTimesOneThird : Lowered :=
  .binary .divide
    (.binary .multiply (.literal 3) (.literal 1))
    (.literal 3)

/- Grouping does not block the later bottom-up division rewrite. -/
example : threeTimesOneThird.lowerForEvaluation = normalizedThreeTimesOneThird := by
  native_decide

/- A leading divided factor puts the non-divided factor first in the new numerator. -/
example : (.binary .multiply oneThird (literal 3 0) : Expr).lowerForEvaluation =
    normalizedThreeTimesOneThird := by
  native_decide

/- Two immediate divided factors become one quotient of numerator and denominator products. -/
example : (.binary .multiply oneThird fourFifths : Expr).lowerForEvaluation =
    .binary .divide
      (.binary .multiply (.literal 1) (.literal 4))
      (.binary .multiply (.literal 3) (.literal 5)) := by
  native_decide

/- A later ordinary factor precedes the numerator synthesized by the child pass. -/
example : (.binary .multiply threeTimesOneThird (literal 5 0) : Expr).lowerForEvaluation =
    .binary .divide
      (.binary .multiply (.literal 5)
        (.binary .multiply (.literal 3) (.literal 1)))
      (.literal 3) := by
  native_decide

/- The pass does not revisit a newly constructed product containing an extracted nested division. -/
example : (.binary .multiply (literal 2 0)
    (.group (.binary .divide oneThird (literal 5 0))) : Expr).lowerForEvaluation =
      .binary .divide
        (.binary .multiply (.literal 2)
          (.binary .divide (.literal 1) (.literal 3)))
        (.literal 5) := by
  native_decide

/- Addition, rounding, and power remain transformation boundaries. -/
example : (.binary .multiply (literal 3 0)
    (.binary .add oneThird (literal 1 0)) : Expr).lowerForEvaluation =
      .binary .multiply (.literal 3)
        (.binary .add
          (.binary .divide (.literal 1) (.literal 3))
          (.literal 1)) := by
  native_decide

example : (.binary .multiply (literal 3 0)
    (.round .halfUp omittedRoundingPlaces oneThird) : Expr).lowerForEvaluation =
      .binary .multiply (.literal 3)
        (.round .halfUp omittedRoundingPlaces
          (.binary .divide (.literal 1) (.literal 3))) := by
  native_decide

example : (.binary .multiply (literal 3 0)
    (.power oneThird (literal 2 0)) : Expr).lowerForEvaluation =
      .binary .multiply (.literal 3)
        (.power
          (.binary .divide (.literal 1) (.literal 3))
          (.literal 2)) := by
  native_decide

/- Static checking consumes the authored tree: lowering would clear this surviving capability at the new root division. -/
example : threeTimesOneThird.summary? noAtoms =
    some { scale := .unknown, canExpandScale := true } := by
  native_decide

/- Per-node precision makes the normalization part of evaluation semantics, not a value-preserving optimization. -/
example : threeTimesOneThird.evalValue (fun _ => .notEvaluated) = .value 1 := by
  native_decide

private def directAuthoredThreeTimesOneThird : NumericArithmeticResult :=
  match divideNumeric 1 3 with
  | .value quotient => .value (NumericArithmeticOp.multiply.eval 3 quotient)
  | .notEvaluated => .notEvaluated

example : directAuthoredThreeTimesOneThird = .value (1 - 1 / 10 ^ 50) := by
  native_decide

private def precisionAmplifier : Rat := 10 ^ 31

private def amplifiedThreeTimesOneThird : Expr :=
  .binary .multiply threeTimesOneThird
    (literal precisionAmplifier (-31))

example : amplifiedThreeTimesOneThird.evalValue (fun _ => .notEvaluated) =
    .value precisionAmplifier := by
  native_decide

/- The counterfactual authored fold leaves a scale-19-visible gap after amplification. -/
example :
    (match directAuthoredThreeTimesOneThird with
    | .value value =>
        NumericArithmeticResult.value
          (NumericArithmeticOp.multiply.eval value precisionAmplifier)
    | .notEvaluated => NumericArithmeticResult.notEvaluated) =
      NumericArithmeticResult.value
        (precisionAmplifier - 1 / 10 ^ 19) := by
  native_decide

/- The amplified gap survives the actual scale-19 comparison boundary. -/
example : NumericComparisonOp.notEqual.holds
    precisionAmplifier (precisionAmplifier - 1 / 10 ^ 19) = true := by
  native_decide

example : (.binary .multiply (literal 2 0)
    (.group (.binary .divide (literal 1 0) (literal 0 0))) : Expr).evalValue
      (fun _ => .notEvaluated) = .notEvaluated := by
  native_decide

/- Absolute value is a numeric-tree operation: it transforms only available values and preserves the child's static summary. -/
example : (.abs (literal (-5) 0) : Expr).evalValue (fun _ => .notEvaluated) =
    .value 5 := by
  native_decide

example : (.abs (.atom 0) : Expr).summary? (fun _ =>
    { scale := .exact 2, canExpandScale := false }) =
      some { scale := .exact 2, canExpandScale := false } := by
  native_decide

private def belowComparisonResolution : Rat := 1 / 10 ^ 20

/- Operand-list Min/Max select at full precision rather than at the later scale-19 comparison boundary. -/
example : (.extremum .minimum (literal belowComparisonResolution 20) (.atom 0) : Expr).evalValue
    (fun _ => .value 0) = .value 0 := by
  native_decide

example : (.extremum .maximum (literal belowComparisonResolution 20) (.atom 0) : Expr).evalValue
    (fun _ => .value 0) = .value belowComparisonResolution := by
  native_decide

/- The operand-list result uses the largest derived scale and retains constant expandability only when every operand has it. -/
example : (.extremum .minimum (.atom 0) (literal 0 2) : Expr).summary? (fun _ =>
    { scale := .exact 0, canExpandScale := false }) =
      some { scale := .exact 2, canExpandScale := false } := by
  native_decide

private def source (id : Nat) : Expr := .atom id

private def quotient (left right : Expr) : Expr :=
  .binary .divide left right

/- One division is legal, while a second division in the same multiplicative region is not. -/
example : (quotient (source 0) (source 1)).authoringCheck = .accepted := by
  native_decide

example : (quotient (quotient (source 0) (source 1)) (source 2)).authoringCheck =
    .tooManyDivisions := by
  native_decide

example : (.binary .multiply
    (quotient (source 0) (source 1))
    (quotient (source 2) (source 3)) : Expr).authoringCheck =
      .tooManyDivisions := by
  native_decide

/- Addition and explicit grouping validate fresh regions and expose no division upward. -/
example : (.binary .add
    (quotient (source 0) (source 1))
    (quotient (source 2) (source 3)) : Expr).authoringCheck = .accepted := by
  native_decide

example : (quotient
    (.group (quotient (source 0) (source 1)))
    (source 2) : Expr).authoringCheck = .accepted := by
  native_decide

example : (quotient
    (source 0)
    (.group (quotient (source 1) (source 2))) : Expr).authoringCheck = .accepted := by
  native_decide

/- A boundary resets only outward contribution; it does not erase an illegal inner region. -/
example : (.group
    (quotient (quotient (source 0) (source 1)) (source 2)) : Expr).authoringCheck =
      .tooManyDivisions := by
  native_decide

example : (.power
    (quotient (source 0) (source 1))
    (quotient (source 2) (source 3)) : Expr).authoringCheck = .accepted := by
  native_decide

/- Only an ungrouped power in the direct left operand is the kernel's nested-power error. -/
example : (.power
    (.power (source 0) (source 1))
    (source 2) : Expr).authoringCheck =
      .directLeftNestedPower := by
  native_decide

example : (.power
    (.group (.power (source 0) (source 1)))
    (source 2) : Expr).authoringCheck = .accepted := by
  native_decide

example : (.power
    (source 0)
    (.group (.power (source 1) (source 2))) : Expr).authoringCheck = .accepted := by
  native_decide

/- This right-nested ungrouped tree is parser-unreachable; its acceptance keeps grammar shape a separate precondition. -/
example : (.power
    (source 0)
    (.power (source 1) (source 2)) : Expr).authoringCheck = .accepted := by
  native_decide

/- Independent violations are retained without inventing a first-diagnostic order. -/
example : (.binary .add
    (quotient (quotient (source 0) (source 1)) (source 2))
    (.power (.power (source 3) (source 4)) (source 5)) :
      Expr).authoringCheck = .tooManyDivisionsAndDirectLeftNestedPower := by
  native_decide

/- Operation-valued wrappers stay outside the plain compositional checker. The operation-level checker delegates a root wrapper to its complete body and separately walks an admitted wrapper inside enclosing arithmetic. -/
example : (.round .halfUp omittedRoundingPlaces
    (quotient (source 0) (source 1)) : Expr).authoringCheck = .outsideFragment := by
  native_decide

example : (.round .halfUp omittedRoundingPlaces
    (quotient (source 0) (source 1)) : Expr).numericOperationAuthoringCheck =
      .accepted := by
  native_decide

example : (.abs (quotient (source 0) (source 1)) : Expr).authoringCheck =
    .outsideFragment := by
  native_decide

example : (.abs
    (quotient (quotient (source 0) (source 1)) (source 2)) : Expr).numericOperationAuthoringCheck =
      .tooManyDivisions := by
  native_decide

/- Enclosing arithmetic sees through a unary wrapper for division-region checking. The wrapped addition retains its ordinary region reset. -/
example : (.binary .divide
    (.binary .multiply
      (.round .halfUp omittedRoundingPlaces
        (quotient (source 0) (source 1)))
      (source 2))
    (source 3) : Expr).numericOperationAuthoringCheck =
      .tooManyDivisions := by
  native_decide

example : (.binary .divide
    (.binary .multiply
      (.round .halfUp omittedRoundingPlaces
        (.binary .add (source 0) (source 1)))
      (source 2))
    (source 3) : Expr).numericOperationAuthoringCheck = .accepted := by
  native_decide

/- A wrapper separates powers structurally but does not hide an illegal power inside its own body. -/
example : (.power
    (.round .halfUp omittedRoundingPlaces
      (.power (source 0) (source 1)))
    (source 2) : Expr).numericOperationAuthoringCheck = .accepted := by
  native_decide

example : (.binary .add
    (.abs (.power (.power (source 0) (source 1)) (source 2)))
    (source 3) : Expr).numericOperationAuthoringCheck =
      .directLeftNestedPower := by
  native_decide

/- Nested unary wrappers and a direct operand-list extremum are ordinary nonliteral wrapper children. Their inner authoring failures remain visible. -/
example : (.round .floor omittedRoundingPlaces
    (.abs (source 0)) : Expr).numericOperationAuthoringCheck = .accepted := by
  native_decide

example : (.abs
    (.extremum .minimum (source 0) (source 1)) : Expr).numericOperationAuthoringCheck =
      .accepted := by
  native_decide

example : (.binary .divide
    (.round .halfUp omittedRoundingPlaces
      (.abs (quotient (source 0) (source 1))))
    (source 2) : Expr).numericOperationAuthoringCheck = .tooManyDivisions := by
  native_decide

example : (.extremum .minimum (source 0) (source 1) : Expr).authoringCheck =
    .outsideFragment := by
  native_decide

end A12Kernel.Conformance.NumericExpression
