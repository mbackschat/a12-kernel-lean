import A12Kernel.Conformance.NumericComputation.Support

/-! # Numeric-computation evaluation order locks -/

namespace A12Kernel.Conformance.NumericComputation.EvaluationOrder

open A12Kernel
open A12Kernel.Conformance.NumericComputation.Support

/- The computation consumer uses the established one-pass lowering rather than folding the authored tree directly. -/
example : resultOf
    (binary .multiply (literal 3)
      (.group (divide (literal 1) (literal 3)))) =
      some (.value 1) := by
  native_decide

/- Arithmetic domain failure survives as its own expression outcome. -/
example : resultOf (divide (literal 1) (literal 0)) = some .domainFailure := by
  native_decide

/- Rounding does not turn a failed arithmetic child into a numeric value. -/
example : resultOf (rounded (divide (literal 1) (literal 0))) =
    some .domainFailure := by
  native_decide

/- Rounding preserves a reached computation poison instead of manufacturing a numeric result. -/
example : resultOf (rounded (field source))
    (context (checkedNumber (.rejected .malformed))) =
      some (.poison .malformed) := by
  rfl

/- Absolute value shares the numeric tree but preserves computation-domain failure and poison. -/
example : resultOf (absolute (field source))
    (context (checkedNumber (.parsed (.num (-5))))) = some (.value 5) := by
  native_decide

example : resultOf (absolute (divide (literal 1) (literal 0))) =
    some .domainFailure := by
  native_decide

example : resultOf (absolute (field source))
    (context (checkedNumber (.rejected .malformed))) =
      some (.poison .malformed) := by
  rfl

/- Numeric operand-list extrema keep empty Number as a competing zero. -/
example : resultOf (AuthoredNumericExpr.extremumList .minimum (field source) [literal 4]) =
    some (.value 0) := by
  native_decide

example : resultOf (AuthoredNumericExpr.extremumList .maximum (field source) [literal (-4)]) =
    some (.value 0) := by
  native_decide

/- A domain failure remains value-level and therefore does not hide a later reached poison. -/
example : resultOf
    (AuthoredNumericExpr.extremumList .maximum
      (divide (literal 1) (literal 0)) [literal 3]) =
      some .domainFailure := by
  native_decide

example : resultOf
    (AuthoredNumericExpr.extremumList .minimum
      (divide (literal 1) (literal 0)) [literal 3, field later])
    (context (checkedNumber .empty)
      (checkedNumber (.rejected .declaredConstraint))) =
      some (.poison .declaredConstraint) := by
  native_decide

/- The first poison aborts the remaining ordered operand stream. -/
example : resultOf
    (AuthoredNumericExpr.extremumList .maximum (field source) [field later])
    (context
      (checkedNumber (.rejected .malformed))
      (checkedNumber (.rejected .declaredConstraint))) =
      some (.poison .malformed) := by
  native_decide

/- Structural preflight traverses the complete list before a reached poison could hide a wrong-kind tail. -/
example : faultOf
    (AuthoredNumericExpr.extremumList .minimum (field source)
      [literal 3, field (stringDeclaration laterId "WrongLater")])
    (context (checkedNumber (.rejected .malformed))) =
      some (.fieldKindMismatch laterId) := by
  native_decide

example : resultOf
    (binary .add (divide (literal 1) (literal 0)) (literal 2)) =
      some .domainFailure := by
  native_decide

example : resultOf
    (binary .add (literal 2) (divide (literal 1) (literal 0))) =
      some .domainFailure := by
  native_decide

/- A formally invalid field actually read by the expression remains poison. -/
example : resultOf (field source)
    (context (checkedNumber (.rejected .malformed))) =
      some (.poison .malformed) := by
  rfl

/- The source-generated arithmetic chain still evaluates its right operand after a domain-invalid receiver; a reached invalid field therefore remains poison. Portable mixed-precedence evidence remains pending. -/
example : resultOf
    (binary .add
      (divide (literal 1) (literal 0))
      (field later))
    (context (checkedNumber .empty)
      (checkedNumber (.rejected .declaredConstraint))) =
      some (.poison .declaredConstraint) := by
  rfl

/- A left poison aborts before a differently poisoned right operand can replace its cause. -/
example : resultOf
    (binary .add
      (field source)
      (field later))
    (context
      (checkedNumber (.rejected .malformed))
      (checkedNumber (.rejected .declaredConstraint))) =
      some (.poison .malformed) := by
  rfl

/- Poison order follows the one-pass lowered tree: `(Source / 2) * Later` becomes `(Later * Source) / 2`, so Later is read first. -/
example : resultOf
    (binary .multiply
      (divide (field source) (literal 2))
      (field later))
    (context
      (checkedNumber (.rejected .malformed))
      (checkedNumber (.rejected .declaredConstraint))) =
      some (.poison .declaredConstraint) := by
  rfl

/- A non-Number declaration is a structural fault even when its cell is empty. -/
example : faultOf (field (stringDeclaration sourceId "WrongSource")) =
      some (.fieldKindMismatch sourceId) := by
  native_decide

/- Complete structural checking prevents a left poison from hiding a wrong-kind right declaration. -/
example : faultOf
    (binary .add
      (field source)
      (field (stringDeclaration laterId "WrongLater")))
    (context (checkedNumber (.rejected .malformed))) =
      some (.fieldKindMismatch laterId) := by
  native_decide

/- Power shares the checked computation result boundary: valid values remain values. -/
example : resultOf (power (literal 2) (literal 3)) =
    some (.value 8) := by
  native_decide

/- Both runtime-invalid integral power regions become arithmetic domain failure. -/
example : resultOf (power (literal 0) (literal (-1))) =
    some .domainFailure := by
  native_decide

example : resultOf (power (literal 2) (literal 1001)) =
    some .domainFailure := by
  native_decide

/- Structural preflight still traverses power before a reached poison can hide a wrong-kind exponent. -/
example : faultOf
    (binary .add (field source)
      (power (literal 2) (field (stringDeclaration laterId "WrongLater"))))
    (context (checkedNumber (.rejected .malformed))) =
      some (.fieldKindMismatch laterId) := by
  native_decide


end A12Kernel.Conformance.NumericComputation.EvaluationOrder
