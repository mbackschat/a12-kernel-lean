import A12Kernel.Elaboration.NumericComputation
import A12Kernel.Semantics.NumericApplication
import A12Kernel.Semantics.NumericDependency

/-! # Numeric dependency-observation locks -/

namespace A12Kernel.Conformance.NumericDependency

open A12Kernel

private def old : StoredNumber := { unscaled := 7, scale := 0 }
private def padded : StoredNumber := { unscaled := 700, scale := 2 }
private def overlong : StoredNumber :=
  { unscaled := 1234567890123456, scale := 0 }

private def scaleTwo : NumericTargetPolicy where
  info := { scale := 2, signed := true }
  minFractionalDigits := 2
  minLeMax := by decide

private def source : FlatFieldDecl where
  id := 1
  groupPath := ["Root"]
  name := "Source"
  policy := { kind := .number { scale := 2, signed := true } }

private def context : ScalarComputationContext where
  read _ := formalCheck source.policy (.parsed (.num 1))

private def literal (amount : Rat) : AuthoredNumericExpr FlatFieldDecl :=
  .literal { value := amount, authoredScale := 0 }

private def roundedDivisionByZero : AuthoredNumericExpr FlatFieldDecl :=
  .round .halfUp ⟨2, by decide⟩
    (.binary .divide (.atom source) (literal 0))

private def dependencyAfter
    (result : Except NumericComputationFault NumericComputationResult) :
    Option NumericDependencyObservation :=
  match result with
  | .error _ => none
  | .ok expressionResult =>
      match scaleTwo.check expressionResult with
      | .unsupported _ => none
      | .supported outcome => some outcome.dependencyObservation

/- Clean no-result becomes an empty dependency, never the stale target value. -/
example : NumericTargetOutcome.noValue.dependencyObservation = .empty := by
  rfl

/- Accepted output preserves the exact stored decimal at the dependency boundary. -/
example :
    (NumericTargetOutcome.accepted padded).dependencyObservation =
      .value padded := by
  rfl

/- Every invalid producer class becomes poisoned; rejected attempts are not readable values. -/
example :
    (NumericTargetOutcome.rejected overlong .totalDigitsTooLong).dependencyObservation =
        .poisoned ∧
      (NumericTargetOutcome.invalidNoValue .calculationValue).dependencyObservation =
        .poisoned ∧
      (NumericTargetOutcome.inheritedPoison .malformed).dependencyObservation =
        .poisoned := by
  decide

/- The source-established legal, already-resolved rounded divide-by-zero route reaches calculation invalidity and therefore a poisoned dependency. Checked target authoring remains outside this capsule. -/
example :
    roundedDivisionByZero.evaluateComputation context = .ok .domainFailure ∧
      scaleTwo.check .domainFailure =
        .supported (.invalidNoValue .calculationValue) ∧
      dependencyAfter (roundedDivisionByZero.evaluateComputation context) =
        some .poisoned := by
  constructor
  · rfl
  · constructor
    · rfl
    · native_decide

/- Over a stale target, clean no-result and calculation invalidity have the same CLEARED delta and exact empty application but different dependency meaning. -/
example :
    NumericTargetOutcome.noValue.projectDelta (.filled old) =
        (NumericTargetOutcome.invalidNoValue .calculationValue).projectDelta
          (.filled old) ∧
      NumericTargetOutcome.noValue.applyTo (.presentValue old) =
        (NumericTargetOutcome.invalidNoValue .calculationValue).applyTo
          (.presentValue old) ∧
      NumericTargetOutcome.noValue.dependencyObservation ≠
        (NumericTargetOutcome.invalidNoValue .calculationValue).dependencyObservation := by
  decide

/- Fresh silence and unchanged absence still do not make calculation invalidity clean. -/
example :
    NumericTargetOutcome.noValue.projectDelta .empty =
        (NumericTargetOutcome.invalidNoValue .calculationValue).projectDelta .empty ∧
      NumericTargetOutcome.noValue.applyTo .absent =
        (NumericTargetOutcome.invalidNoValue .calculationValue).applyTo .absent ∧
      NumericTargetOutcome.noValue.dependencyObservation ≠
        (NumericTargetOutcome.invalidNoValue .calculationValue).dependencyObservation := by
  decide

end A12Kernel.Conformance.NumericDependency
