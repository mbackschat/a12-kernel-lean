import A12Kernel.Conformance.NumericComputation.Support

/-! # Numeric-computation core locks -/

namespace A12Kernel.Conformance.NumericComputation.Core

open A12Kernel
open A12Kernel.Conformance.NumericComputation.Support

private def targetDiagnosticOf
    (error? : Option NumericComputationElabError) :
    Option KernelStaticDiagnostic :=
  error?.bind NumericComputationElabError.targetDiagnostic?

/- Checked computation-operation authoring resolves the shared numeric tree and rejects a nested direct reference to its own target. -/
example :
    checkedErrorOf
      (.binary .add (surfaceField ["Root"] "Source")
        (.group (.binary .multiply
          (surfaceField ["Root"] "Target")
          (.literal { value := 2, authoredScale := 0 })))) =
        some (.targetSelfReference targetId) ∧
      checkedErrorOf (.abs (surfaceField ["Root"] "Target")) =
        some (.targetSelfReference targetId) ∧
      checkedErrorOf
        (.round .halfUp omittedRoundingPlaces
          (.binary .add (surfaceField ["Root"] "Target")
            (.literal { value := 1, authoredScale := 0 }))) =
        some (.targetSelfReference targetId) ∧
      checkedErrorOf
        (.binary .multiply
          (.round .halfUp omittedRoundingPlaces
            (surfaceField ["Root"] "Target"))
          (.literal { value := 2, authoredScale := 0 })) =
        some (.targetSelfReference targetId) := by
  native_decide

/- The measured direct-left forms reach scale comparison before the bounded
target-reference refusal. The same-scale field form is a separate positive
branch from the literal mismatch and suppression branches. -/
example :
    let targetField := surfaceField ["Root"] "Target"
    let sourceField := surfaceField ["Root"] "Source"
    let scaleOne : AuthoredNumericExpr SurfaceNumericAtom :=
      .literal { value := 3 / 2, authoredScale := 1 }
    let scaleZero : AuthoredNumericExpr SurfaceNumericAtom :=
      .literal { value := 2, authoredScale := 0 }
    let multiply := AuthoredNumericExpr.binary .multiply targetField scaleOne
    let matchedMultiply :=
      AuthoredNumericExpr.binary .multiply targetField scaleZero
    let addLiteral := AuthoredNumericExpr.binary .add targetField scaleOne
    let addField := AuthoredNumericExpr.binary .add targetField sourceField
    checkedErrorOf multiply =
        some (.operationScaleMismatch 0
          (NumericScaleSummary.binary .multiply
            (NumericScaleSummary.field 0)
            (NumericScaleSummary.constant 1))) ∧
      checkedErrorOf multiply (suppressExactScaleWarning := true) =
        some (.targetSelfReferenceAfterScale targetId) ∧
      checkedErrorOf matchedMultiply =
        some (.targetSelfReferenceAfterScale targetId) ∧
      checkedErrorOf addLiteral =
        some (.operationScaleMismatch 0
          (NumericScaleSummary.binary .add
            (NumericScaleSummary.field 0)
            (NumericScaleSummary.constant 1))) ∧
      checkedErrorOf addLiteral (suppressExactScaleWarning := true) =
        some (.targetSelfReferenceAfterScale targetId) ∧
      checkedErrorOf addField =
        some (.targetSelfReferenceAfterScale targetId) ∧
      targetDiagnosticOf (checkedErrorOf multiply) =
        some .invalidCompareDecimalPlaces ∧
      targetDiagnosticOf
          (checkedErrorOf multiply (suppressExactScaleWarning := true)) =
        some .errorReferenceToCalculatedField ∧
      targetDiagnosticOf (checkedErrorOf matchedMultiply) =
        some .errorReferenceToCalculatedField ∧
      targetDiagnosticOf (checkedErrorOf addLiteral) =
        some .invalidCompareDecimalPlaces ∧
      targetDiagnosticOf
          (checkedErrorOf addLiteral (suppressExactScaleWarning := true)) =
        some .errorReferenceToCalculatedField ∧
      targetDiagnosticOf (checkedErrorOf addField) =
        some .errorReferenceToCalculatedField := by
  native_decide

/- Unmeasured or invalid target-reading shapes retain the old immediate local
refusal, including when a later operand would otherwise fail resolution. -/
example :
    let targetField := surfaceField ["Root"] "Target"
    let sourceField := surfaceField ["Root"] "Source"
    let wrongField := surfaceField ["Root"] "Wrong"
    let scaleOne : AuthoredNumericExpr SurfaceNumericAtom :=
      .literal { value := 3 / 2, authoredScale := 1 }
    let targetThenWrong := AuthoredNumericExpr.binary .add targetField wrongField
    let groupedTargetThenWrong :=
      AuthoredNumericExpr.group (.binary .add targetField wrongField)
    let targetThenRepeatable :=
      AuthoredNumericExpr.binary .add targetField
        (surfaceField ["Root", "Rows"] "Repeated")
    let reverse := AuthoredNumericExpr.binary .add sourceField targetField
    let subtract := AuthoredNumericExpr.binary .subtract targetField scaleOne
    let sameTarget := AuthoredNumericExpr.binary .add targetField targetField
    let twoDivisions :=
      AuthoredNumericExpr.binary .multiply
        (.binary .divide targetField
          (.literal { value := 2, authoredScale := 0 }))
        (.binary .divide (.literal { value := 3, authoredScale := 0 })
          (.literal { value := 4, authoredScale := 0 }))
    let stringLengthTarget : AuthoredNumericExpr SurfaceNumericAtom :=
      .atom (.stringLength (surfacePath ["Root"] "Target"))
    let scaleOneSource : FlatFieldDecl := {
      numberDeclaration 30 "ScaleOneSource" with
      policy := { kind := .number { scale := 1, signed := true } } }
    let scaleOneModel : FlatModel := {
      model with fields := scaleOneSource :: model.fields }
    let targetThenWrongScale :=
      AuthoredNumericExpr.binary .add targetField
        (surfaceField ["Root"] "ScaleOneSource")
    checkedErrorOf targetThenWrong = some (.targetSelfReference targetId) ∧
      checkedErrorOf groupedTargetThenWrong = some (.targetSelfReference targetId) ∧
      checkedErrorOf targetThenRepeatable = some (.targetSelfReference targetId) ∧
      checkedErrorOf reverse = some (.targetSelfReference targetId) ∧
      checkedErrorOf subtract = some (.targetSelfReference targetId) ∧
      checkedErrorOf sameTarget = some (.targetSelfReference targetId) ∧
      checkedErrorOf twoDivisions = some (.targetSelfReference targetId) ∧
      checkedErrorOf stringLengthTarget = some (.targetSelfReference targetId) ∧
      checkedErrorOfIn scaleOneModel targetThenWrongScale =
        some (.targetSelfReference targetId) ∧
      targetDiagnosticOf (checkedErrorOf targetThenWrong) = none ∧
      targetDiagnosticOf (checkedErrorOf groupedTargetThenWrong) = none ∧
      targetDiagnosticOf (checkedErrorOf targetThenRepeatable) = none ∧
      targetDiagnosticOf (checkedErrorOf reverse) = none ∧
      targetDiagnosticOf (checkedErrorOf subtract) = none ∧
      targetDiagnosticOf (checkedErrorOf sameTarget) = none ∧
      targetDiagnosticOf (checkedErrorOf twoDivisions) = none ∧
      targetDiagnosticOf (checkedErrorOf stringLengthTarget) = none ∧
      targetDiagnosticOf
        (checkedErrorOfIn scaleOneModel targetThenWrongScale) = none := by
  native_decide

/- Target policy is attached once: a different scale/signedness summary is rejected before evaluation. -/
example :
    let wrongPolicy : NumericTargetPolicy :=
      { info := { scale := 1, signed := true }
        minFractionalDigits := 0
        minLeMax := by decide }
    targetPolicyAttachErrorOf wrongPolicy =
      some (.targetPolicyMismatch numberInfo wrongPolicy.info) := by
  native_decide

/- Evaluation consumes the retained complete policy rather than accepting a new caller-selected one. -/
example :
    let zeroForbidden := { targetPolicy with zeroAllowed := false }
    checkedTargetResultOf (.literal { value := 0, authoredScale := 0 })
      false zeroForbidden =
        some (.supported (.rejected
          { unscaled := 0, scale := 0 } .zeroNotAllowed)) := by
  native_decide

/- The ordinary checked target route constructs and retains the target policy from the validated declaration; no caller policy argument can override the zero constraint. -/
example :
    checkedDeclaredTargetResultOf
        (.literal { value := 0, authoredScale := 0 }) =
      some (.supported (.rejected
        { unscaled := 0, scale := 0 } .zeroNotAllowed)) ∧
    checkedDeclaredTargetResultOf
        (.literal { value := 3, authoredScale := 0 }) =
      some (.supported (.accepted { unscaled := 3, scale := 0 })) := by
  native_decide

/- A second declaration-owned constraint class is integrated through the same construction: minimum scale controls stored identity and the inclusive maximum remains the later target check. -/
example :
    checkedBoundedScaleTwoTargetResultOf 5 =
        some (.supported (.accepted { unscaled := 500, scale := 2 })) ∧
      checkedBoundedScaleTwoTargetResultOf 6 =
        some (.supported (.rejected
          { unscaled := 600, scale := 2 } .aboveMaximum)) := by
  native_decide

/- Number target constraints cannot be attached to another kind. -/
example :
    let nonNumber := { wrong with
      numericTargetConstraints := { zeroAllowed := false } }
    errorOf
      ({ model with fields := model.fields.map fun (declaration : FlatFieldDecl) =>
        if declaration.id == wrongId then nonNumber else declaration }).validate =
      some (.numericTargetConstraintsRequireNumber nonNumber.path) := by
  native_decide

/- Required fractional digits cannot exceed the existing Number scale. -/
example :
    let excessiveMinimum := { target with
      numericTargetConstraints := { minFractionalDigits := 1 } }
    errorOf
      ({ model with fields := model.fields.map fun (declaration : FlatFieldDecl) =>
        if declaration.id == targetId then excessiveMinimum else declaration }).validate =
      some (.numericMinimumFractionalDigitsExceedMaximum
        excessiveMinimum.path 1 0) := by
  native_decide

/- `fieldScaleCap`: 14 is declarable and 15 is not. The pair is the separator — a bound stated
only as "at most 14" without the accepted side cannot distinguish this from an off-by-one, and
the kernel's refusal here carries no MVK code. Distinct from `maxRoundingPlaces`, which bounds a
rounding argument at the same number on a different axis (`spec/04`). -/
example :
    let atCap := { target with
      policy := { target.policy with kind := .number { scale := 14, signed := true } } }
    let aboveCap := { target with
      policy := { target.policy with kind := .number { scale := 15, signed := true } } }
    errorOf
      ({ model with fields := model.fields.map fun (declaration : FlatFieldDecl) =>
        if declaration.id == targetId then atCap else declaration }).validate = none ∧
    errorOf
      ({ model with fields := model.fields.map fun (declaration : FlatFieldDecl) =>
        if declaration.id == targetId then aboveCap else declaration }).validate =
      some (.numericFractionalDigitsAboveCap aboveCap.path 15 14) := by
  native_decide

/- A present effective integer-digit capacity is positive. -/
example :
    let zeroCapacity := { target with
      numericTargetConstraints := { maxIntegerDigits := some 0 } }
    errorOf
      ({ model with fields := model.fields.map fun (declaration : FlatFieldDecl) =>
        if declaration.id == targetId then zeroCapacity else declaration }).validate =
      some (.numericMaximumIntegerDigitsZero zeroCapacity.path) := by
  native_decide

/- The one legal warning suppression bypasses only the result-scale gate and selects the no-fit target branch carried by the checked operation. -/
example :
    let scaleOne :=
      AuthoredNumericExpr.literal
        (Atom := SurfaceNumericAtom) { value := 11 / 10, authoredScale := 1 }
    checkedErrorOf scaleOne =
        some (.operationScaleMismatch 0 (NumericScaleSummary.constant 1)) ∧
      checkedErrorOf scaleOne (suppressExactScaleWarning := true) = none ∧
      checkedTargetResultOf scaleOne true =
        some (.supported (.rejected
          { unscaled := 11, scale := 1 } .suppressedScaleMismatch)) := by
  native_decide

/- Every reached scale mismatch and the bounded after-scale target reference
project to their measured Kernel classes. Earlier local self-reference and
unrelated authoring failures remain explicitly unmapped. -/
example :
    let scaleOne :=
      AuthoredNumericExpr.literal
        (Atom := SurfaceNumericAtom) { value := 11 / 10, authoredScale := 1 }
    targetDiagnosticOf (checkedErrorOf scaleOne) =
        some .invalidCompareDecimalPlaces ∧
      targetDiagnosticOf
        (checkedErrorOf scaleOne (suppressExactScaleWarning := true)) = none ∧
      NumericComputationElabError.targetDiagnostic?
        (.targetSelfReferenceAfterScale targetId) =
          some .errorReferenceToCalculatedField ∧
      NumericComputationElabError.targetDiagnostic?
        (.targetSelfReference targetId) = none ∧
      NumericComputationElabError.targetDiagnostic?
        (.authoring .tooManyDivisions) = none ∧
      NumericComputationElabError.targetDiagnostic? .unsupportedExpression = none ∧
      KernelStaticDiagnostic.kernelCode .invalidCompareDecimalPlaces =
        "MVK_INVALID_COMPARE_DEC_PLACES" ∧
      KernelStaticDiagnostic.kernelCode .errorReferenceToCalculatedField =
        "MVK_ERROR_REFERENCE_TO_CALCULATED_FIELD" := by
  native_decide

/- Suppression does not bypass the independent plain-authoring rejection. -/
example :
    let twoDivisions :=
      AuthoredNumericExpr.binary .multiply
        (.binary .divide (surfaceField ["Root"] "Source")
          (.literal { value := 2, authoredScale := 0 }))
        (.binary .divide (.literal { value := 3, authoredScale := 0 })
          (.literal { value := 4, authoredScale := 0 }))
    checkedErrorOf twoDivisions (suppressExactScaleWarning := true) =
      some (.authoring .tooManyDivisions) := by
  native_decide

/- A checked operation reuses the existing numeric evaluator; unlike a validation comparison, a constant-only computation is legal. -/
example :
    checkedResultOf
        (.binary .add (surfaceField ["Root"] "Source")
          (.literal { value := 2, authoredScale := 0 }))
        (context (checkedNumber (.parsed (.num 3)))) = some (.value 5) ∧
      checkedResultOf (.literal { value := 7, authoredScale := 0 }) =
        some (.value 7) := by
  native_decide

example :
    noBaseYearErrorOf surfaceBaseYear = some .baseYearNotDeclared ∧
    checkedResultOf surfaceBaseYear = some (.value 2020) ∧
    checkedResultOf (.binary .add surfaceBaseYear
      (surfaceField ["Root"] "Source"))
      (context (checkedNumber (.parsed (.num 1)))) = some (.value 2021) ∧
    checkedErrorOf (.binary .add surfaceBaseYear
      (.literal { value := 0, authoredScale := 2 })) =
        some (.operationScaleMismatch 0
          ((NumericScaleSummary.field 0).union
            (NumericScaleSummary.constant 2))) := by
  native_decide

example :
    let directYear := surfaceBaseYearDatePart .direct .year
    let finishDay := surfaceBaseYearDatePart (.range .finish) .day
    let finishQuarter := surfaceBaseYearDatePart (.range .finish) .quarter
    noBaseYearErrorOf finishDay = some .baseYearNotDeclared ∧
      checkedResultOf directYear = some (.value 2020) ∧
      checkedResultOf finishDay = some (.value 31) ∧
      checkedResultOf finishQuarter = some (.value 4) ∧
      checkedResultOf (.abs finishDay) = some (.value 31) ∧
      checkedResultOf (.round .halfUp omittedRoundingPlaces finishDay) =
        some (.value 31) ∧
      checkedResultOf (.binary .add finishDay
        (surfaceField ["Root"] "Source"))
        (context (checkedNumber (.parsed (.num 1)))) = some (.value 32) ∧
      checkedResultOf (.abs surfaceBaseYear) = some (.value 2020) ∧
      checkedResultOf
        (.round .floor omittedRoundingPlaces (.group surfaceBaseYear)) =
          some (.value 2020) := by
  native_decide

/- Direct functions are the smallest specialization of the complete numeric-operation route shared with numeric validation. -/
example :
    let sourceField := surfaceField ["Root"] "Source"
    let input := context (checkedNumber (.parsed (.num (5 / 2))))
    checkedResultOf (.round .halfUp omittedRoundingPlaces sourceField) input =
        some (.value 3) ∧
      checkedResultOf (.abs sourceField)
        (context (checkedNumber (.parsed (.num (-5))))) = some (.value 5) ∧
      checkedResultOf
        (AuthoredNumericExpr.extremumList .maximum sourceField
          [.literal { value := 4, authoredScale := 0 }]) input =
        some (.value 4) := by
  native_decide

/- Checked computation retains each operand-list call boundary while admitting complete numeric operands and surrounding arithmetic. -/
example :
    let sourceField := surfaceField ["Root"] "Source"
    let input := context (checkedNumber (.parsed (.num 5)))
    checkedResultOf
        (AuthoredNumericExpr.extremumList .minimum
          (AuthoredNumericExpr.extremumList .maximum sourceField
            [.literal { value := 1, authoredScale := 0 }])
          [.literal { value := 2, authoredScale := 0 }]) input =
        some (.value 2) ∧
      checkedResultOf
        (AuthoredNumericExpr.extremumList .minimum
          (.binary .add sourceField
            (.literal { value := 1, authoredScale := 0 }))
          [.group (.literal { value := 2, authoredScale := 0 })]) input =
        some (.value 2) ∧
      checkedResultOf
        (.binary .add
          (AuthoredNumericExpr.extremumList .minimum sourceField
            [.literal { value := 2, authoredScale := 0 }])
          (.literal { value := 1, authoredScale := 0 })) input =
        some (.value 3) := by
  native_decide

/- Each checked Min/Max call still rejects a second immediate constant, while unary wrappers compose in authored order around the completed call. -/
example :
    let sourceField := surfaceField ["Root"] "Source"
    checkedErrorOf
        (AuthoredNumericExpr.extremumList .minimum sourceField
          [.literal { value := 1, authoredScale := 0 },
            .literal { value := 2, authoredScale := 0 }]) =
          some .unsupportedExpression ∧
      checkedErrorOf
        (.round .halfUp omittedRoundingPlaces
          (.binary .add sourceField
            (.literal { value := 1, authoredScale := 0 }))) =
          none ∧
      checkedResultOf
        (.round .halfUp omittedRoundingPlaces
          (.binary .add sourceField
            (.literal { value := 1, authoredScale := 0 })))
        (context (checkedNumber (.parsed (.num 2)))) = some (.value 3) ∧
      checkedResultOf
        (.abs (.binary .subtract sourceField
          (surfaceField ["Root"] "Later")))
        (context (checkedNumber (.parsed (.num 2)))
          (checkedNumber (.parsed (.num 5)))) = some (.value 3) ∧
      checkedResultOf
        (.round .halfUp omittedRoundingPlaces
          (.binary .divide sourceField
            (.literal { value := 0, authoredScale := 0 }))) =
          some .domainFailure ∧
      checkedResultOf
        (.binary .add
          (.round .halfUp omittedRoundingPlaces
            (.binary .divide sourceField
              (.literal { value := 0, authoredScale := 0 })))
          (.literal { value := 1, authoredScale := 0 })) =
          some .domainFailure ∧
      checkedResultOf
        (.round .floor omittedRoundingPlaces (.abs sourceField))
        (context (checkedNumber (.parsed (.num ((-14 : Rat) / 10))))) =
          some (.value 1) ∧
      checkedResultOf
        (.abs (.round .floor omittedRoundingPlaces sourceField))
        (context (checkedNumber (.parsed (.num ((-14 : Rat) / 10))))) =
          some (.value 2) ∧
      checkedResultOf
        (.abs (AuthoredNumericExpr.extremumList .minimum sourceField
          [surfaceField ["Root"] "Later"]))
        (context (checkedNumber (.parsed (.num (-3))))
          (checkedNumber (.parsed (.num 2)))) = some (.value 3) := by
  native_decide

example :
    checkedErrorOf (surfaceField ["Root"] "Wrong") =
        some (.operandNotNumber wrong.path) ∧
      checkedErrorOf (surfaceField ["Root", "Rows"] "Repeated") =
        some (.resolve (.repeatableReference repeated.path)) ∧
      checkedErrorOf (.literal { value := 1, authoredScale := 0 }) wrongId =
        some (.targetNotNumber wrongId) := by
  native_decide

/- Authoring and result-scale checks precede runtime evaluation and retain their distinct rejection classes. -/
example :
    let twoDivisions :=
      AuthoredNumericExpr.binary .multiply
        (.binary .divide (surfaceField ["Root"] "Source")
          (.literal { value := 2, authoredScale := 0 }))
        (.binary .divide (.literal { value := 3, authoredScale := 0 })
          (.literal { value := 4, authoredScale := 0 }))
    checkedErrorOf twoDivisions = some (.authoring .tooManyDivisions) ∧
      checkedErrorOf (.literal { value := 1, authoredScale := 1 }) =
        some (.operationScaleMismatch 0 (NumericScaleSummary.constant 1)) := by
  native_decide

/- Empty Number is a real computation value, not clean no-selection. -/
example : resultOf (field source) = some (.value 0) := by
  rfl

example : resultOf (binary .add (field source) (literal 2)) =
    some (.value 2) := by
  native_decide

example : resultOf (field source)
    (context ((checkedNumber .empty).withFinding .required)) =
      some (.value 0) := by
  rfl


end A12Kernel.Conformance.NumericComputation.Core
