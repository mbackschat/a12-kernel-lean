import A12Kernel.Conformance.NumericComputation.Support

/-! # Numeric-computation core locks -/

namespace A12Kernel.Conformance.NumericComputation.Core

open A12Kernel
open A12Kernel.Conformance.NumericComputation.Support

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
