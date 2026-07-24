import A12Kernel.Conformance.NumericValidation.Support

/-! # Checked numeric-validation comparison locks -/

namespace A12Kernel.Conformance.NumericValidation.Comparison

open A12Kernel
open A12Kernel.Conformance.NumericValidation.Support

/- Checked tolerance bypasses exact-comparison scale agreement and preserves directional arithmetic fillability. -/
example : (elaborateNumericComparison model ["Order"]
    (tolerance .range1 (atom "U") (atom "Scale2"))).isOk = true := by
  native_decide

example :
    errorOf (twoSided .equal (atom "U") baseYear) =
      some .baseYearNotDeclared ∧
    errorOf (twoSided .equal (atom "Scale2") baseYear) baseYearModel =
      some (.exactScaleMismatch
        (NumericScaleSummary.field 2) (NumericScaleSummary.field 0)) ∧
    (elaborateNumericComparison baseYearModel ["Order"]
      (tolerance .range1 (atom "Scale2") baseYear)).isOk = true ∧
    errorOf (twoSided .equal (.abs baseYear) (atom "U")) baseYearModel =
      none := by
  native_decide

example :
    verdictOf (tolerance .range1 (atom "U") baseYear)
        (raw (.parsed (.num 2022))) true baseYearModel = some (.fired .value) ∧
      verdictOf (twoSided .equal (atom "U") baseYear)
        (raw (.parsed (.num 2020))) true baseYearModel = some (.fired .value) ∧
      verdictOf (twoSided .equal
        (.binary .add baseYear (atom "U")) (literal 2021 0))
        (raw (.parsed (.num 1))) true baseYearModel = some (.fired .value) ∧
      verdictOf (twoSided .equal (.abs baseYear) (atom "U"))
        (raw (.parsed (.num 2020))) true baseYearModel = some (.fired .value) ∧
      verdictOf (twoSided .equal
        (.binary .add
          (.round .floor omittedRoundingPlaces (.group baseYear))
          (atom "U"))
        (literal 2021 0))
        (raw (.parsed (.num 1))) true baseYearModel = some (.fired .value) := by
  native_decide

example : errorOf (twoSided .equal baseYear (literal 2020 0)) baseYearModel =
    some .constantExpression := by
  native_decide

example :
    let directYear := baseYearDatePart .direct .year
    let finishDay := baseYearDatePart (.range .finish) .day
    let finishQuarter := baseYearDatePart (.range .finish) .quarter
    errorOf (twoSided .equal (atom "U") finishDay) =
        some .baseYearNotDeclared ∧
      verdictOf (twoSided .equal (atom "U") directYear)
        (raw (.parsed (.num 2020))) true baseYearModel = some (.fired .value) ∧
      verdictOf (twoSided .equal (atom "U") finishDay)
        (raw (.parsed (.num 31))) true baseYearModel = some (.fired .value) ∧
      verdictOf (twoSided .equal (atom "U") finishQuarter)
        (raw (.parsed (.num 4))) true baseYearModel = some (.fired .value) ∧
      verdictOf (twoSided .equal
        (.binary .add (atom "U") finishDay) (literal 32 0))
        (raw (.parsed (.num 1))) true baseYearModel = some (.fired .value) := by
  native_decide

example :
    let finishDay := baseYearDatePart (.range .finish) .day
    errorOf (twoSided .equal finishDay (literal 31 0)) baseYearModel =
        some .constantExpression ∧
      verdictOf (twoSided .equal (.abs finishDay) (atom "U"))
        (raw (.parsed (.num 31))) true baseYearModel = some (.fired .value) ∧
      (elaborateNumericComparison baseYearModel ["Order"]
        (twoSided .equal
          (.round .halfUp ⟨2, by decide⟩ finishDay)
          (atom "Scale2"))).isOk = true ∧
      errorOf (twoSided .equal (atom "Scale2") finishDay) baseYearModel =
        some (.exactScaleMismatch
          (NumericScaleSummary.field 2) (NumericScaleSummary.field 0)) := by
  native_decide

example : verdictOf
    (tolerance .range1
      (atom "U")
      (.binary .add (atom "V") (literal 2 0)))
    (raw .empty (.parsed (.num 0))) = some (.fired .omission) := by
  native_decide

example : verdictOf
    (tolerance .range1
      (atom "U")
      (.binary .subtract (atom "V") (literal 2 0)))
    (raw .empty (.parsed (.num 0))) = some (.fired .value) := by
  native_decide

/- The closed band is not ordinary inequality: its exact endpoint remains quiet. -/
example : verdictOf
    (tolerance .range1 (atom "U") (literal 1 0))
    (raw (.parsed (.num 0))) = some .notFired := by
  native_decide

example : verdictOf
    (comparison .notEqual (atom "U") 1)
    (raw (.parsed (.num 0))) = some (.fired .value) := by
  native_decide

/- The checked bridge keeps formal invalidity, pure arithmetic domain failure, and the row gate distinct. -/
example : verdictOf
    (tolerance .range1 (atom "U") (literal 5 0))
    (raw (.rejected .malformed)) = some .unknown := by
  native_decide

example : verdictOf
    (tolerance .range1
      (.binary .divide (literal 1 0) (atom "U"))
      (literal 5 0)) = some .notFired := by
  native_decide

example : verdictOf
    (tolerance .range1 (atom "U") (literal 5 0))
    raw false = some .notFired := by
  native_decide

/- Tolerance shares the checked expression subset and still rejects constant-only trees. -/
example : errorOf
    (tolerance .range1 (literal 0 0) (literal 5 0)) =
      some .constantExpression := by
  native_decide

example : verdictOf
    (tolerance .range1 (.power (atom "U") (literal 2 0)) (literal 5 0))
    (raw (.parsed (.num 1))) = some (.fired .value) := by
  native_decide

/- The right operand's grow-only empty Number changes a true comparison from VALUE to OMISSION. -/
example : verdictOf
    (twoSided .greaterEqual (atom "V") (atom "U"))
    (raw .empty (.parsed (.num 0))) = some (.fired .omission) := by
  native_decide

example : verdictOf
    (twoSided .greaterEqual (atom "V") (atom "U"))
    (raw (.parsed (.num 0)) (.parsed (.num 0))) = some (.fired .value) := by
  native_decide

/- Right-side movement is directional, not a generic "some input was empty" bit. -/
example : verdictOf
    (twoSided .less
      (atom "V")
      (.binary .add (literal 1 0) (atom "U")))
    (raw .empty (.parsed (.num 0))) = some (.fired .value) := by
  native_decide

example : verdictOf
    (twoSided .less
      (atom "V")
      (.binary .subtract (literal 1 0) (atom "U")))
    (raw .empty (.parsed (.num 0))) = some (.fired .omission) := by
  native_decide

example : verdictOf
    (twoSided .notEqual
      (atom "V")
      (.binary .add (literal 1 0) (atom "U")))
    (raw .empty (.parsed (.num 0))) = some (.fired .value) := by
  native_decide

example : verdictOf
    (twoSided .notEqual
      (atom "V")
      (.binary .subtract (literal 1 0) (atom "U")))
    (raw .empty (.parsed (.num 0))) = some (.fired .omission) := by
  native_decide

/- In a content-bearing selected row, the runtime reads aliases independently; the fillability abstraction has no dependency deduplication. -/
example : verdictOf
    (twoSided .equal (atom "U") (atom "U")) =
      some (.fired .omission) := by
  native_decide

/- Equality-boundary cases separate the strict and inclusive operators. -/
example : verdictOf
    (twoSided .greater (atom "V") (atom "U"))
    (raw .empty (.parsed (.num 0))) = some .notFired := by
  native_decide

example : verdictOf
    (twoSided .lessEqual (atom "V") (atom "U"))
    (raw .empty (.parsed (.num 0))) = some (.fired .value) := by
  native_decide

/- This one case crosses checked paths, empty substitution, static ordering legality, arithmetic fillability, scale-19 comparison, polarity, and the row gate. -/
example : verdictOf
    (comparison .greaterEqual (.binary .multiply (atom "U") dividedThird) 0) =
      some (.fired .value) := by
  native_decide

private def precisionAmplifier : Rat := 10 ^ 31

private def amplifiedThird : AuthoredNumericExpr SurfaceNumericAtom :=
  .binary .multiply
    (.binary .multiply
      (atom "U")
      (.group (.binary .divide (literal 1 0) (literal 3 0))))
    (literal precisionAmplifier (-31))

/- The checked consumer must use the one-pass lowered tree, not directly fold the authored tree. -/
example : verdictOf
    (comparison .greaterEqual amplifiedThird precisionAmplifier (-31))
    (raw (.parsed (.num 3))) = some (.fired .value) := by
  native_decide

/- The same lowering stage is independently required on the right comparison operand. -/
example : verdictOf
    (twoSided .less
      (literal (precisionAmplifier - 1 / (10 ^ 19)) 19)
      amplifiedThird)
    (raw (.parsed (.num 3))) = some (.fired .value) := by
  native_decide

/- Tolerance consumes the same one-pass lowered tree: the lowered gap is exactly the closed range-1 boundary. -/
example : verdictOf
    (tolerance .range1
      amplifiedThird
      (literal (precisionAmplifier + 1) 0))
    (raw (.parsed (.num 3))) = some .notFired := by
  native_decide

/- A counterfactual direct authored fold would retain a scale-19-visible gap beyond the band and fire. -/
example : NumericToleranceRange.range1.eval
    (.value (precisionAmplifier - 1 / (10 ^ 19)) .fixed)
    (.value (precisionAmplifier + 1) .fixed) = .fired .value := by
  native_decide

/- Both total binary branches are exercised through the integrated checked route. -/
example : verdictOf
    (comparison .equal
      (.binary .subtract
        (.binary .add (atom "U") (literal 3 0))
        (literal 1 0))
      7)
    (raw (.parsed (.num 5))) = some (.fired .value) := by
  native_decide

example : verdictOf
    (comparison .greaterEqual (.binary .multiply (atom "U") dividedThird) 0)
    raw false = some .notFired := by
  native_decide

example : verdictOf
    (comparison .greaterEqual (.binary .multiply (atom "U") (literal (-4) 0)) (-100)) =
      some (.fired .omission) := by
  native_decide

example : verdictOf
    (comparison .greaterEqual (.binary .multiply (atom "U") (literal (-4) 0)) (-100))
    (raw (.parsed (.num 5))) = some (.fired .value) := by
  native_decide

example : verdictOf
    (comparison .greaterEqual (.binary .multiply (atom "U") (literal (-4) 0)) (-100))
    (raw (.rejected .malformed)) = some .unknown := by
  native_decide

example : verdictOf
    (comparison .less (.binary .divide (literal 1 0) (atom "U")) 100) =
      some .notFired := by
  native_decide

example : verdictOf
    (twoSided .less (literal 0 0) (atom "V"))
    (raw .empty (.rejected .malformed)) = some .unknown := by
  native_decide

example : verdictOf
    (twoSided .less
      (literal 0 0)
      (.binary .divide (literal 1 0) (atom "U"))) =
      some .notFired := by
  native_decide

/- The Lean projection conservatively keeps formal invalidity unknown beside a domain failure; this mixed internal precedence is not a kernel-correspondence claim. -/
example : verdictOf
    (twoSided .less
      (.binary .divide (literal 1 0) (atom "U"))
      (atom "V"))
    (raw .empty (.rejected .malformed)) = some .unknown := by
  native_decide

example : verdictOf
    (twoSided .less
      (atom "V")
      (.binary .divide (literal 1 0) (atom "U")))
    (raw .empty (.rejected .malformed)) = some .unknown := by
  native_decide

/- Exact comparison accepts padding only on the expandable, smaller-scale side. -/
example : (elaborateNumericComparison model ["Order"]
    (comparison .equal (atom "Scale2") 0)).isOk = true := by
  native_decide

example : errorOf (comparison .equal (atom "U") 0 2) =
    some (.exactScaleMismatch
      { scale := .exact 0, canExpandScale := false }
      { scale := .exact 2, canExpandScale := true }) := by
  native_decide

example : errorOf (comparison .notEqual (atom "U") 0 2) =
    some (.exactScaleMismatch
      { scale := .exact 0, canExpandScale := false }
      { scale := .exact 2, canExpandScale := true }) := by
  native_decide

example : errorOf (twoSided .equal (atom "U") (atom "Scale2")) =
    some (.exactScaleMismatch
      { scale := .exact 0, canExpandScale := false }
      { scale := .exact 2, canExpandScale := false }) := by
  native_decide

/- The one legal warning suppression bypasses exact scale rejection without changing the evaluated comparison. -/
example : verdictOf
    (suppressScaleWarning (comparison .equal (atom "U") 0 2))
    (raw (.parsed (.num 0))) = some (.fired .value) := by
  native_decide

example : verdictOf
    (suppressScaleWarning
      (twoSided .notEqual (atom "U") (atom "Scale2")))
    (raw (.parsed (.num 0)) .empty .empty (.parsed (.num 1))) =
      some (.fired .value) := by
  native_decide

example : (elaborateNumericComparison model ["Order"]
    (twoSided .greater (atom "U") (atom "Scale2"))).isOk = true := by
  native_decide

/- Division has unknown derived scale: ordering admits it, exact comparison does not. -/
example : (elaborateNumericComparison model ["Order"]
    (comparison .less (.binary .divide (atom "U") (literal 2 0)) 0)).isOk = true := by
  native_decide

example : errorOf
    (comparison .equal (.binary .divide (atom "U") (literal 2 0)) 0) =
      some (.exactScaleMismatch
        { scale := .unknown, canExpandScale := false }
        { scale := .exact 0, canExpandScale := true }) := by
  native_decide

/- Suppression also admits the kernel's unknown derived scale rather than guessing a concrete scale. -/
example : verdictOf
    (suppressScaleWarning
      (comparison .equal
        (.binary .divide (atom "U") (literal 2 0)) 2))
    (raw (.parsed (.num 4))) = some (.fired .value) := by
  native_decide

/- Suppression is not a general authoring escape hatch. -/
example : errorOf
    (suppressScaleWarning
      (comparison .equal
        (.binary .divide
          (.binary .divide (atom "U") (literal 2 0))
          (literal 3 0))
        0)) = some (.authoring .tooManyDivisions) := by
  native_decide

/- Division-region legality resets at the comparison boundary, so one division on each side is accepted. -/
example : (elaborateNumericComparison model ["Order"]
    (twoSided .less
      (.binary .divide (atom "U") (literal 2 0))
      (.binary .divide (atom "V") (literal 3 0)))).isOk = true := by
  native_decide

example : errorOf
    (comparison .less
      (.binary .divide
        (.binary .divide (atom "U") (literal 2 0))
        (literal 3 0))
      0) = some (.authoring .tooManyDivisions) := by
  native_decide

example : errorOf
    (twoSided .less
      (atom "U")
      (.binary .divide
        (.binary .divide (atom "V") (literal 2 0))
        (literal 3 0))) =
      some (.authoring .tooManyDivisions) := by
  native_decide


end A12Kernel.Conformance.NumericValidation.Comparison
