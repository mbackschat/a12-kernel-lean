import A12Kernel.Elaboration.NumericValidation

/-! # Checked numeric-validation integration locks -/

namespace A12Kernel.Conformance.NumericValidation

open A12Kernel

private def unsigned : NumField := { scale := 0, signed := false }
private def signed : NumField := { scale := 0, signed := true }
private def scaleTwo : NumField := { scale := 2, signed := false }

private def model : FlatModel :=
  { fields := [
      { id := 0, groupPath := ["Order"], name := "U",
        policy := { kind := .number unsigned } },
      { id := 1, groupPath := ["Order"], name := "V",
        policy := { kind := .number unsigned } },
      { id := 2, groupPath := ["Order"], name := "Scale2",
        policy := { kind := .number scaleTwo } },
      { id := 3, groupPath := ["Order"], name := "Flag",
        policy := { kind := .boolean } },
      { id := 4, groupPath := ["Reference"], name := "Other",
        policy := { kind := .number unsigned } },
      { id := 5, groupPath := ["Order", "Items"], name := "Item",
        policy := { kind := .number unsigned }, repeatableScope := [10] },
      { id := 6, groupPath := ["Order"], name := "S",
        policy := { kind := .number signed } }],
    repeatableGroups := [{ level := 10, path := ["Order", "Items"] }] }

private def path (groups : List String) (field : String) : SurfaceFieldPath :=
  { base := .absolute, groups, field }

private def atom (name : String) : AuthoredNumericExpr SurfaceFieldPath :=
  .atom (path ["Order"] name)

private def literal (value : Rat) (authoredScale : Int) :
    AuthoredNumericExpr SurfaceFieldPath :=
  .literal { value, authoredScale }

private def comparison (op : NumericComparisonOp)
    (left : AuthoredNumericExpr SurfaceFieldPath)
    (rightValue : Rat) (rightScale : Int := 0) :
    SurfaceNumericComparison :=
  { op := .ordinary op, left, right := literal rightValue rightScale }

private def twoSided (op : NumericComparisonOp)
    (left right : AuthoredNumericExpr SurfaceFieldPath) :
    SurfaceNumericComparison :=
  { op := .ordinary op, left, right }

private def raw (u v s scale2Value : RawCell := .empty) : RawFlatContext where
  read id :=
    if id == 0 then u else if id == 1 then v else if id == 2 then scale2Value
      else if id == 6 then s else .empty

private def verdictOf (surface : SurfaceNumericComparison)
    (context : RawFlatContext := raw) (hasContent : Bool := true) : Option Verdict :=
  (elaborateAndEvalNumericComparison model ["Order"] context hasContent surface).toOption

private def errorOf (surface : SurfaceNumericComparison) :
    Option NumericValidationElabError :=
  match elaborateNumericComparison model ["Order"] surface with
  | .ok _ => none
  | .error error => some error

private def suppressScaleWarning
    (surface : SurfaceNumericComparison) : SurfaceNumericComparison :=
  { surface with suppressExactScaleWarning := true }

private def tolerance (range : NumericToleranceRange)
    (left right : AuthoredNumericExpr SurfaceFieldPath) :
    SurfaceNumericComparison :=
  { op := .tolerance range, left, right }

private def dividedThird : AuthoredNumericExpr SurfaceFieldPath :=
  .group (.binary .divide (literal 3 0) (literal 3 0))

/- Checked tolerance bypasses exact-comparison scale agreement and preserves directional arithmetic fillability. -/
example : (elaborateNumericComparison model ["Order"]
    (tolerance .range1 (atom "U") (atom "Scale2"))).isOk = true := by
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

private def amplifiedThird : AuthoredNumericExpr SurfaceFieldPath :=
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

/- Checked power reuses authored scale, nesting, runtime value, and directional-fillability semantics. -/
example : verdictOf
    (comparison .equal (.power (atom "U") (literal 2 0)) 4)
    (raw (.parsed (.num 2))) = some (.fired .value) := by
  native_decide

example : verdictOf
    (comparison .less (.power (atom "U") (literal 2 0)) 10) =
      some (.fired .omission) := by
  native_decide

/- Runtime-invalid integral regions project to quiet validation domain failure. -/
example : verdictOf
    (comparison .less (.power (atom "U") (literal (-1) 0)) 1)
    (raw (.parsed (.num 0))) = some .notFired := by
  native_decide

example : verdictOf
    (comparison .less (.power (atom "U") (literal 1001 0)) 1)
    (raw (.parsed (.num 2))) = some .notFired := by
  native_decide

/- Empty exponent polarity is not a generic given-bit: unsigned and signed zero exponents produce different directions at fixed base zero. -/
example : verdictOf
    (comparison .greaterEqual (.power (literal 0 0) (atom "U")) 1) =
      some (.fired .omission) := by
  native_decide

example : verdictOf
    (comparison .greaterEqual (.power (literal 0 0) (atom "S")) 1) =
      some (.fired .value) := by
  native_decide

/- Fractional-scale exponents remain a static rejection before runtime. -/
example : errorOf
    (comparison .less
      (.power (atom "U") (literal ((1 : Rat) / 2) 1)) 1) =
      some .unsupportedExpression := by
  native_decide

/- Direct-left nested power is rejected, while grouping creates the legal fresh authoring region. -/
example : errorOf
    (comparison .less
      (.power (.power (atom "U") (literal 2 0)) (literal 3 0)) 100) =
      some (.authoring .directLeftNestedPower) := by
  native_decide

example : verdictOf
    (comparison .less
      (.power (.group (.power (atom "U") (literal 2 0))) (literal 3 0)) 100)
    (raw (.parsed (.num 2))) = some (.fired .value) := by
  native_decide

/- A source-confirmed root rounding operation is admitted without widening the unclosed wrapper traversal. -/
example : verdictOf
    (comparison .less (.round .halfUp omittedRoundingPlaces (atom "U")) 1) =
      some (.fired .omission) := by
  native_decide

/- The checked route retains the existing negative half-tie behavior. The mode-parametric delegation law covers all three modes without duplicating their pure matrix here. -/
example : verdictOf
    (comparison .equal (.round .halfUp omittedRoundingPlaces (atom "U")) (-3))
    (raw (.parsed (.num ((-25 : Rat) / 10)))) = some (.fired .value) := by
  native_decide

/- The independently traversed right operand uses the same admitted root-rounding seam. -/
example : verdictOf
    (twoSided .equal
      (literal 1 0)
      (.round .floor omittedRoundingPlaces (atom "U")))
    (raw (.parsed (.num ((16 : Rat) / 10)))) = some (.fired .value) := by
  native_decide

/- The rounded result's authored places, rather than the source field's scale, control exact-comparison admission. -/
example : (elaborateNumericComparison model ["Order"]
    (twoSided .equal
      (.round .halfUp ⟨2, by decide⟩ (atom "U"))
      (atom "Scale2"))).isOk = true := by
  native_decide

/- Formal invalidity survives the wrapper instead of becoming a rounded zero. -/
example : verdictOf
    (comparison .less (.round .halfUp omittedRoundingPlaces (atom "U")) 1)
    (raw (.rejected .malformed)) = some .unknown := by
  native_decide

/- Nested wrapper/arithmetic authoring remains deliberately outside this checked fragment. -/
example : errorOf
    (comparison .less
      (.binary .add
        (.round .halfUp omittedRoundingPlaces (atom "U"))
        (literal 1 0))
      0) = some .unsupportedExpression := by
  native_decide

/- Root rounding over arithmetic is the opposite unclosed nesting direction and must not be mistaken for direct-field rounding. -/
example : errorOf
    (comparison .less
      (.round .halfUp omittedRoundingPlaces
        (.binary .add (atom "U") (literal 1 0)))
      0) = some .unsupportedExpression := by
  native_decide

/- Root absolute value is the second admitted numeric value function. Its sign-sensitive fillability is visible for signed empty input. -/
example : verdictOf (comparison .greaterEqual (.abs (atom "S")) 0) =
    some (.fired .value) := by
  native_decide

example : verdictOf (comparison .equal (.abs (atom "S")) 5)
    (raw .empty .empty (.parsed (.num (-5)))) = some (.fired .value) := by
  native_decide

/- The independently traversed right operand applies the same absolute-value seam. -/
example : verdictOf
    (twoSided .equal (literal 5 0) (.abs (atom "S")))
    (raw .empty .empty (.parsed (.num (-5)))) = some (.fired .value) := by
  native_decide

example : verdictOf (comparison .less (.abs (atom "S")) 1)
    (raw .empty .empty (.rejected .malformed)) = some .unknown := by
  native_decide

/- Absolute value preserves the operand's static scale. -/
example : (elaborateNumericComparison model ["Order"]
    (twoSided .equal (.abs (atom "Scale2")) (atom "Scale2"))).isOk = true := by
  native_decide

/- Both wrapper/arithmetic nesting directions remain outside the checked boundary. -/
example : errorOf
    (comparison .less
      (.binary .add (.abs (atom "U")) (literal 1 0))
      0) = some .unsupportedExpression := by
  native_decide

example : errorOf
    (comparison .less
      (.abs (.binary .add (atom "U") (literal 1 0)))
      0) = some .unsupportedExpression := by
  native_decide

/- Checked multi-operand Min/Max use one root over direct same-group Number fields. Empty Number remains a directional zero competitor. -/
example : verdictOf
    (comparison .less
      (AuthoredNumericExpr.extremumList .minimum (atom "U") [atom "V"]) 100)
    (raw .empty (.parsed (.num 4))) = some (.fired .omission) := by
  native_decide

example : verdictOf
    (comparison .greater
      (AuthoredNumericExpr.extremumList .minimum (atom "U") [atom "V"]) (-100))
    (raw .empty (.parsed (.num 4))) = some (.fired .value) := by
  native_decide

example : verdictOf
    (comparison .greater
      (AuthoredNumericExpr.extremumList .maximum (atom "S") [atom "V"]) (-100))
    (raw .empty (.parsed (.num (-4))) .empty) = some (.fired .omission) := by
  native_decide

example : verdictOf
    (comparison .less
      (AuthoredNumericExpr.extremumList .minimum
        (atom "U") [atom "V", atom "S"])
      100)
    (raw (.parsed (.num 2)) (.parsed (.num 4)) (.rejected .malformed)) =
      some .unknown := by
  native_decide

/- Min/Max derive the maximum operand scale for the ordinary equality gate. -/
example : (elaborateNumericComparison model ["Order"]
    (twoSided .equal
      (AuthoredNumericExpr.extremumList .minimum (atom "U") [atom "Scale2"])
      (atom "Scale2"))).isOk = true := by
  native_decide

/- The checked root remains deliberately narrower than general wrapper traversal in either direction. -/
example : errorOf
    (comparison .less
      (.binary .add
        (AuthoredNumericExpr.extremumList .minimum (atom "U") [atom "V"])
        (literal 1 0))
      0) = some .unsupportedExpression := by
  native_decide

example : errorOf
    (comparison .less
      (AuthoredNumericExpr.extremumList .minimum
        (.binary .add (atom "U") (literal 1 0))
        [atom "V"])
      0) = some .unsupportedExpression := by
  native_decide

example : errorOf
    (comparison .less
      (AuthoredNumericExpr.extremumList .minimum (atom "U") [literal 1 0])
      0) = some .unsupportedExpression := by
  native_decide

example : errorOf
    (comparison .less
      (.extremum .minimum
        (.extremum .maximum (atom "U") (atom "V"))
        (atom "S"))
      0) = some .unsupportedExpression := by
  native_decide

example : errorOf (comparison .equal (literal 0 0) 0) =
    some .constantExpression := by
  native_decide

example : errorOf (comparison .equal (atom "Flag") 0) =
    some (.fieldNotNumber ["Order", "Flag"]) := by
  native_decide

example : errorOf (twoSided .equal (atom "U") (atom "Flag")) =
    some (.fieldNotNumber ["Order", "Flag"]) := by
  native_decide

example : errorOf
    (comparison .equal (.atom (path ["Order", "Items"] "Item")) 0) =
      some (.resolve (.repeatableReference ["Order", "Items", "Item"])) := by
  native_decide

example : errorOf
    (comparison .equal (.atom (path ["Reference"] "Other")) 0) =
      some (.fieldOutsideRowGroup ["Reference", "Other"] ["Order"]) := by
  native_decide

end A12Kernel.Conformance.NumericValidation
