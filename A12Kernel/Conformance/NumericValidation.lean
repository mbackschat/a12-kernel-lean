import A12Kernel.Elaboration.NumericValidation

/-! # Checked numeric-validation integration locks -/

namespace A12Kernel.Conformance.NumericValidation

open A12Kernel

private def unsigned : NumField := { scale := 0, signed := false }
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
        policy := { kind := .number unsigned }, repeatableScope := [10] }],
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
  { op, left, right := literal rightValue rightScale }

private def twoSided (op : NumericComparisonOp)
    (left right : AuthoredNumericExpr SurfaceFieldPath) :
    SurfaceNumericComparison :=
  { op, left, right }

private def raw (u v : RawCell := .empty) : RawFlatContext where
  read id := if id == 0 then u else if id == 1 then v else .empty

private def verdictOf (surface : SurfaceNumericComparison)
    (context : RawFlatContext := raw) (hasContent : Bool := true) : Option Verdict :=
  (elaborateAndEvalNumericComparison model ["Order"] context hasContent surface).toOption

private def errorOf (surface : SurfaceNumericComparison) :
    Option NumericValidationElabError :=
  match elaborateNumericComparison model ["Order"] surface with
  | .ok _ => none
  | .error error => some error

private def dividedThird : AuthoredNumericExpr SurfaceFieldPath :=
  .group (.binary .divide (literal 3 0) (literal 3 0))

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

example : errorOf (comparison .less (.power (atom "U") (literal 2 0)) 0) =
    some .unsupportedExpression := by
  native_decide

example : errorOf
    (comparison .less (.round .halfUp omittedRoundingPlaces (atom "U")) 0) =
      some .unsupportedExpression := by
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
