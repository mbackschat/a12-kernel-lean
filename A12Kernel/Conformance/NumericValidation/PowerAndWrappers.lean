import A12Kernel.Conformance.NumericValidation.Support

/-! # Checked numeric-validation power and wrappers locks -/

namespace A12Kernel.Conformance.NumericValidation.PowerAndWrappers

open A12Kernel
open A12Kernel.Conformance.NumericValidation.Support

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

/- A source-confirmed rounding operation is admitted through the shared complete numeric-operation route. -/
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

/- Enclosing arithmetic accepts a checked unary wrapper and continues to preserve its directional result. -/
example : verdictOf
    (comparison .less
      (.binary .add
        (.round .halfUp omittedRoundingPlaces (atom "U"))
        (literal 1 0))
      100) = some (.fired .omission) := by
  native_decide

/- A root operation-form rounding wrapper accepts an already-checked plain arithmetic body and preserves its directional fillability. -/
example : verdictOf
    (comparison .less
      (.round .halfUp omittedRoundingPlaces
        (.binary .add (atom "U") (literal 1 0)))
      100) = some (.fired .omission) := by
  native_decide

example : verdictOf
    (comparison .greater
      (.round .halfUp omittedRoundingPlaces
        (.binary .add (atom "U") (literal 1 0)))
      (-100)) = some (.fired .value) := by
  native_decide

/- Each grouped division is checked in its own region, and rounding applies the scale-19 pre-round before flooring the near-one sum. -/
example :
    let third := .group (.binary .divide (atom "U") (literal 3 0))
    verdictOf
      (comparison .equal
        (.round .floor omittedRoundingPlaces
          (.binary .add (.binary .add third third) third))
        1)
      (raw (.parsed (.num 1))) = some (.fired .value) := by
  native_decide

/- A grouped field is still nonconstant, while a grouped literal is the same immediate constant rejected by the wrapper checker. -/
example : verdictOf
    (comparison .equal
      (.round .halfUp omittedRoundingPlaces (.group (atom "U"))) 2)
    (raw (.parsed (.num 2))) = some (.fired .value) := by
  native_decide

example : errorOf
    (twoSided .equal
      (.round .halfUp omittedRoundingPlaces (.group (literal 1 0)))
      (atom "U")) = some .unsupportedExpression := by
  native_decide

/- Enclosing arithmetic does not let a wrapper evade the immediate-literal gate. Nested wrappers remain ordered transformations, and a checked operand-list extremum is another nonliteral numeric child. -/
example :
    errorOf
        (comparison .less
          (.binary .add
            (.round .halfUp omittedRoundingPlaces (literal 1 0))
            (atom "U"))
          0) = some .unsupportedExpression ∧
      verdictOf
        (comparison .equal
          (.round .floor omittedRoundingPlaces (.abs (atom "S")))
          1)
        (raw .empty .empty (.parsed (.num ((-14 : Rat) / 10)))) =
          some (.fired .value) ∧
      verdictOf
        (comparison .equal
          (.abs (.round .floor omittedRoundingPlaces (atom "S")))
          2)
        (raw .empty .empty (.parsed (.num ((-14 : Rat) / 10)))) =
          some (.fired .value) ∧
      verdictOf
        (comparison .equal
          (.binary .add
            (.round .halfUp omittedRoundingPlaces
              (AuthoredNumericExpr.extremumList .minimum
                (atom "U") [atom "V"]))
            (literal 1 0))
          3)
        (raw (.parsed (.num 2)) (.parsed (.num 4))) =
          some (.fired .value) := by
  native_decide

/- The wrapper opens no exemption for an illegal division region inside its body. -/
example : errorOf
    (comparison .less
      (.round .halfUp omittedRoundingPlaces
        (.binary .multiply
          (.binary .divide (atom "U") (atom "V"))
          (.binary .divide (atom "S") (atom "Scale2"))))
      0) = some (.authoring .tooManyDivisions) := by
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

example : verdictOf
    (comparison .less
      (.binary .add (.abs (atom "U")) (literal 1 0))
      100) = some (.fired .omission) := by
  native_decide

example : verdictOf
    (comparison .less
      (.abs (.binary .subtract (atom "U") (atom "S")))
      100) = some (.fired .omission) := by
  native_decide

example : verdictOf
    (comparison .greater
      (.abs (.binary .subtract (atom "U") (atom "S")))
      (-100)) = some (.fired .value) := by
  native_decide

/- A wrapper body division contributes to the enclosing multiplication/division region, while an addition inside the wrapper resets that contribution. -/
example : errorOf
    (comparison .less
      (.binary .divide
        (.binary .multiply
          (.round .halfUp omittedRoundingPlaces
            (.binary .divide (atom "U") (atom "V")))
          (atom "S"))
        (atom "Scale2"))
      0) = some (.authoring .tooManyDivisions) := by
  native_decide

example : verdictOf
    (suppressScaleWarning
      (comparison .equal
        (.binary .divide
          (.binary .multiply
            (.round .halfUp omittedRoundingPlaces
              (.binary .add (atom "U") (literal 1 0)))
            (atom "V"))
          (atom "Scale2"))
        3))
    (raw (.parsed (.num 2)) (.parsed (.num 3)) .empty
      (.parsed (.num 3))) = some (.fired .value) := by
  native_decide

/- The wrapper is a structural power separator, but its body still undergoes the ordinary direct-left power check. -/
example : verdictOf
    (comparison .equal
      (.power
        (.round .halfUp omittedRoundingPlaces
          (.power (atom "U") (literal 2 0)))
        (literal 2 0))
      16)
    (raw (.parsed (.num 2))) = some (.fired .value) := by
  native_decide

example : errorOf
    (comparison .less
      (.binary .add
        (.abs (.power (.power (atom "U") (literal 2 0)) (literal 3 0)))
        (literal 1 0))
      100) = some (.authoring .directLeftNestedPower) := by
  native_decide


end A12Kernel.Conformance.NumericValidation.PowerAndWrappers
