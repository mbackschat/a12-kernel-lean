import A12Kernel.Conformance.NumericValidation.Support

/-! # Checked numeric-validation extrema locks -/

namespace A12Kernel.Conformance.NumericValidation.Extrema

open A12Kernel
open A12Kernel.Conformance.NumericValidation.Support

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

/- An admitted operand-list call composes with surrounding arithmetic, and every list member may itself be an admitted numeric operation. -/
example : errorOf
    (comparison .less
      (.binary .add
        (AuthoredNumericExpr.extremumList .minimum (atom "U") [atom "V"])
        (literal 1 0))
      0) = none := by
  native_decide

example : errorOf
    (comparison .less
      (AuthoredNumericExpr.extremumList .minimum
        (.binary .add (atom "U") (literal 1 0))
        [atom "V"])
      0) = none := by
  native_decide

/- One direct top-level constant may occur at any position in the canonical operand list. -/
example : verdictOf
    (comparison .less
      (AuthoredNumericExpr.extremumList .minimum (literal 5 0) [atom "U"])
      10) = some (.fired .omission) := by
  native_decide

example : verdictOf
    (comparison .greater
      (AuthoredNumericExpr.extremumList .maximum
        (atom "U") [literal 5 0, atom "V"])
      4)
    (raw .empty (.parsed (.num 4))) = some (.fired .value) := by
  native_decide

/- The constant participates in the ordinary static summary without making the field-bearing fold a constant expression. -/
example : (elaborateNumericComparison model ["Order"]
    (twoSided .equal
      (AuthoredNumericExpr.extremumList .minimum
        (atom "U") [literal 0 2])
      (atom "Scale2"))).isOk = true := by
  native_decide

/- Two direct constants in one operand-list call remain illegal. A nested call gets its own constant budget, and grouping does not hide or forbid one literal. -/
example : errorOf
    (comparison .less
      (AuthoredNumericExpr.extremumList .minimum
        (atom "U") [literal 1 0, literal 2 0])
      0) = some .unsupportedExpression := by
  native_decide

example : verdictOf
    (comparison .less
      (AuthoredNumericExpr.extremumList .minimum
        (atom "U") [.group (literal 1 0)])
      2)
    (raw (.parsed (.num 5))) = some (.fired .value) := by
  native_decide

example : verdictOf
    (comparison .less
      (AuthoredNumericExpr.extremumList .minimum
        (AuthoredNumericExpr.extremumList .minimum
          (atom "U") [literal 1 0])
        [literal 2 0])
      2)
    (raw (.parsed (.num 5))) = some (.fired .value) := by
  native_decide

/- Each operand is a complete numeric operation. A literal nested inside arithmetic is not a direct list constant. -/
example : verdictOf
    (comparison .less
      (AuthoredNumericExpr.extremumList .minimum
        (.binary .add (atom "U") (literal 1 0))
        [literal 2 0])
      3)
    (raw (.parsed (.num 5))) = some (.fired .value) := by
  native_decide

example : verdictOf
    (comparison .less
      (.binary .add
        (AuthoredNumericExpr.extremumList .minimum
          (atom "U") [literal 2 0])
        (literal 1 0))
      4)
    (raw (.parsed (.num 5))) = some (.fired .value) := by
  native_decide

example : verdictOf
    (comparison .less
      (AuthoredNumericExpr.extremumList .minimum
        (.abs (atom "U")) [literal 2 0])
      3)
    (raw (.parsed (.num 5))) = some (.fired .value) := by
  native_decide

example : verdictOf
    (comparison .less
      (AuthoredNumericExpr.extremumList .minimum
        (AuthoredNumericExpr.extremumList .maximum
          (atom "U") [literal 1 0])
        [literal 2 0])
      3)
    (raw (.parsed (.num 5))) = some (.fired .value) := by
  native_decide

example : errorOf
    (comparison .less
      (.extremum .minimum (atom "U")
        (.extremum .minimum (atom "V") (literal 1 0)))
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


end A12Kernel.Conformance.NumericValidation.Extrema
