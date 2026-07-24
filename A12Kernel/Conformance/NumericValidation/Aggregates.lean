import A12Kernel.Conformance.NumericValidation.Support

/-! # Checked numeric-validation aggregates locks -/

namespace A12Kernel.Conformance.NumericValidation.Aggregates

open A12Kernel
open A12Kernel.Conformance.NumericValidation.Support

/- Direct field-list aggregates are ordinary numeric-expression atoms: arithmetic and comparison polarity reuse the existing expression and aggregate evaluators. -/
example : verdictOf
    (comparison .greater
      (.binary .add (aggregate .sum "U" ["V"]) (literal 1 0)) 10)
    (raw (.parsed (.num 4)) (.parsed (.num 6))) =
      some (.fired .value) := by
  native_decide

example :
    verdictOf (comparison .less (aggregate .sum "U" ["V"]) 10)
        (raw (.parsed (.num 4))) = some (.fired .omission) ∧
      verdictOf (comparison .less (aggregate .sum "U" ["V"]) 1) =
        some (.fired .omission) ∧
      verdictOf (comparison .greater (aggregate .minimum "U" ["V"]) 10)
        (raw (.parsed (.num 20))) = some (.fired .omission) ∧
      verdictOf (comparison .less (aggregate .minimum "U" ["V"]) 10)
        (raw (.parsed (.num 20))) = some .notFired ∧
      verdictOf (comparison .greater (aggregate .maximum "U" ["V"]) 10)
        (raw (.parsed (.num 20)) (.rejected .declaredConstraint)) =
        some .unknown := by
  native_decide

/- Aggregate scale is the maximum declaration scale, without literal expansion capability. -/
example :
    (elaborateNumericComparison model ["Order"]
      (twoSided .equal (aggregate .sum "U" ["Scale2"])
        (atom "Scale2"))).isOk = true ∧
      errorOf (twoSided .equal (aggregate .sum "U" ["Scale2"])
        (atom "U")) = some (.exactScaleMismatch
          (NumericScaleSummary.field 2) (NumericScaleSummary.field 0)) := by
  native_decide

/- Direct aggregate `Abs` applies after the shared fold: a negative total changes sign, all-empty bidirectional zero becomes grow-only magnitude, formal failure stays unknown, and the aggregate scale is retained. -/
example :
    verdictOf (comparison .equal (.abs (aggregate .sum "S" ["U"])) 3)
        (raw (.parsed (.num 2)) .empty (.parsed (.num (-5)))) =
      some (.fired .value) ∧
    verdictOf (comparison .less (.abs (aggregate .sum "S" ["U"])) 10) =
      some (.fired .omission) ∧
    verdictOf (comparison .greater (.abs (aggregate .sum "S" ["U"])) (-10)) =
      some (.fired .value) ∧
    verdictOf (comparison .equal (.abs (aggregate .sum "S" ["U"])) 0)
        (raw (.rejected .declaredConstraint)) = some .unknown ∧
    verdictOf (comparison .equal (.abs (aggregate .minimum "S" ["U"])) 5)
        (raw (.parsed (.num 2)) .empty (.parsed (.num (-5)))) =
      some (.fired .value) ∧
    verdictOf (comparison .equal (.abs (aggregate .maximum "S" ["U"])) 2)
        (raw (.parsed (.num 2)) .empty (.parsed (.num (-5)))) =
      some (.fired .value) ∧
    verdictOf (comparison .equal
        (.abs (aggregate .distinctCount "U" ["V"])) 1)
        (raw (.parsed (.num 5)) (.parsed (.num 5))) = some (.fired .value) ∧
    verdictOf (comparison .less
        (.abs (aggregate .distinctCount "U" ["V"])) 1) =
      some (.fired .omission) ∧
    verdictOf (comparison .greater
        (.abs (aggregate .distinctCount "U" ["V"])) (-1)) =
      some (.fired .value) ∧
    (elaborateNumericComparison model ["Order"]
      (twoSided .equal (.abs (aggregate .sum "U" ["Scale2"]))
        (atom "Scale2"))).isOk = true := by
  native_decide

/- NumberOfDifferentValues is an integral aggregate independently of operand declarations, and its grow-only missing state reaches ordinary comparison polarity. -/
example :
    errorOf (twoSided .equal
      (aggregate .distinctCount "U" ["Scale2"]) (atom "U")) = none ∧
    verdictOf (comparison .equal
      (aggregate .distinctCount "U" ["V"]) 1)
      (raw (.parsed (.num 5)) (.parsed (.num 5))) =
        some (.fired .value) ∧
    verdictOf (comparison .less
      (aggregate .distinctCount "U" ["V"]) 1) =
        some (.fired .omission) := by
  native_decide

/- The aggregate owner retains wrong-kind and repeatable-source diagnostics rather than collapsing them into a generic expression rejection. -/
example :
    errorOf (comparison .greater (aggregate .sum "U" ["Flag"]) 0) =
        some (.aggregate (.fieldKindMismatch ["Order", "Flag"] .boolean)) := by
  native_decide

example :
    errorOf (comparison .greater
      (.atom (.aggregate .sum {
        first := path ["Order"] "U"
        rest := [path ["Reference"] "Other"] })) 0) =
      some (.fieldOutsideRowGroup ["Reference", "Other"] ["Order"]) := by
  native_decide

example :
    errorOf (comparison .greater
      (.atom (.aggregate .sum {
        first := path ["Order"] "U"
        rest := [path ["Order", "Items"] "Item"] })) 0) =
      some (.aggregate (.resolve (.repeatableReference
        ["Order", "Items", "Item"]))) := by
  native_decide

private def aggregateTraversal : Option (Bool × Bool × Bool × Bool) := do
  let checked ← (elaborateNumericComparison model ["Order"]
    (comparison .greater (aggregate .sum "U" ["V"]) 0)).toOption
  pure (checked.core.referencesField model 0,
    checked.core.referencesField model 1,
    checked.core.allRelevant (fun field => field == 0),
    checked.core.allRelevant (fun field => field == 0 || field == 1))

example : aggregateTraversal = some (true, true, false, true) := by
  native_decide


end A12Kernel.Conformance.NumericValidation.Aggregates
