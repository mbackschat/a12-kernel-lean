import A12Kernel.Semantics.NumericTolerance

/-! # Fixed numeric-tolerance separating cases -/

namespace A12Kernel.Conformance.NumericTolerance

open A12Kernel

example : NumericToleranceRange.range1.threshold = 1 := by
  rfl

example : NumericToleranceRange.range2.threshold = 2 := by
  rfl

example : NumericToleranceRange.range5.threshold = 5 := by
  rfl

example : NumericToleranceRange.range10.threshold = 10 := by
  rfl

/- Every band is strict: its exact endpoint remains inside the tolerance. -/
example : NumericToleranceRange.range1.eval
    (.value 0 .fixed) (.value 1 .fixed) = .notFired := by
  native_decide

example : NumericToleranceRange.range2.eval
    (.value 0 .fixed) (.value 2 .fixed) = .notFired := by
  native_decide

example : NumericToleranceRange.range5.eval
    (.value 0 .fixed) (.value 5 .fixed) = .notFired := by
  native_decide

example : NumericToleranceRange.range10.eval
    (.value 0 .fixed) (.value 10 .fixed) = .notFired := by
  native_decide

example : NumericToleranceRange.range1.eval
    (.value 0 .fixed) (.value 2 .fixed) = .fired .value := by
  native_decide

example : NumericToleranceRange.range2.eval
    (.value 0 .fixed) (.value 3 .fixed) = .fired .value := by
  native_decide

example : NumericToleranceRange.range5.eval
    (.value 0 .fixed) (.value 6 .fixed) = .fired .value := by
  native_decide

example : NumericToleranceRange.range10.eval
    (.value 0 .fixed) (.value 11 .fixed) = .fired .value := by
  native_decide

private def belowPositiveHalfUlp : Rat := 49 / ((10 : Rat) ^ 21)
private def atPositiveHalfUlp : Rat := 1 + 5 / ((10 : Rat) ^ 20)

/- Both operands are normalized independently at scale 19 before the strict band check. -/
example : NumericToleranceRange.range1.eval
    (.value (1 + belowPositiveHalfUlp) .fixed)
      (.value (-belowPositiveHalfUlp) .fixed) = .notFired := by
  native_decide

example : NumericToleranceRange.range1.eval
    (.value 0 .fixed) (.value atPositiveHalfUlp .fixed) = .fired .value := by
  native_decide

example : ((1 + belowPositiveHalfUlp) - (-belowPositiveHalfUlp)).abs > 1 := by
  native_decide

example :
    normalizedComparisonValue
      (((1 + belowPositiveHalfUlp) - (-belowPositiveHalfUlp)).abs) > 1 := by
  native_decide

/- Truth and fixed polarity are symmetric. -/
example : NumericToleranceRange.range2.eval
    (.value 3 .fixed) (.value 0 .fixed) =
      NumericToleranceRange.range2.eval (.value 0 .fixed) (.value 3 .fixed) := by
  native_decide

/- Tolerance reuses directional inequality polarity rather than treating every movement as repairing. -/
example : NumericToleranceRange.range1.eval
    (.value 0 (.emptyNumber false)) (.value (-5) .fixed) = .fired .value := by
  native_decide

example : NumericToleranceRange.range1.eval
    (.value 0 (.emptyNumber true)) (.value (-5) .fixed) = .fired .omission := by
  native_decide

example : NumericToleranceRange.range1.eval
    (.value 0 (.emptyNumber false)) (.value 5 .fixed) = .fired .omission := by
  native_decide

example : NumericToleranceRange.range1.eval
    (.value (-5) .fixed) (.value 0 (.emptyNumber false)) = .fired .value := by
  native_decide

example : NumericToleranceRange.range1.eval
    (.value (-5) .fixed) (.value 0 (.emptyNumber true)) = .fired .omission := by
  native_decide

example : NumericToleranceRange.range1.eval
    (.value 5 .fixed) (.value 0 (.emptyNumber false)) = .fired .omission := by
  native_decide

example : NumericToleranceRange.range1.eval
    (.value 0 (.emptyNumber false)) (.value 1 .fixed) = .notFired := by
  native_decide

example : NumericToleranceRange.range1.eval
    (.value 0 (.emptyNumber false)) (.value 0 (.emptyNumber true)) = .notFired := by
  native_decide

example : NumericToleranceRange.range1.eval
    (.unknown .malformed) (.value 5 .fixed) = .unknown := by
  native_decide

example : NumericToleranceRange.range1.eval
    (.value 5 .fixed) (.unknown .declaredConstraint) = .unknown := by
  native_decide

end A12Kernel.Conformance.NumericTolerance
