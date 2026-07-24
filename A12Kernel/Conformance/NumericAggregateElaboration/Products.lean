import A12Kernel.Conformance.NumericAggregateElaboration.Support

/-! # Checked row-paired product aggregate locks -/

namespace A12Kernel.Conformance.NumericAggregateElaboration.Products

open A12Kernel
open A12Kernel.Conformance.NumericAggregateElaboration.Support

/- The dedicated pair admits exactly two same-group Number stars, permits the same wildcarded field twice as the A12 checker does, and rejects a different group or wrong kind. -/
example :
    productErrorOf aggregateStar aggregateStar = none ∧
      productErrorOf (productStar "Amount") (productStar "Price") = none ∧
      productErrorOf (productStar "Amount") (productStar "Amount" "Other") =
        some (.differentGroups ["Form", "Rows"] ["Form", "Other"]) ∧
      productErrorOf (productStar "Amount") (productStar "Label") =
        some (.source (.fieldNotNumber repeatedText.path)) := by
  native_decide

/- Only the lowest repeatable level may be starred. A named outer row plus an inner star remains legal. -/
example :
    productErrorOf (nestedProductStar true) (nestedProductStar true) =
        some (.wildcardNotLowest nestedRepeated.path) ∧
      productErrorOf (nestedProductStar false) (nestedProductStar false) = none := by
  native_decide

/- Both fields are read from each shared canonical environment: 2·3 + 4·5 is 26, not a cross-paired 22. -/
example :
    productValidationOf [1, 2, 3]
      (cells3 (.parsed (.num 2)) (.parsed (.num 4)) (.parsed (.num 0)))
      (cells3 (.parsed (.num 3)) (.parsed (.num 5)) (.parsed (.num 0))) =
        some (.value 26 .fixed) := by
  native_decide

/- Multiplication and addition are staged at precision 50 in canonical row order. -/
example :
    productValidationOf [1, 2, 3]
      (cells3 (.parsed (.num tenPow50)) (.parsed (.num (-tenPow50)))
        (.parsed (.num (3 / 5))))
      (cells3 (.parsed (.num 1)) (.parsed (.num 1)) (.parsed (.num 1))) =
        some (.value (3 / 5) .fixed) := by
  native_decide

/- Each row product is rounded before entering the running sum; exact rational multiplication would retain the final `3 / 5`. -/
example :
    productValidationOf [1, 2, 3]
      (cells3 (.parsed (.num (tenPow50 - 1))) (.parsed (.num 0))
        (.parsed (.num 0)))
      (cells3 (.parsed (.num (3 / 5))) (.parsed (.num 0))
        (.parsed (.num 0))) =
        some (.value (tenPow50 * 3 / 5 - 1) .fixed) := by
  native_decide

/- Empty cells substitute zero but retain declaration-owned arithmetic directions; any omitted declared row makes the successful fold both-directionally fillable. -/
example :
    productValidationOf [1, 2, 3]
      (cells3 (.parsed (.num 2)) (.parsed (.num 10)) (.parsed (.num 0)))
      (cells3 (.parsed (.num 3)) .presentEmpty (.parsed (.num 0))) =
        some (.value 6 .both) ∧
      productValidationOf [1, 2, 3]
        (cells3 (.parsed (.num 2)) .presentEmpty (.parsed (.num 0)))
        (cells3 (.parsed (.num 3)) (.parsed (.num 5)) (.parsed (.num 0))) =
          some (.value 6 .growOnly) ∧
      productValidationOf [1, 2]
        (cells3 (.parsed (.num 2)) (.parsed (.num 4)) .empty)
        (cells3 (.parsed (.num 3)) (.parsed (.num 5)) .empty) =
          some (.value 26 .both) := by
  native_decide

/- The first unavailable reached cell owns suppression, with left-before-right order inside each pair. -/
example :
    productValidationOf [1]
      (cells3 (.rejected .declaredConstraint) .empty .empty)
      (cells3 (.rejected .malformed) .empty .empty) =
        some (.unknown .declaredConstraint) := by
  native_decide

/- Phase-sensitive reads share the fold: required-only emptiness suppresses validation but computes as zero, while ordinary formal invalidity poisons computation. -/
example :
    let zeros := cells3 (.parsed (.num 0)) (.parsed (.num 0)) (.parsed (.num 0))
    productCheckedValidationOf [1, 2, 3]
        (cells3 .presentEmpty (.parsed (.num 0)) (.parsed (.num 0)))
        (cells3 (.parsed (.num 5)) (.parsed (.num 0)) (.parsed (.num 0)))
        (requiredLeft := true) =
          some (.unknown .required) ∧
      productComputationOf [1, 2, 3]
        (cells3 .presentEmpty (.parsed (.num 0)) (.parsed (.num 0)))
        (cells3 (.parsed (.num 5)) (.parsed (.num 0)) (.parsed (.num 0)))
        (requiredLeft := true) =
          some (.value 0) ∧
      productComputationOf [1, 2, 3]
        (cells3 (.rejected .declaredConstraint) (.parsed (.num 0)) (.parsed (.num 0)))
        zeros = some (.poison .declaredConstraint) := by
  native_decide

/- Partial validation needs wildcard/ancestor extent coverage for both declarations; enumerating every current row or wildcarding only one field is insufficient. -/
example :
    let left := cells3 (.parsed (.num 2)) (.parsed (.num 4)) (.parsed (.num 0))
    let right := cells3 (.parsed (.num 3)) (.parsed (.num 5)) (.parsed (.num 0))
    let concreteAll := ValidationRelevanceScope.partialSet [
      productRelevance repeated.path [.concrete 1, .concrete 1, .concrete 1],
      productRelevance repeated.path [.concrete 1, .concrete 2, .concrete 1],
      productRelevance repeated.path [.concrete 1, .concrete 3, .concrete 1],
      productRelevance repeatedPrice.path [.concrete 1, .concrete 1, .concrete 1],
      productRelevance repeatedPrice.path [.concrete 1, .concrete 2, .concrete 1],
      productRelevance repeatedPrice.path [.concrete 1, .concrete 3, .concrete 1]]
    let leftOnly := ValidationRelevanceScope.partialSet [
      productRelevance repeated.path [.concrete 1, .all, .concrete 1]]
    let both := ValidationRelevanceScope.partialSet [
      productRelevance repeated.path [.concrete 1, .all, .concrete 1],
      productRelevance repeatedPrice.path [.concrete 1, .all, .concrete 1]]
    productPartialOf [1, 2, 3] left right concreteAll = some .nonRelevant ∧
      productPartialOf [1, 2, 3] left right leftOnly = some .nonRelevant ∧
      productPartialOf [1, 2, 3] left right both =
        some (.evaluated (.value 26 .fixed)) ∧
      productPartialOf [1, 2, 3] left right
        (.partialSet [productRelevance ["Form"] [.concrete 1]]) =
          some (.evaluated (.value 26 .fixed)) := by
  native_decide

/- Result scale is the exact sum of both field scales and never gains literal expansion capability. -/
example : productScale = some { scale := .exact 2, canExpandScale := false } := by
  native_decide


end A12Kernel.Conformance.NumericAggregateElaboration.Products
