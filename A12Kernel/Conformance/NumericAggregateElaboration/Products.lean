import A12Kernel.Conformance.NumericAggregateElaboration.Support

/-! # Checked row-paired product aggregate locks -/

namespace A12Kernel.Conformance.NumericAggregateElaboration.Products

open A12Kernel
open A12Kernel.Conformance.NumericAggregateElaboration.Support

private def plainProductPath (groups : List String) (field : String) :
    SurfaceStarFieldPath :=
  { base := .absolute
    groups := groups.map fun name => { name }
    field }

private def outerOnlyNestedProductStar : SurfaceStarFieldPath :=
  { base := .absolute
    groups := [
      { name := "Form" },
      { name := "Rows", starred := true },
      { name := "Details" }]
    field := "Amount" }

private def productHaving : SurfaceCorrelatedHaving :=
  .compareNumbers .equal
    { origin := .inner, field := absolute ["Form", "Rows"] "FilterLeft" }
    { origin := .inner, field := absolute ["Form", "Rows"] "FilterRight" }

private def productDiagnosticCode? (left right : SurfaceStarFieldPath)
    (declaringGroup : GroupPath := ["Form"])
    (leftHaving : Option SurfaceCorrelatedHaving := none)
    (rightHaving : Option SurfaceCorrelatedHaving := none) : Option String :=
  match elaborateNumericProductAggregate productModel declaringGroup {
      left, right, leftHaving, rightHaving } with
  | .ok _ => none
  | .error error => error.diagnostic?.map KernelStaticDiagnostic.kernelCode

private inductive ProductAuthoringView where
  | accepted
  | refused (diagnostic : Option String)
  deriving Repr, DecidableEq

private def productAuthoringView (left right : SurfaceStarFieldPath) :
    ProductAuthoringView :=
  match elaborateNumericProductAggregate productModel ["Form"] { left, right } with
  | .ok _ => .accepted
  | .error error =>
      .refused (error.diagnostic?.map KernelStaticDiagnostic.kernelCode)

/- The `Having` refusal controls use an independently admissible same-scale row filter. -/
example :
    (elaborateStarNumberHavingSource productModel ["Form"] aggregateStar
      productHaving).isOk = true := by
  native_decide

/- The dedicated pair admits exactly two Number stars from one owning group, permits the same wildcarded field twice as the A12 checker does, and rejects a different owning group or wrong kind. -/
example :
    productErrorOf aggregateStar aggregateStar = none ∧
      productErrorOf (productStar "Amount") (productStar "Price") = none ∧
      productErrorOf (productStar "Amount") (productStar "Amount" "Other") =
        some (.differentGroups ["Form", "Rows"] ["Form", "Other"]) ∧
      productErrorOf (productStar "Amount") (productStar "Label") =
        some (.source (.fieldNotNumber repeatedText.path)) := by
  native_decide

/- The pair gate reads the fields' immediate owning groups, not merely their common starred ancestor.
That owning group may itself be fixed as long as each path crosses the same repeatable level. -/
example :
    productErrorOf packagedWeightStar packagedWeightStar = none ∧
      productErrorOf aggregateStar packagedWeightStar =
        some (.differentGroups ["Form", "Rows"]
          ["Form", "Rows", "Packaging"]) := by
  native_decide

/- Only the lowest repeatable level may be starred. An inner-only star also requires its outer row to be bound by the declaring scope. -/
example :
    productErrorOf (nestedProductStar true) (nestedProductStar true) =
        some (.wildcardOnlyAtLowestLevel nestedRepeated.path) ∧
      productErrorOf (nestedProductStar false) (nestedProductStar false) =
        some (.noWildcard nestedRepeated.path) := by
  native_decide

/- The public error plus optional diagnostic projection gives Explain and Transform three distinct
answers: admitted, mapped refusal, and insufficient information for an unmeasured refusal. -/
example :
    productAuthoringView aggregateStar (productStar "Price") = .accepted ∧
      productAuthoringView aggregateStar
          (plainProductPath ["Form", "Rows"] "Price") =
        .refused (some "MVK_NO_WILDCARD") ∧
      productAuthoringView aggregateStar (productStar "Label") =
        .refused none := by
  native_decide

/- The measured static matrix distinguishes each authored wildcard shape before any runtime
topology exists, including the root rule's missing outer binding. The final bound-outer positive is
an internal scope-certificate control and carries no separate Kernel-correspondence claim. -/
example :
    productDiagnosticCode? aggregateStar (productStar "Amount" "Other") =
        some "MVK_DIFFERENT_GROUPS" ∧
      productDiagnosticCode? aggregateStar packagedWeightStar =
        some "MVK_DIFFERENT_GROUPS" ∧
      productDiagnosticCode? aggregateStar
          (plainProductPath ["Form"] "UnsignedA") =
        some "MVK_DIFFERENT_GROUPS" ∧
      productDiagnosticCode? aggregateStar
          (plainProductPath ["Form", "Rows"] "Price") =
        some "MVK_NO_WILDCARD" ∧
      productDiagnosticCode? aggregateStar (nestedProductStar false) =
        some "MVK_NO_WILDCARD" ∧
      productDiagnosticCode? outerOnlyNestedProductStar
          outerOnlyNestedProductStar = some "MVK_NO_WILDCARD" ∧
      productDiagnosticCode? (nestedProductStar true) (nestedProductStar true) =
        some "MVK_WILDCARD_ONLY_AT_LOWEST_LEVEL_ALLOWED" ∧
      productDiagnosticCode?
          (plainProductPath ["Form"] "UnsignedA")
          (plainProductPath ["Form"] "SignedB") =
        some "MVK_REPEATABLE_LEVEL_REQUIRED" ∧
      productDiagnosticCode? aggregateStar (productStar "Price")
          (leftHaving := some productHaving) =
        some "MVK_WILDCARD_AT_LOWEST_LEVEL_REQUIRED" ∧
      productDiagnosticCode? aggregateStar (productStar "Price")
          (rightHaving := some productHaving) =
        some "MVK_WILDCARD_AT_LOWEST_LEVEL_REQUIRED" ∧
      productDiagnosticCode? aggregateStar (productStar "Price") = none ∧
      productDiagnosticCode? packagedWeightStar packagedWeightStar = none ∧
      productDiagnosticCode? (nestedProductStar false) (nestedProductStar false)
          ["Form", "Rows"] = none := by
  native_decide

/- The five external classes remain independently enumerable rather than collapsing static
refusals into one generic authoring failure. -/
example :
    KernelStaticDiagnostic.differentGroups.kernelCode =
        "MVK_DIFFERENT_GROUPS" ∧
      KernelStaticDiagnostic.noWildcard.kernelCode = "MVK_NO_WILDCARD" ∧
      KernelStaticDiagnostic.wildcardOnlyAtLowestLevelAllowed.kernelCode =
        "MVK_WILDCARD_ONLY_AT_LOWEST_LEVEL_ALLOWED" ∧
      KernelStaticDiagnostic.wildcardAtLowestLevelRequired.kernelCode =
        "MVK_WILDCARD_AT_LOWEST_LEVEL_REQUIRED" ∧
      KernelStaticDiagnostic.repeatableLevelRequired.kernelCode =
        "MVK_REPEATABLE_LEVEL_REQUIRED" := by
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

/- `SumOfProducts` is **not** an all-rows aggregate for partial relevance: it reaches neither the Kernel's shared combiner nor that combiner's pre-loop whole-repetition survey, so enumerating every concrete row evaluates it where `Sum`/`MaxValue`/`MinValue`/`NumberOfDifferentValues` stay UNKNOWN. Measured per operator against the Kernel at a12-dmkits `6fe8d501`/`12491e4f`, with a wildcard positive control proving a silent concrete row is a relevance decision rather than an operator that never fires. Covering only one of the two declarations remains insufficient, which is the case that separates per-cell relevance from no relevance gate at all. -/
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
    productPartialOf [1, 2, 3] left right concreteAll =
        some (.evaluated (.value 26 .fixed)) ∧
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
