import A12Kernel.Reference.Dm.Validate
import A12Kernel.Reference.Dm.Compute

/-! # `SumOfTerms` admission through the reader

Every admission row of the iteration entity and of the term, through `checkRule` for a rule and
`lowerComputation` for a computation, each answering the Kernel class it draws or `ADMITTED`
([spec/07 §3.10](../../../spec/07-repetition-and-iteration.md#310-sumofterms)). The models are
this project's own insurance-claims domain, rebuilt from the peer's two model drafts; their runtime
rows are in [`SumOfTermsRuntimeLocks`](SumOfTermsRuntimeLocks.lean).
-/

namespace A12Kernel.Dm.SumOfTermsLocks

private def number (scale : Nat) : FieldKind := .number { scale, signed := true }

/-- `SumOfTermsIterationEntityLawsTest`'s policy: one repeatable claim list holding two numbers. -/
private def entityModel : FlatModel := {
  fields := [
    { id := 1, name := "Holder", groupPath := ["Policy"], policy := { kind := .string } },
    { id := 2, name := "Amount", groupPath := ["Policy", "Claims"], repeatableScope := [10], policy := { kind := number 0 } },
    { id := 3, name := "Reserve", groupPath := ["Policy", "Claims"], repeatableScope := [10], policy := { kind := number 0 } }]
  repeatableGroups := [{ level := 10, path := ["Policy", "Claims"], repeatability := some 3 }] }

/-- `ModelDrafts.policyClaims`: a keyed claim list holding a nested repeatable and a non-repeatable
group, beside a second repeatable group and a non-repeatable one. -/
private def claimsModel (baseYear : Option Int := none) : FlatModel := {
  baseYear := baseYear
  fields := [
    { id := 1, name := "Holder", groupPath := ["Policy"], policy := { kind := .string } },
    { id := 2, name := "Total", groupPath := ["Policy"], policy := { kind := number 2 } },
    { id := 3, name := "Zip", groupPath := ["Policy", "Address"], policy := { kind := number 0 } },
    { id := 4, name := "Value", groupPath := ["Policy", "Vehicles"], repeatableScope := [30], policy := { kind := number 0 } },
    { id := 5, name := "ClaimRef", groupPath := ["Policy", "Claims"], repeatableScope := [10], policy := { kind := .string } },
    { id := 6, name := "Status", groupPath := ["Policy", "Claims"], repeatableScope := [10], policy := { kind := .string } },
    { id := 7, name := "Amount", groupPath := ["Policy", "Claims"], repeatableScope := [10], policy := { kind := number 2 } },
    { id := 8, name := "Score", groupPath := ["Policy", "Claims", "Assessment"], repeatableScope := [10], policy := { kind := number 0 } },
    { id := 9, name := "Qty", groupPath := ["Policy", "Claims", "Parts"], repeatableScope := [10, 20], policy := { kind := number 0 } },
    { id := 10, name := "Price", groupPath := ["Policy", "Claims", "Parts"], repeatableScope := [10, 20], policy := { kind := number 2 } }]
  repeatableGroups := [
    { level := 10, path := ["Policy", "Claims"], repeatability := some 3, indexField := some 5 },
    { level := 20, path := ["Policy", "Claims", "Parts"], repeatability := some 4 },
    { level := 30, path := ["Policy", "Vehicles"], repeatability := some 2 }] }

private def dm (model : FlatModel) : DmModel :=
  { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }

/-- The class a rule draws at the policy root, with the given error field. A refusal without a class
reads as `unclassed`, which no row expects. -/
private def verdict (model : FlatModel) (errorPath condition : String) : String :=
  let rule : DmRule := {
    group := ["Policy"], name := "Sum", errorCode := "SUM",
    errorEntityRelPath := "../" ++ errorPath, condition := condition, severity := "ERROR" }
  match checkRule (dm model) .english rule with
  | .ok _ => "ADMITTED"
  | .error refusal => refusal.kernelClass?.getD "unclassed"

/-- The class a computation of the policy's total draws. -/
private def computationVerdict (model : FlatModel) (operation : String) : String :=
  let computation : DmComputation := {
    name := "TotalOfClaims", group := ["Policy"], targetRelPath := "../Total",
    commonPrecondition := none, alternatives := [{ precondition := none, operation := operation }],
    errorCodesToSuppress := [] }
  match lowerComputation model .english computation with
  | .ok _ => "ADMITTED"
  | .error refusal => refusal.kernelClass?.getD "unclassed"

private def holder (condition : String) : String := "FieldFilled(Holder) And " ++ condition

/-- One row: the model, the error field's relative path, the condition, and the Kernel's answer. -/
private abbrev Row := FlatModel × String × String × String

private def holds (rows : List Row) : Bool :=
  rows.all fun (model, errorPath, condition, expected) => verdict model errorPath condition == expected

-- Locked: a12-dmkits SumOfTermsIterationEntityLawsTest at 1124b523f, kernel 31.1.1.
-- The entity is a starred repeatable group with an iterating term; the unstarred rows draw the
-- iteration walk's class where the rule does not bind the level, and the entity's own where it does.
example : holds [
    (entityModel, "Holder", holder "SumOfTerms(Claims*, [Claims/Amount]) > 0", "ADMITTED"),
    (entityModel, "Holder", holder "SumOfTerms(Claims*, [Claims/Amount] + [Claims/Reserve]) > 0", "ADMITTED"),
    (entityModel, "Holder", holder "SumOfTerms(Claims* Having [Claims/Amount] > 5, [Claims/Amount]) > 0", "ADMITTED"),
    (entityModel, "Claims/Amount", "SumOfTerms(Claims, [Claims/Amount]) > 0", "MVK_WILDCARD_AT_LOWEST_LEVEL_REQUIRED"),
    (entityModel, "Holder", "SumOfTerms(Claims, [Claims/Amount]) > 0", "MVK_NO_WILDCARD"),
    (entityModel, "Holder", "SumOfTerms(Claims*, 5) > 0", "MVK_NO_ITERATION_FOR_LOWEST_WILDCARD"),
    (entityModel, "Holder", "SumOfTerms(Claims*/Amount, [Claims/Amount]) > 0", "MVK_NO_FIELDS_ALLOWED")] = true := by
  native_decide

-- Locked: a12-dmkits SumOfTermsTermLawsTest at 1124b523f, kernel 31.1.1
-- (`theTermIsANumberThatIteratesOnlyTheIterationEntitysPath`). Each refusal pairs with an admitted
-- row differing in one element of the term.
example : holds [
    (claimsModel, "Holder", holder "SumOfTerms(Claims*, [Claims/Amount]) > 0", "ADMITTED"),
    (claimsModel, "Holder", holder "SumOfTerms(Claims*, [Claims/Status]) > 0", "MVK_NO_NUMBER"),
    (claimsModel, "Holder", holder "SumOfTerms(Claims*, [Claims/Amount] + [Vehicles/Value]) > 0",
      "MVK_INVALID_ITERATION_IN_SET_EXPRESSION"),
    (claimsModel, "Holder", holder "SumOfTerms(Claims*, [Claims/Amount] + [Address/Zip]) > 0", "ADMITTED"),
    (claimsModel, "Holder", holder "SumOfTerms(Claims*, [Claims/Amount] + [Claims/Amount For \"C1\"]) > 0",
      "MVK_SEMANTIC_INDEX_NOT_ALLOWED"),
    (claimsModel, "Holder", holder "SumOfTerms(Claims*, [$Claims/Amount]) > 0", "MVK_INVALID_OUTER_ITERATION"),
    (claimsModel, "Holder", holder "SumOfTerms(Claims*, [Claims/Amount] + NumberOfFilledFields(Vehicles*/Value Having [Vehicles/Value] > 1)) > 0",
      "MVK_DISALLOWED_CONSTRUCT_IN_SET_EXPRESSION"),
    (claimsModel, "Holder", holder "SumOfTerms(Claims*, NumberOfFilledGroups(Claims/Parts* Having [Claims/Parts/Qty] > 1)) > 0",
      "MVK_NO_WILDCARD"),
    (claimsModel, "Holder", holder "SumOfTerms(Claims*, [Claims/Amount] + NumberOfFilledFields(Vehicles*/Value)) > 0", "ADMITTED"),
    (claimsModel, "Holder", holder "SumOfTerms(Claims*, Sum(Claims/Parts*/Qty)) > 0", "ADMITTED"),
    (claimsModel, "Holder", holder "SumOfTerms(Claims*, SumOfTerms(Claims/Parts*, [Claims/Parts/Qty])) > 0",
      "MVK_DISALLOWED_CONSTRUCT_IN_SET_EXPRESSION")] = true := by
  native_decide

-- Locked: a12-dmkits SumOfTermsTermLawsTest at 1124b523f, kernel 31.1.1
-- (`aNestedIterationEntityIsIteratedAtItsLowestLevel`).
example : holds [
    (claimsModel, "Holder", holder "SumOfTerms(Claims*/Parts*, [Claims/Parts/Qty] * [Claims/Parts/Price]) > 0", "ADMITTED"),
    (claimsModel, "Holder", holder "SumOfTerms(Claims*/Parts*, [Claims/Amount]) > 0", "MVK_NO_ITERATION_FOR_LOWEST_WILDCARD"),
    (claimsModel, "Claims/Amount", "FieldFilled(Claims/Amount) And SumOfTerms(Claims/Parts*, [Claims/Parts/Qty]) > 10", "ADMITTED"),
    (claimsModel, "Holder", "SumOfTerms(Claims/Parts*, [Claims/Parts/Qty]) > 10", "MVK_NO_WILDCARD"),
    (claimsModel, "Holder", holder "SumOfTerms(Address*, [Address/Zip]) > 0", "MVK_INVALID_WILDCARD"),
    (claimsModel, "Holder", holder "SumOfTerms(Claims*/Parts, [Claims/Parts/Qty]) > 0", "MVK_NO_WILDCARD"),
    (claimsModel, "Holder", holder "SumOfTerms(Claims*/Assessment, [Claims/Assessment/Score]) > 0", "MVK_GROUP_NOT_REPEATABLE")] = true := by
  native_decide

-- Locked: a12-dmkits SumOfTermsTermLawsTest at 1124b523f, kernel 31.1.1
-- (`theTermAndTheFilterEachReferenceTheErrorField`). A term read never references the error field and
-- refuses the marker outright; a filter read references it once marked.
example : holds [
    (claimsModel, "Total", "SumOfTerms(Claims*, [Claims/Amount] + [Total]) > 0", "MVK_ERROR_FIELD_NOT_REFERENCED"),
    (claimsModel, "Total", "SumOfTerms(Claims*, [Claims/Amount] + [$Total]) > 0", "MVK_INVALID_OUTER_ITERATION"),
    (claimsModel, "Total", "SumOfTerms(Claims* Having [Claims/Amount] > [Total], [Claims/Amount]) > 0",
      "MVK_ERROR_FIELD_NOT_REFERENCED"),
    (claimsModel, "Total", "SumOfTerms(Claims* Having [Claims/Amount] > [$Total], [Claims/Amount]) > 0", "ADMITTED"),
    (claimsModel, "Total", "SumOfTerms(Claims*, [Claims/Amount]) > 0", "MVK_ERROR_FIELD_NOT_REFERENCED"),
    (claimsModel, "Total", "FieldFilled(Total) And SumOfTerms(Claims*, [Claims/Amount]) > 0", "ADMITTED"),
    (claimsModel, "Claims/Status", "SumOfTerms(Claims*, [Claims/Amount]) > 0", "ADMITTED"),
    (claimsModel, "Claims/Status",
      "FieldFilled(Claims/Status) And SumOfTerms(Claims/Parts*, [Claims/Parts/Qty]) > 0", "ADMITTED")] = true := by
  native_decide

-- Locked: a12-dmkits SumOfTermsTermLawsTest at 1124b523f, kernel 31.1.1
-- (`theRemainingArmsOfTheIterationAndTermWalk`).
example : holds [
    (claimsModel, "Holder", holder "SumOfTerms(Claims* For \"C1\", [Claims/Amount]) > 0", "MVK_SEMANTIC_INDEX_AND_WILDCARD"),
    (claimsModel, "Holder", holder "SumOfTerms(Claims*/Parts*, [Claims/Parts/Qty] + Sum(Claims*/Parts/Price)) > 0", "MVK_NO_WILDCARD"),
    (claimsModel, "Vehicles/Value", "SumOfTerms(Claims*, [Claims/Amount]) > 0", "MVK_ERROR_FIELD_NOT_REFERENCED"),
    (claimsModel, "Claims/Status", "SumOfTerms(Claims*/Parts*, [Claims/Parts/Qty]) > 0", "MVK_ERROR_FIELD_NOT_REFERENCED"),
    (claimsModel, "Claims/Parts/Price", "SumOfTerms(Claims*/Parts*, [Claims/Parts/Qty]) > 0", "ADMITTED")] = true := by
  native_decide

-- Locked: a12-dmkits SumOfTermsTermLawsTest at 1124b523f, kernel 31.1.1
-- (`aBaseYearTermIsDecidedByTheIterationWalk`), on a model declaring a base year.
example : holds [
    (claimsModel (some 2024), "Holder", holder "SumOfTerms(Claims*, [Claims/Amount]) > 0", "ADMITTED"),
    (claimsModel (some 2024), "Holder", holder "SumOfTerms(Claims*, BaseYear) > 0", "MVK_NO_ITERATION_FOR_LOWEST_WILDCARD"),
    (claimsModel (some 2024), "Holder", holder "SumOfTerms(Claims*, [Claims/Amount] + BaseYear) > 0", "ADMITTED")] = true := by
  native_decide

-- Locked: a12-dmkits SumOfTermsTermLawsTest at 1124b523f, kernel 31.1.1 (`aComputationMayAssignATermSum`).
example : computationVerdict claimsModel "SumOfTerms(Claims*, [Claims/Amount] * 2)" = "ADMITTED" ∧
    computationVerdict claimsModel "SumOfTerms(Claims*, 5)" = "MVK_NO_ITERATION_FOR_LOWEST_WILDCARD" := by
  native_decide

end A12Kernel.Dm.SumOfTermsLocks
