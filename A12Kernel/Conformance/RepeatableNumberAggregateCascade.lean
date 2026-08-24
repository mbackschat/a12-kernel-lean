import A12Kernel.Elaboration.RepeatableNumberAggregateCascade

/-! # Repeatable Number to aggregate cascade locks -/

namespace A12Kernel.Conformance.RepeatableNumberAggregateCascade

open A12Kernel

private def number (id : FieldId) (name : String) (groupPath : GroupPath)
    (scope : List RepeatableLevel) : FlatFieldDecl := {
  id, name, groupPath, repeatableScope := scope
  policy := { kind := .number { scale := 2, signed := true } }
  numericTargetConstraints := { minFractionalDigits := 2 }
}

private def best := number 1 "Best" ["Shop"] []
private def price := number 2 "Price" ["Shop", "Pricing"] [10]
private def helper := number 3 "Helper" ["Shop", "Pricing"] [10]

private def model : FlatModel := {
  fields := [best, price, helper]
  repeatableGroups := [{
    level := 10
    path := ["Shop", "Pricing"]
    repeatability := some 3
  }]
}

private def prepared :
    PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

private def parent (field : String) : SurfaceFieldPath :=
  { base := .relative 1, groups := [], field }

private def star (field : String) : SurfaceStarFieldPath := {
  base := .absolute
  groups := [
    { name := "Shop" },
    { name := "Pricing", starred := true }]
  field
}

private def nestedPath := ["Shop", "Pricing", "Items"]

private def nestedModel : FlatModel := {
  fields := [
    best,
    { price with groupPath := nestedPath, repeatableScope := [10, 20] },
    { helper with groupPath := nestedPath, repeatableScope := [10, 20] }]
  repeatableGroups := [
    { level := 10, path := ["Shop", "Pricing"], repeatability := some 3 },
    { level := 20, path := nestedPath, repeatability := some 3 }]
}

private def nestedStar (field : String) : SurfaceStarFieldPath := {
  base := .absolute
  groups := [
    { name := "Shop" },
    { name := "Pricing" },
    { name := "Items", starred := true }]
  field
}

private def plan? (op : NumericAggregateOp)
    (rowSource : SurfaceFieldPath := bare "Price")
    (aggregateSource : SurfaceStarFieldPath := star "Helper") :
    Option (CheckedRepeatableNumberAggregateCascade model) :=
  (checkRepeatableNumberAggregateCascade model
    ["Shop", "Pricing"] helper.id rowSource
    ["Shop"] best.id aggregateSource op).toOption

private def decimalCell (field : FieldId) (path : List Nat)
    (stored : String) (unscaled : Int) : ClassifiedCellInput := {
  address := { field, path }
  stored
  raw := .parsed (.num (unscaled / 100))
  numericDecimal := some { unscaled, scale := 2 }
}

private def invalidPrice : ClassifiedCellInput := {
  address := { field := price.id, path := [2] }
  stored := "5.5"
  raw := .rejected .declaredConstraint
}

private def input? (secondPrice : ClassifiedCellInput) :
    Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := [
      { group := 10, path := [1] },
      { group := 10, path := [2] }]
    cells := [
      decimalCell price.id [1] "10.00" 1000,
      secondPrice,
      decimalCell helper.id [1] "1.00" 100,
      decimalCell helper.id [2] "1.00" 100,
      decimalCell best.id [] "99.99" 9999]
  }).toOption

private def summary? (op : NumericAggregateOp)
    (secondPrice : ClassifiedCellInput) :
    Option (List (CellAddr × NumericTargetOutcome) ×
      CellAddr × NumericTargetOutcome) := do
  let plan <- plan? op
  let input <- input? secondPrice
  let outcomes <- (plan.execute { now := { epochMillis := 0 } } input).toOption
  pure (outcomes.rows.map fun row => (row.targetField, row.outcome),
    outcomes.aggregate.targetField, outcomes.aggregate.outcome)

/- Analyze preserves both real field edges and the repeatable scope. -/
example :
    (plan? .maximum).map CheckedRepeatableNumberAggregateCascade.analyze =
      some {
        operation := .maximum
        repeatableScope := [10]
        fieldDependencies := [
          (helper.id, [price.id]),
          (best.id, [helper.id])]
      } := by
  native_decide

/- The aggregate reads freshly computed row values, not either stale Helper seed. -/
example :
    summary? .maximum (decimalCell price.id [2] "3.10" 310) = some (
      [
        ({ field := helper.id, path := [1] },
          .accepted { unscaled := 1000, scale := 2 }),
        ({ field := helper.id, path := [2] },
          .accepted { unscaled := 310, scale := 2 })],
      { field := best.id, path := [] },
      .accepted { unscaled := 1000, scale := 2 }) := by
  native_decide

/- One poisoned computed row reaches the later Sum as cause-blind dependency poison. -/
example :
    summary? .sum invalidPrice = some (
      [
        ({ field := helper.id, path := [1] },
          .accepted { unscaled := 1000, scale := 2 }),
        ({ field := helper.id, path := [2] },
          .inheritedPoison .declaredConstraint)],
      { field := best.id, path := [] },
      .inheritedPoison .computedDependency) := by
  native_decide

/- A different star field is not the dependency, and reading the total back into the row is a cycle. -/
example :
    (match checkRepeatableNumberAggregateCascade model
        ["Shop", "Pricing"] helper.id (bare "Price")
        ["Shop"] best.id (star "Price") .maximum with
      | .error (.dependency expected actual) =>
          expected == helper.id && actual == price.id
      | _ => false) = true ∧
    (match checkRepeatableNumberAggregateCascade model
        ["Shop", "Pricing"] helper.id (parent "Best")
        ["Shop"] best.id (star "Helper") .maximum with
      | .error (.cycle field) => field == best.id
      | _ => false) = true := by
  native_decide

/- A valid nested producer and matching star still fail at this route's one-level boundary. -/
example :
    (match checkRepeatableNumberAggregateCascade nestedModel
        nestedPath helper.id (bare "Price")
        ["Shop"] best.id (nestedStar "Helper") .maximum with
      | .error (.unsupportedScope scope) => scope == [10, 20]
      | _ => false) = true := by
  native_decide

end A12Kernel.Conformance.RepeatableNumberAggregateCascade
