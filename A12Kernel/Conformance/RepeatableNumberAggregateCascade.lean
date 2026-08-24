import A12Kernel.Elaboration.RepeatableNumberAggregateCascade

/-! # Repeatable Number to aggregate cascade locks -/

namespace A12Kernel.Conformance.RepeatableNumberAggregateCascade

open A12Kernel

private def number (id : FieldId) (name : String) (groupPath : GroupPath)
    (scope : List RepeatableLevel) (scale : Nat := 2) : FlatFieldDecl := {
  id, name, groupPath, repeatableScope := scope
  policy := { kind := .number { scale, signed := true } }
  numericTargetConstraints := { minFractionalDigits := scale }
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

private def binaryTotal := number 11 "Total" ["Order"] []
private def doubled := number 17 "Doubled" ["Order"] []
private def otherRoot := number 18 "Other" ["Order"] []
private def quantity := number 12 "Qty" ["Order", "Lines"] [30] 0
private def unitPrice := number 13 "Price" ["Order", "Lines"] [30]
private def amount := number 14 "Amount" ["Order", "Lines"] [30]
private def commission := number 15 "Commission" ["Order", "Lines"] [30]
private def limit := number 16 "Limit" ["Order", "Lines"] [30]

private def binaryModel : FlatModel := {
  fields := [binaryTotal, doubled, otherRoot, quantity, unitPrice, amount,
    commission, limit]
  repeatableGroups := [{
    level := 30
    path := ["Order", "Lines"]
    repeatability := some 3
  }]
}

private def binaryStar (field : String) : SurfaceStarFieldPath := {
  base := .absolute
  groups := [
    { name := "Order" },
    { name := "Lines", starred := true }]
  field
}

private def binaryPlan? :
    Option (CheckedRepeatableNumberAggregateCascade binaryModel) :=
  (checkRepeatableNumberBinaryAggregateCascade binaryModel
    ["Order", "Lines"] amount.id (bare "Qty") (bare "Price") .multiply
    ["Order"] binaryTotal.id (binaryStar "Amount") .sum).toOption

private def innerNumber (field : String) : SurfaceHavingNumberRef := {
  origin := .inner
  field := { base := .absolute, groups := ["Order", "Lines"], field }
}

private def amountUnderLimit : SurfaceCorrelatedHaving :=
  .compareNumbers .less (innerNumber "Amount") (innerNumber "Limit")

private def conjunctiveAmountFilter : SurfaceCorrelatedHaving :=
  .and amountUnderLimit
    (.compareNumbers .less (innerNumber "Price") (innerNumber "Amount"))

private def filteredBinaryPlan? :
    Option (CheckedRepeatableNumberAggregateCascade binaryModel) :=
  (checkRepeatableNumberBinaryFilteredAggregateCascade binaryModel
    ["Order", "Lines"] amount.id (bare "Qty") (bare "Price") .multiply
    ["Order"] binaryTotal.id (binaryStar "Commission")
    amountUnderLimit .sum).toOption

private def aggregateScalarPlan? :
    Option (CheckedRepeatableNumberAggregateScalarCascade binaryModel) := do
  let cascade ← binaryPlan?
  (checkRepeatableNumberAggregateScalarCascade cascade ["Order"] doubled.id
    (bare "Total") (bare "Total") .add).toOption

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

private def quantityCell (row : Nat) (stored : String)
    (value : Int) : ClassifiedCellInput := {
  address := { field := quantity.id, path := [row] }
  stored
  raw := .parsed (.num value)
  numericDecimal := some { unscaled := value, scale := 0 }
}

private def invalidUnitPrice : ClassifiedCellInput := {
  address := { field := unitPrice.id, path := [2] }
  stored := "5.123"
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

private def binaryInput? (secondPrice : ClassifiedCellInput) :
    Option (CheckedDocument binaryModel) :=
  (checkDocument
    ((prepareFlatStringContext { now := { epochMillis := 0 } }
      builtinStringPatternCompiler binaryModel).toOption.get
        (by native_decide)) "en_US" {
      instantiatedRows := [
        { group := 30, path := [1] },
        { group := 30, path := [2] }]
      cells := [
        quantityCell 1 "2" 2,
        decimalCell unitPrice.id [1] "10.00" 1000,
        quantityCell 2 "3" 3,
        secondPrice,
        decimalCell amount.id [1] "1.00" 100,
        decimalCell amount.id [2] "1.00" 100,
        decimalCell binaryTotal.id [] "99.99" 9999,
        decimalCell doubled.id [] "1.00" 100,
        decimalCell otherRoot.id [] "4.00" 400]
    }).toOption

private def binarySummary? (secondPrice : ClassifiedCellInput) :
    Option (RepeatableNumberAggregateCascadeAnalysis ×
      List (CellAddr × NumericTargetOutcome) × NumericTargetOutcome) := do
  let plan <- binaryPlan?
  let input <- binaryInput? secondPrice
  let outcomes <- (plan.execute { now := { epochMillis := 0 } } input).toOption
  pure (plan.analyze,
    outcomes.rows.map fun row => (row.targetField, row.outcome),
    outcomes.aggregate.outcome)

private def aggregateScalarSummary? (secondPrice : ClassifiedCellInput) :
    Option (RepeatableNumberAggregateScalarCascadeAnalysis ×
      List (CellAddr × NumericTargetOutcome) × NumericTargetOutcome ×
      NumericTargetOutcome) := do
  let plan ← aggregateScalarPlan?
  let input ← binaryInput? secondPrice
  let outcomes ← (plan.execute { now := { epochMillis := 0 } } input).toOption
  pure (plan.analyze,
    outcomes.cascade.rows.map fun row => (row.targetField, row.outcome),
    outcomes.cascade.aggregate.outcome,
    outcomes.scalar.outcome)

private def filteredBinaryInput? (secondPrice : ClassifiedCellInput) :
    Option (CheckedDocument binaryModel) :=
  (checkDocument
    ((prepareFlatStringContext { now := { epochMillis := 0 } }
      builtinStringPatternCompiler binaryModel).toOption.get
        (by native_decide)) "en_US" {
      instantiatedRows := [
        { group := 30, path := [1] },
        { group := 30, path := [2] }]
      cells := [
        quantityCell 1 "2" 2,
        decimalCell unitPrice.id [1] "10.00" 1000,
        quantityCell 2 "3" 3,
        secondPrice,
        decimalCell amount.id [1] "99.00" 9900,
        decimalCell amount.id [2] "1.00" 100,
        decimalCell commission.id [1] "7.00" 700,
        decimalCell commission.id [2] "11.00" 1100,
        decimalCell limit.id [1] "30.00" 3000,
        decimalCell limit.id [2] "50.00" 5000,
        decimalCell binaryTotal.id [] "99.99" 9999]
    }).toOption

private def filteredBinarySummary? (secondPrice : ClassifiedCellInput) :
    Option (RepeatableNumberAggregateCascadeAnalysis ×
      List (CellAddr × NumericTargetOutcome) × NumericTargetOutcome) := do
  let plan <- filteredBinaryPlan?
  let input <- filteredBinaryInput? secondPrice
  let outcomes <- (plan.execute { now := { epochMillis := 0 } } input).toOption
  pure (plan.analyze,
    outcomes.rows.map fun row => (row.targetField, row.outcome),
    outcomes.aggregate.outcome)

/- Analyze preserves both real field edges and the repeatable scope. -/
example :
    (plan? .maximum).map CheckedRepeatableNumberAggregateCascade.analyze =
      some {
        producer := .direct
        consumer := .plain
        operation := .maximum
        repeatableScope := [10]
        fieldDependencies := [
          (helper.id, [price.id]),
          (best.id, [helper.id])]
      } := by
  native_decide

/- Binary producer identity, ordered dependencies, fresh values, and poison all cross the same aggregate boundary. -/
example :
    binarySummary? (decimalCell unitPrice.id [2] "20.00" 2000) = some (
      {
        producer := .binary .multiply
        consumer := .plain
        operation := .sum
        repeatableScope := [30]
        fieldDependencies := [
          (amount.id, [quantity.id, unitPrice.id]),
          (binaryTotal.id, [amount.id])]
      },
      [
        ({ field := amount.id, path := [1] },
          .accepted { unscaled := 2000, scale := 2 }),
        ({ field := amount.id, path := [2] },
          .accepted { unscaled := 6000, scale := 2 })],
      .accepted { unscaled := 8000, scale := 2 }) ∧
    (binarySummary? invalidUnitPrice).map (fun result =>
      (result.2.1, result.2.2)) = some (
        [
          ({ field := amount.id, path := [1] },
            .accepted { unscaled := 2000, scale := 2 }),
          ({ field := amount.id, path := [2] },
            .inheritedPoison .declaredConstraint)],
        .inheritedPoison .computedDependency) := by
  native_decide

/- A later root scalar reads the fresh aggregate outcome rather than its stale seed, and cause-blind poison crosses both stage boundaries. -/
example :
    aggregateScalarSummary?
        (decimalCell unitPrice.id [2] "20.00" 2000) = some (
      {
        cascade := {
          producer := .binary .multiply
          consumer := .plain
          operation := .sum
          repeatableScope := [30]
          fieldDependencies := [
            (amount.id, [quantity.id, unitPrice.id]),
            (binaryTotal.id, [amount.id])]
        }
        scalarOperation := .add
        fieldDependencies := [
          (amount.id, [quantity.id, unitPrice.id]),
          (binaryTotal.id, [amount.id]),
          (doubled.id, [binaryTotal.id])]
      },
      [
        ({ field := amount.id, path := [1] },
          .accepted { unscaled := 2000, scale := 2 }),
        ({ field := amount.id, path := [2] },
          .accepted { unscaled := 6000, scale := 2 })],
      .accepted { unscaled := 8000, scale := 2 },
      .accepted { unscaled := 16000, scale := 2 }) ∧
    (aggregateScalarSummary? invalidUnitPrice).map (fun result =>
      (result.2.2.1, result.2.2.2)) = some (
        .inheritedPoison .computedDependency,
        .inheritedPoison .computedDependency) := by
  native_decide

/- The third stage must read the aggregate, own a new target, and remain absent from both earlier stages. -/
example :
    (match binaryPlan? with
      | none => false
      | some cascade =>
          match checkRepeatableNumberAggregateScalarCascade cascade ["Order"]
              doubled.id (bare "Other") (bare "Other") .add with
          | .error (.missingAggregateDependency field) =>
              field == binaryTotal.id
          | _ => false) = true ∧
    (match binaryPlan? with
      | none => false
      | some cascade =>
          match checkRepeatableNumberAggregateScalarCascade cascade ["Order"]
              binaryTotal.id (bare "Other") (bare "Other") .add with
          | .error (.duplicateTarget field) => field == binaryTotal.id
          | _ => false) = true ∧
    (match checkRepeatableNumberBinaryAggregateCascade binaryModel
        ["Order", "Lines"] amount.id (parent "Doubled") (bare "Price") .add
        ["Order"] binaryTotal.id (binaryStar "Amount") .sum with
      | .error _ => false
      | .ok cascade =>
          match checkRepeatableNumberAggregateScalarCascade cascade ["Order"]
              doubled.id (bare "Total") (bare "Total") .add with
          | .error (.cycle field) => field == doubled.id
          | _ => false) = true := by
  native_decide

/- The computed row value is read only by `Having`: stale seeds select the opposite row, while the fresh overlay keeps Commission 7 and drops Commission 11. A poisoned producer aborts the filtered aggregate even though its value field is clean. -/
example :
    filteredBinarySummary?
        (decimalCell unitPrice.id [2] "20.00" 2000) = some (
      {
        producer := .binary .multiply
        consumer := .filtered
        operation := .sum
        repeatableScope := [30]
        fieldDependencies := [
          (amount.id, [quantity.id, unitPrice.id]),
          (binaryTotal.id, [commission.id, amount.id, limit.id])]
      },
      [
        ({ field := amount.id, path := [1] },
          .accepted { unscaled := 2000, scale := 2 }),
        ({ field := amount.id, path := [2] },
          .accepted { unscaled := 6000, scale := 2 })],
      .accepted { unscaled := 700, scale := 2 }) ∧
    (filteredBinarySummary? invalidUnitPrice).map (fun result =>
      (result.2.1, result.2.2)) = some (
        [
          ({ field := amount.id, path := [1] },
            .accepted { unscaled := 2000, scale := 2 }),
          ({ field := amount.id, path := [2] },
            .inheritedPoison .declaredConstraint)],
        .inheritedPoison .computedDependency) ∧
    (checkRepeatableNumberBinaryFilteredAggregateCascade binaryModel
      ["Order", "Lines"] amount.id (bare "Qty") (bare "Price") .multiply
      ["Order"] binaryTotal.id (binaryStar "Commission")
      conjunctiveAmountFilter .sum).toOption.map (fun plan =>
        plan.analyze.fieldDependencies[1]?) =
      some (some (binaryTotal.id,
        [commission.id, amount.id, limit.id, unitPrice.id])) := by
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

/- Either binary source may not read the later aggregate target. -/
example :
    (match checkRepeatableNumberBinaryAggregateCascade binaryModel
        ["Order", "Lines"] amount.id (bare "Qty") (parent "Total") .add
        ["Order"] binaryTotal.id (binaryStar "Amount") .sum with
      | .error (.cycle field) => field == binaryTotal.id
      | _ => false) = true := by
  native_decide

/- A filtered aggregate is a downstream stage only when the filter itself reads the producer. Neither sharing its row group nor aggregating the producer bypasses that gate. -/
example :
    (match checkRepeatableNumberBinaryFilteredAggregateCascade binaryModel
        ["Order", "Lines"] amount.id (bare "Qty") (bare "Price") .multiply
        ["Order"] binaryTotal.id (binaryStar "Commission")
        (.compareNumbers .less
          (innerNumber "Commission") (innerNumber "Limit")) .sum with
      | .error (.missingFilterDependency field) => field == amount.id
      | _ => false) = true ∧
    (match checkRepeatableNumberBinaryFilteredAggregateCascade binaryModel
        ["Order", "Lines"] amount.id (bare "Qty") (bare "Price") .multiply
        ["Order"] binaryTotal.id (binaryStar "Amount")
        (.compareNumbers .less
          (innerNumber "Commission") (innerNumber "Limit")) .sum with
      | .error (.missingFilterDependency field) => field == amount.id
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
