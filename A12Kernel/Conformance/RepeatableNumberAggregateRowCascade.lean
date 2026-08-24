import A12Kernel.Elaboration.RepeatableNumberAggregateRowCascade

/-! # Aggregate-to-repeatable Number cascade locks -/

namespace A12Kernel.Conformance.RepeatableNumberAggregateRowCascade

open A12Kernel

private def number (id : FieldId) (name : String) (groupPath : GroupPath)
    (scope : List RepeatableLevel) (scale : Nat := 2) : FlatFieldDecl := {
  id, name, groupPath, repeatableScope := scope
  policy := { kind := .number { scale, signed := true } }
  numericTargetConstraints := { minFractionalDigits := scale }
}

private def total := number 1 "Total" ["Order"] []
private def other := number 2 "Other" ["Order"] []
private def quantity := number 3 "Qty" ["Order", "Lines"] [30] 0
private def price := number 4 "Price" ["Order", "Lines"] [30]
private def amount := number 5 "Amount" ["Order", "Lines"] [30]
private def allocation := number 6 "Allocation" ["Order", "Lines"] [30]

private def model : FlatModel := {
  fields := [total, other, quantity, price, amount, allocation]
  repeatableGroups := [{
    level := 30
    path := ["Order", "Lines"]
    repeatability := some 3
  }]
}

private def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

private def parent (field : String) : SurfaceFieldPath :=
  { base := .relative 1, groups := [], field }

private def star (field : String) : SurfaceStarFieldPath := {
  base := .absolute
  groups := [{ name := "Order" }, { name := "Lines", starred := true }]
  field
}

private def innerNumber (field : String) : SurfaceHavingNumberRef := {
  origin := .inner
  field := { base := .absolute, groups := ["Order", "Lines"], field }
}

private def cascade? : Option (CheckedRepeatableNumberAggregateCascade model) :=
  (checkRepeatableNumberBinaryAggregateCascade model
    ["Order", "Lines"] amount.id (bare "Qty") (bare "Price") .multiply
    ["Order"] total.id (star "Amount") .sum).toOption

private def plan? : Option (CheckedRepeatableNumberAggregateRowCascade model) := do
  let cascade ← cascade?
  (checkRepeatableNumberAggregateRowCascade cascade
    ["Order", "Lines"] allocation.id (parent "Total")).toOption

private def decimalCell (field : FieldId) (path : List Nat)
    (stored : String) (unscaled : Int) : ClassifiedCellInput := {
  address := { field, path }
  stored
  raw := .parsed (.num (unscaled / 100))
  numericDecimal := some { unscaled, scale := 2 }
}

private def quantityCell (row : Nat) (value : Int) : ClassifiedCellInput := {
  address := { field := quantity.id, path := [row] }
  stored := toString value
  raw := .parsed (.num value)
  numericDecimal := some { unscaled := value, scale := 0 }
}

private def invalidPrice : ClassifiedCellInput := {
  address := { field := price.id, path := [2] }
  stored := "20.123"
  raw := .rejected .declaredConstraint
}

private def input? (secondPrice : ClassifiedCellInput) : Option (CheckedDocument model) := do
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption
  (checkDocument prepared "en_US" {
    instantiatedRows := [
      { group := 30, path := [1] }, { group := 30, path := [2] }]
    cells := [
      quantityCell 1 2, decimalCell price.id [1] "10.00" 1000,
      quantityCell 2 3, secondPrice,
      decimalCell amount.id [1] "1.00" 100,
      decimalCell amount.id [2] "1.00" 100,
      decimalCell total.id [] "99.99" 9999,
      decimalCell allocation.id [1] "1.00" 100,
      decimalCell allocation.id [2] "2.00" 200]
  }).toOption

private def summary? (secondPrice : ClassifiedCellInput) :
    Option (RepeatableNumberAggregateRowCascadeAnalysis ×
      List (CellAddr × NumericTargetOutcome) × NumericTargetOutcome ×
      List (CellAddr × NumericTargetOutcome)) := do
  let plan ← plan?
  let input ← input? secondPrice
  let outcomes ← (plan.execute { now := { epochMillis := 0 } } input).toOption
  pure (plan.analyze,
    outcomes.cascade.rows.map fun row => (row.targetField, row.outcome),
    outcomes.cascade.aggregate.outcome,
    outcomes.suffix.map fun row => (row.targetField, row.outcome))

/- Fresh aggregate state reaches every suffix row; reached aggregate poison does too. -/
example :
    summary? (decimalCell price.id [2] "20.00" 2000) = some (
      {
        cascade := {
          producer := .binary .multiply
          consumer := .plain
          operation := .sum
          repeatableScope := [30]
          fieldDependencies := [
            (amount.id, [quantity.id, price.id]), (total.id, [amount.id])]
        }
        suffixTarget := allocation.id
        repeatableScope := [30]
        fieldDependencies := [
          (amount.id, [quantity.id, price.id]),
          (total.id, [amount.id]),
          (allocation.id, [total.id])]
      },
      [
        ({ field := amount.id, path := [1] },
          .accepted { unscaled := 2000, scale := 2 }),
        ({ field := amount.id, path := [2] },
          .accepted { unscaled := 6000, scale := 2 })],
      .accepted { unscaled := 8000, scale := 2 },
      [
        ({ field := allocation.id, path := [1] },
          .accepted { unscaled := 8000, scale := 2 }),
        ({ field := allocation.id, path := [2] },
          .accepted { unscaled := 8000, scale := 2 })]) ∧
    (summary? invalidPrice).map (fun result => (result.2.2.1, result.2.2.2)) =
      some (
        .inheritedPoison .computedDependency,
        [
          ({ field := allocation.id, path := [1] },
            .inheritedPoison .computedDependency),
          ({ field := allocation.id, path := [2] },
            .inheritedPoison .computedDependency)]) := by
  native_decide

/- The suffix must read the aggregate, own a new target, and stay absent from prefix reads. -/
example :
    (match cascade? with
      | none => false
      | some cascade =>
          match checkRepeatableNumberAggregateRowCascade cascade
              ["Order", "Lines"] allocation.id (parent "Other") with
          | .error (.missingAggregateDependency expected actual) =>
              expected == total.id && actual == other.id
          | _ => false) = true ∧
    (match cascade? with
      | none => false
      | some cascade =>
          match checkRepeatableNumberAggregateRowCascade cascade
              ["Order", "Lines"] amount.id (parent "Total") with
          | .error (.duplicateTarget field) => field == amount.id
          | _ => false) = true ∧
    (do
      let cascade ← (checkRepeatableNumberBinaryAggregateCascade model
        ["Order", "Lines"] amount.id (bare "Allocation") (bare "Price") .add
        ["Order"] total.id (star "Amount") .sum).toOption
      match checkRepeatableNumberAggregateRowCascade cascade
          ["Order", "Lines"] allocation.id (parent "Total") with
      | .error (.cycle field) => some field
      | _ => none) = some allocation.id ∧
    (do
      let having := SurfaceCorrelatedHaving.and
        (.compareNumbers .less (innerNumber "Amount") (innerNumber "Price"))
        (.compareNumbers .less
          (innerNumber "Allocation") (innerNumber "Price"))
      let cascade ← (checkRepeatableNumberBinaryFilteredAggregateCascade model
        ["Order", "Lines"] amount.id (bare "Qty") (bare "Price") .multiply
        ["Order"] total.id (star "Price") having .sum).toOption
      match checkRepeatableNumberAggregateRowCascade cascade
          ["Order", "Lines"] allocation.id (parent "Total") with
      | .error (.cycle field) => some field
      | _ => none) = some allocation.id := by
  native_decide

end A12Kernel.Conformance.RepeatableNumberAggregateRowCascade
