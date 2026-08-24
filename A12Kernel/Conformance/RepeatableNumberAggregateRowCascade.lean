import A12Kernel.Elaboration.RepeatableNumberAggregateRowCascade

/-! # Aggregate-to-repeatable scalar cascade locks -/

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
private def final := number 7 "Final" ["Order", "Lines"] [30]
private def label : FlatFieldDecl := {
  id := 8
  name := "Label"
  groupPath := ["Order", "Lines"]
  repeatableScope := [30]
  policy := { kind := .string }
}

private def model : FlatModel := {
  fields := [total, other, quantity, price, amount, allocation, final, label]
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

private def group : SurfaceGroupPath := {
  base := .absolute
  groups := ["Order", "Lines"]
}

private def checkedRowChain? (firstTarget : FieldId)
    (firstSource : SurfaceFieldPath) (secondTarget : FieldId)
    (secondSource : SurfaceFieldPath) :
    Option (CheckedCurrentRepetitionNumberCascade model) :=
  (checkCurrentRepetitionNumberCascade model ["Order", "Lines"] group
    firstTarget firstSource secondTarget secondSource).toOption

private def rowChain? : Option (CheckedCurrentRepetitionNumberCascade model) :=
  checkedRowChain? allocation.id (parent "Total") final.id (bare "Allocation")

private def chain? : Option (CheckedRepeatableNumberAggregateRowChain model) := do
  let cascade ← cascade?
  let suffix ← rowChain?
  (checkRepeatableNumberAggregateRowChain cascade suffix).toOption

private def checkedNumberToStringRowChain? (numberTarget : FieldId)
    (numberSource : SurfaceFieldPath) (stringSource : SurfaceFieldPath) :
    Option (CheckedCurrentRepetitionNumberToStringCascade model) :=
  (checkCurrentRepetitionNumberToStringCascade model ["Order", "Lines"] group
    numberTarget numberSource label.id stringSource).toOption

private def numberToStringRowChain? :
    Option (CheckedCurrentRepetitionNumberToStringCascade model) :=
  checkedNumberToStringRowChain? allocation.id (parent "Total")
    (bare "Allocation")

private def numberToStringChain? :
    Option (CheckedRepeatableNumberAggregateNumberToStringRowChain model) := do
  let cascade ← cascade?
  let suffix ← numberToStringRowChain?
  (checkRepeatableNumberAggregateNumberToStringRowChain cascade suffix).toOption

private def binaryRowPlan? (left right : SurfaceFieldPath) :
    Option (CheckedRepeatableNumberAggregateBinaryRowCascade model) := do
  let cascade ← cascade?
  (checkRepeatableNumberAggregateBinaryRowCascade cascade
    ["Order", "Lines"] allocation.id left right .subtract).toOption

private def aggregateLeftBinaryPlan? :
    Option (CheckedRepeatableNumberAggregateBinaryRowCascade model) :=
  binaryRowPlan? (parent "Total") (bare "Price")

private def aggregateRightBinaryPlan? :
    Option (CheckedRepeatableNumberAggregateBinaryRowCascade model) :=
  binaryRowPlan? (bare "Price") (parent "Total")

private def binaryPlanError?
    (cascadePlan? : Option (CheckedRepeatableNumberAggregateCascade model))
    (target : FieldId) (left right : SurfaceFieldPath) :
    Option RepeatableNumberAggregateBinaryRowCascadeElabError := do
  let cascadePlan ← cascadePlan?
  match checkRepeatableNumberAggregateBinaryRowCascade cascadePlan
      ["Order", "Lines"] target left right .subtract with
  | .error cause => some cause
  | .ok _ => none

private def backEdgeCascade? :
    Option (CheckedRepeatableNumberAggregateCascade model) :=
  (checkRepeatableNumberBinaryAggregateCascade model
    ["Order", "Lines"] amount.id (bare "Allocation") (bare "Price") .add
    ["Order"] total.id (star "Amount") .sum).toOption

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

private def stringCell (field : FieldId) (path : List Nat)
    (stored : String) : ClassifiedCellInput := {
  address := { field, path }
  stored
  raw := .parsed (.str stored)
}

private def prepared :
    PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def input? (secondPrice : ClassifiedCellInput) : Option (CheckedDocument model) := do
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
      decimalCell allocation.id [2] "2.00" 200,
      decimalCell final.id [1] "3.00" 300,
      decimalCell final.id [2] "4.00" 400,
      stringCell label.id [1] "old1",
      stringCell label.id [2] "old2"]
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

private structure ChainRowSummary where
  coordinate : Nat
  firstTarget : CellAddr
  firstOutcome : NumericTargetOutcome
  secondTarget : CellAddr
  secondOutcome : NumericTargetOutcome
  deriving Repr, DecidableEq

private def chainSummary? (secondPrice : ClassifiedCellInput) :
    Option (RepeatableNumberAggregateRowChainAnalysis × NumericTargetOutcome ×
      List ChainRowSummary) := do
  let plan ← chain?
  let input ← input? secondPrice
  let outcomes ← (plan.execute { now := { epochMillis := 0 } } input).toOption
  pure (plan.analyze, outcomes.cascade.aggregate.outcome,
    outcomes.suffix.rows.map fun row =>
      { coordinate := row.coordinate
        firstTarget := row.first.targetField
        firstOutcome := row.first.outcome
        secondTarget := row.second.targetField
        secondOutcome := row.second.outcome })

private structure TypedChainRowSummary where
  coordinate : Nat
  numberTarget : CellAddr
  numberOutcome : NumericTargetOutcome
  stringTarget : CellAddr
  stringOutcome : StringTargetOutcome
  deriving Repr, DecidableEq

private def stored (text : String) (nonempty : text ≠ "") : StoredString :=
  { text, nonempty }

private def numberToStringChainSummary? (secondPrice : ClassifiedCellInput) :
    Option (RepeatableNumberAggregateRowChainAnalysis × NumericTargetOutcome ×
      List TypedChainRowSummary) := do
  let plan ← numberToStringChain?
  let input ← input? secondPrice
  let outcomes ← (plan.execute prepared.patterns
    { now := { epochMillis := 0 } } input).toOption
  pure (plan.analyze, outcomes.cascade.aggregate.outcome,
    outcomes.suffix.rows.map fun row =>
      { coordinate := row.coordinate
        numberTarget := row.number.targetField
        numberOutcome := row.number.outcome
        stringTarget := row.string.targetField
        stringOutcome := row.string.outcome })

private def binarySummary?
    (plan? : Option (CheckedRepeatableNumberAggregateBinaryRowCascade model))
    (secondPrice : ClassifiedCellInput) :
    Option (NumericTargetOutcome × List (CellAddr × NumericTargetOutcome)) := do
  let plan ← plan?
  let input ← input? secondPrice
  let outcomes ← (plan.execute { now := { epochMillis := 0 } } input).toOption
  pure (outcomes.cascade.aggregate.outcome,
    outcomes.suffix.map fun row => (row.targetField, row.outcome))

private def binaryAnalysis?
    (plan? : Option (CheckedRepeatableNumberAggregateBinaryRowCascade model)) :
    Option (NumericArithmeticOp × FieldId × List RepeatableLevel ×
      FieldId × List FieldId) := do
  let plan ← plan?
  let analysis := plan.analyze
  let dependency ← analysis.fieldDependencies.getLast?
  pure (analysis.suffixOperation, analysis.suffixTarget,
    analysis.repeatableScope, dependency)

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

/- The binary suffix must own a later target, read the aggregate on at least one side, and stay absent from prefix reads. -/
example :
    binaryPlanError? cascade? allocation.id (bare "Price")
        (parent "Other") = some (.missingAggregateDependency total.id) ∧
    binaryPlanError? cascade? total.id (parent "Total")
        (bare "Price") = some (.duplicateTarget total.id) ∧
    binaryPlanError? cascade? amount.id (parent "Total")
        (bare "Price") = some (.duplicateTarget amount.id) ∧
    binaryPlanError? backEdgeCascade? allocation.id (parent "Total")
        (bare "Price") = some (.cycle allocation.id) := by
  native_decide

/- Analyze retains the suffix operation, target scope, and authored dependency order. -/
example :
    binaryAnalysis? aggregateLeftBinaryPlan? =
      some (.subtract, allocation.id, [30], allocation.id,
        [total.id, price.id]) := by
  native_decide

example :
    binaryAnalysis? aggregateRightBinaryPlan? =
      some (.subtract, allocation.id, [30], allocation.id,
        [price.id, total.id]) := by
  native_decide

/- Authored operand order controls clean subtraction. -/
example :
    let cleanPrice := decimalCell price.id [2] "20.00" 2000
    [binarySummary? aggregateLeftBinaryPlan? cleanPrice,
      binarySummary? aggregateRightBinaryPlan? cleanPrice] = [
        some (.accepted { unscaled := 8000, scale := 2 }, [
          ({ field := allocation.id, path := [1] },
            .accepted { unscaled := 7000, scale := 2 }),
          ({ field := allocation.id, path := [2] },
            .accepted { unscaled := 6000, scale := 2 })]),
        some (.accepted { unscaled := 8000, scale := 2 }, [
          ({ field := allocation.id, path := [1] },
            .accepted { unscaled := -7000, scale := 2 }),
          ({ field := allocation.id, path := [2] },
            .accepted { unscaled := -6000, scale := 2 })])] := by
  native_decide

/- A row-local left poison short-circuits the fresh aggregate read; reversing the operands reaches aggregate poison first. -/
example :
    [binarySummary? aggregateLeftBinaryPlan? invalidPrice,
      binarySummary? aggregateRightBinaryPlan? invalidPrice] = [
        some (.inheritedPoison .computedDependency, [
          ({ field := allocation.id, path := [1] },
            .inheritedPoison .computedDependency),
          ({ field := allocation.id, path := [2] },
            .inheritedPoison .computedDependency)]),
        some (.inheritedPoison .computedDependency, [
          ({ field := allocation.id, path := [1] },
            .inheritedPoison .computedDependency),
          ({ field := allocation.id, path := [2] },
            .inheritedPoison .declaredConstraint)])] := by
  native_decide

/- The typed suffix reuses the direct Number admission boundary before entering its checked String edge. -/
example :
    (do
      let cascade ← cascade?
      let suffix ← checkedNumberToStringRowChain? allocation.id
        (parent "Other") (bare "Allocation")
      match checkRepeatableNumberAggregateNumberToStringRowChain cascade suffix with
      | .error (.missingAggregateDependency expected actual) =>
          some (expected, actual)
      | _ => none) = some (total.id, other.id) ∧
    (do
      let cascade ← cascade?
      let suffix ← checkedNumberToStringRowChain? amount.id
        (parent "Total") (bare "Amount")
      match checkRepeatableNumberAggregateNumberToStringRowChain cascade suffix with
      | .error (.duplicateTarget field) => some field
      | _ => none) = some amount.id ∧
    (do
      let cascade ← (checkRepeatableNumberBinaryAggregateCascade model
        ["Order", "Lines"] amount.id (bare "Allocation") (bare "Price") .add
        ["Order"] total.id (star "Amount") .sum).toOption
      let suffix ← numberToStringRowChain?
      match checkRepeatableNumberAggregateNumberToStringRowChain cascade suffix with
      | .error (.cycle field) => some field
      | _ => none) = some allocation.id := by
  native_decide

/- Fresh aggregate state reaches the typed row chain; reached poison crosses both target families. -/
example :
    (numberToStringChainSummary?
      (decimalCell price.id [2] "20.00" 2000)).map (·.1) = some {
        cascade := {
          producer := .binary .multiply
          consumer := .plain
          operation := .sum
          repeatableScope := [30]
          fieldDependencies := [
            (amount.id, [quantity.id, price.id]), (total.id, [amount.id])]
        }
        suffix := {
          structuralGroup := ["Order", "Lines"]
          scope := [30]
          fieldDependencies := [
            (allocation.id, [total.id]), (label.id, [allocation.id])]
        }
      } ∧
    (numberToStringChainSummary?
      (decimalCell price.id [2] "20.00" 2000)).map (·.2.1) =
        some (.accepted { unscaled := 8000, scale := 2 }) ∧
    (numberToStringChainSummary?
      (decimalCell price.id [2] "20.00" 2000)).map (·.2.2) = some [
        { coordinate := 1
          numberTarget := { field := allocation.id, path := [1] }
          numberOutcome := .accepted { unscaled := 8000, scale := 2 }
          stringTarget := { field := label.id, path := [1] }
          stringOutcome := .accepted (stored "80.00" (by decide)) },
        { coordinate := 2
          numberTarget := { field := allocation.id, path := [2] }
          numberOutcome := .accepted { unscaled := 8000, scale := 2 }
          stringTarget := { field := label.id, path := [2] }
          stringOutcome := .accepted (stored "80.00" (by decide)) }] ∧
    (numberToStringChainSummary? invalidPrice).map (·.2.1) =
      some (.inheritedPoison .computedDependency) ∧
    (numberToStringChainSummary? invalidPrice).map (·.2.2) = some [
      { coordinate := 1
        numberTarget := { field := allocation.id, path := [1] }
        numberOutcome := .inheritedPoison .computedDependency
        stringTarget := { field := label.id, path := [1] }
        stringOutcome := .poison .computedDependency },
      { coordinate := 2
        numberTarget := { field := allocation.id, path := [2] }
        numberOutcome := .inheritedPoison .computedDependency
        stringTarget := { field := label.id, path := [2] }
        stringOutcome := .poison .computedDependency }] := by
  native_decide

/- The checked row chain must start from the aggregate, own two new targets, and keep both targets out of every prefix dependency. -/
example :
    (do
      let cascade ← cascade?
      let suffix ← checkedRowChain? allocation.id (parent "Other")
        final.id (bare "Allocation")
      match checkRepeatableNumberAggregateRowChain cascade suffix with
      | .error (.missingAggregateDependency expected actual) =>
          some (expected, actual)
      | _ => none) = some (total.id, other.id) ∧
    (do
      let cascade ← cascade?
      let suffix ← checkedRowChain? allocation.id (parent "Total")
        amount.id (bare "Allocation")
      match checkRepeatableNumberAggregateRowChain cascade suffix with
      | .error (.duplicateTarget field) => some field
      | _ => none) = some amount.id ∧
    (do
      let having := SurfaceCorrelatedHaving.and
        (.compareNumbers .less (innerNumber "Amount") (innerNumber "Price"))
        (.compareNumbers .less (innerNumber "Final") (innerNumber "Price"))
      let cascade ← (checkRepeatableNumberBinaryFilteredAggregateCascade model
        ["Order", "Lines"] amount.id (bare "Qty") (bare "Price") .multiply
        ["Order"] total.id (star "Price") having .sum).toOption
      let suffix ← rowChain?
      match checkRepeatableNumberAggregateRowChain cascade suffix with
      | .error (.cycle field) => some field
      | _ => none) = some final.id := by
  native_decide

/- The completed aggregate enters the first repeatable suffix stage, whose exact row outcomes feed the second stage. -/
example :
    (chainSummary? (decimalCell price.id [2] "20.00" 2000)).map (·.1) =
      some {
        cascade := {
          producer := .binary .multiply
          consumer := .plain
          operation := .sum
          repeatableScope := [30]
          fieldDependencies := [
            (amount.id, [quantity.id, price.id]), (total.id, [amount.id])]
        }
        suffix := {
          structuralGroup := ["Order", "Lines"]
          scope := [30]
          fieldDependencies := [
            (allocation.id, [total.id]), (final.id, [allocation.id])]
        }
      } ∧
    (chainSummary? (decimalCell price.id [2] "20.00" 2000)).map (·.2.1) =
      some (.accepted { unscaled := 8000, scale := 2 }) ∧
    (chainSummary? (decimalCell price.id [2] "20.00" 2000)).map (·.2.2) =
      some [
        { coordinate := 1
          firstTarget := { field := allocation.id, path := [1] }
          firstOutcome := .accepted { unscaled := 8000, scale := 2 }
          secondTarget := { field := final.id, path := [1] }
          secondOutcome := .accepted { unscaled := 8000, scale := 2 } },
        { coordinate := 2
          firstTarget := { field := allocation.id, path := [2] }
          firstOutcome := .accepted { unscaled := 8000, scale := 2 }
          secondTarget := { field := final.id, path := [2] }
          secondOutcome := .accepted { unscaled := 8000, scale := 2 } }] ∧
    (chainSummary? invalidPrice).map (·.2.1) =
      some (.inheritedPoison .computedDependency) ∧
    (chainSummary? invalidPrice).map (·.2.2) = some [
      { coordinate := 1
        firstTarget := { field := allocation.id, path := [1] }
        firstOutcome := .inheritedPoison .computedDependency
        secondTarget := { field := final.id, path := [1] }
        secondOutcome := .inheritedPoison .computedDependency },
      { coordinate := 2
        firstTarget := { field := allocation.id, path := [2] }
        firstOutcome := .inheritedPoison .computedDependency
        secondTarget := { field := final.id, path := [2] }
        secondOutcome := .inheritedPoison .computedDependency }] := by
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
