import A12Kernel.Elaboration.RepeatableNumberAggregateStringRowCascade
import A12Kernel.Elaboration.RepeatableNumberAggregateRowCascade

/-! # Aggregate-to-repeatable String locks -/

namespace A12Kernel.Conformance.RepeatableNumberAggregateStringRowCascade

open A12Kernel

private def number (id : FieldId) (name : String) (group : GroupPath)
    (scope : List RepeatableLevel := []) : FlatFieldDecl where
  id
  name
  groupPath := group
  repeatableScope := scope
  policy := { kind := .number { scale := 2, signed := true } }
  numericTargetConstraints := { minFractionalDigits := 2 }

private def label : FlatFieldDecl where
  id := 5
  name := "Label"
  groupPath := ["Order", "Lines"]
  repeatableScope := [10]
  policy := { kind := .string }
  stringPolicy := { maxLength := some 15 }

private def siblingNumber :=
  number 6 "SiblingNumber" ["Order", "OtherLines"] [20]

private def siblingLabel : FlatFieldDecl where
  id := 7
  name := "SiblingLabel"
  groupPath := ["Order", "OtherLines"]
  repeatableScope := [20]
  policy := { kind := .string }

private def nestedLabel : FlatFieldDecl where
  id := 8
  name := "NestedLabel"
  groupPath := ["Order", "Lines", "Details"]
  repeatableScope := [10, 30]
  policy := { kind := .string }

private def total := number 1 "Total" ["Order"]
private def other := number 2 "Other" ["Order"]
private def quantity := number 3 "Qty" ["Order", "Lines"] [10]
private def amount := number 4 "Amount" ["Order", "Lines"] [10]

private def model : FlatModel where
  fields := [total, other, quantity, amount, label, siblingNumber,
    siblingLabel, nestedLabel]
  repeatableGroups := [
    {
      level := 10
      path := ["Order", "Lines"]
      repeatability := some 3
    },
    {
      level := 20
      path := ["Order", "OtherLines"]
      repeatability := some 3
    },
    {
      level := 30
      path := ["Order", "Lines", "Details"]
      repeatability := some 3
    }]

private def world : World := { now := { epochMillis := 0 } }

private def prepared :
    PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext world builtinStringPatternCompiler model).toOption.get
    (by native_decide)

private def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

private def parent (field : String) : SurfaceFieldPath :=
  { base := .relative 1, groups := [], field }

private def ancestor (depth : Nat) (field : String) : SurfaceFieldPath :=
  { base := .relative depth, groups := [], field }

private def starAmount : SurfaceStarFieldPath := {
  base := .absolute
  groups := [{ name := "Order" }, { name := "Lines", starred := true }]
  field := "Amount"
}

private def cascade? : Option (CheckedRepeatableNumberAggregateCascade model) :=
  (checkRepeatableNumberAggregateCascade model
    ["Order", "Lines"] amount.id (bare "Qty")
    ["Order"] total.id starAmount .sum).toOption

private def plan? (target : FieldId := label.id)
    (source : SurfaceFieldPath := parent "Total") :
    Option (CheckedRepeatableNumberAggregateStringRowCascade model) := do
  let cascade ← cascade?
  (checkRepeatableNumberAggregateStringRowCascade cascade
    ["Order", "Lines"] target source).toOption

private def decimalCell (field : FieldId) (path : List Nat)
    (stored : String) (unscaled : Int) : ClassifiedCellInput := {
  address := { field, path }
  stored
  raw := .parsed (.num (unscaled / 100))
  numericDecimal := some { unscaled, scale := 2 }
}

private def invalidQuantity : ClassifiedCellInput := {
  address := { field := quantity.id, path := [2] }
  stored := "3.001"
  raw := .rejected .declaredConstraint
}

private def input? (secondQuantity : ClassifiedCellInput) :
    Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := [
      { group := 10, path := [1] },
      { group := 10, path := [2] }]
    cells := [
      decimalCell quantity.id [1] "2.00" 200,
      secondQuantity,
      decimalCell amount.id [1] "10.00" 1000,
      decimalCell amount.id [2] "20.00" 2000,
      decimalCell total.id [] "99.99" 9999,
      decimalCell other.id [] "7.00" 700,
      { address := { field := label.id, path := [1] }
        stored := "1.00", raw := .parsed (.str "1.00") },
      { address := { field := label.id, path := [2] }
        stored := "2.00", raw := .parsed (.str "2.00") }]
  }).toOption

private def summary? (secondQuantity : ClassifiedCellInput) :
    Option (RepeatableNumberAggregateStringRowCascadeAnalysis ×
      NumericTargetOutcome × List (CellAddr × StringTargetOutcome)) := do
  let plan ← plan?
  let input ← input? secondQuantity
  let outcomes ← (plan.execute world prepared.patterns input).toOption
  pure (plan.analyze, outcomes.cascade.aggregate.outcome,
    outcomes.suffix.map fun entry => (entry.targetField, entry.outcome))

/- The completed aggregate renders canonically into every physical String target row instead of exposing the stale root cell. -/
example :
    summary? (decimalCell quantity.id [2] "3.00" 300) = some (
      {
        cascade := {
          producer := .direct
          consumer := .plain
          operation := .sum
          repeatableScope := [10]
          fieldDependencies := [
            (amount.id, [quantity.id]), (total.id, [amount.id])]
        }
        suffixTarget := label.id
        repeatableScope := [10]
        fieldDependencies := [
          (amount.id, [quantity.id]),
          (total.id, [amount.id]),
          (label.id, [total.id])]
      },
      .accepted { unscaled := 500, scale := 2 },
      [
        ({ field := label.id, path := [1] },
          .accepted { text := "5.00", nonempty := by decide }),
        ({ field := label.id, path := [2] },
          .accepted { text := "5.00", nonempty := by decide })]) := by
  native_decide

/- Invalid aggregate state crosses the Number-to-String boundary as cause-blind dependency poison at both exact row addresses. -/
example :
    (summary? invalidQuantity).map (fun result => (result.2.1, result.2.2)) =
      some (
        .inheritedPoison .computedDependency,
        [
          ({ field := label.id, path := [1] },
            .poison .computedDependency),
          ({ field := label.id, path := [2] },
            .poison .computedDependency)]) := by
  native_decide

/- The suffix must read the aggregate and cannot reuse a prefix target. -/
example :
    (match cascade? with
      | some cascade =>
          match checkRepeatableNumberAggregateStringRowCascade cascade
              ["Order", "Lines"] label.id (parent "Other") with
          | .error (.missingAggregateDependency expected actual) =>
              expected == total.id && actual == other.id
          | _ => false
      | none => false) = true ∧
    (match cascade? with
      | some cascade =>
          match checkRepeatableNumberAggregateStringRowCascade cascade
              ["Order", "Lines"] amount.id (parent "Total") with
          | .error (.duplicateTarget field) => field == amount.id
          | _ => false
      | none => false) = true := by
  native_decide

/- Aggregate suffixes are confined to the prefix producer's exact repeatable scope; sibling and deeper scopes are not admitted as accidental schedulers. -/
example :
    (match cascade? with
      | some cascade =>
          match checkRepeatableNumberAggregateStringRowCascade cascade
              ["Order", "OtherLines"] siblingLabel.id (parent "Total") with
          | .error (.scopeMismatch producerScope suffixScope) =>
              producerScope == [10] && suffixScope == [20]
          | _ => false
      | none => false) = true ∧
    (match cascade? with
      | some cascade =>
          match checkRepeatableNumberAggregateRowCascade cascade
              ["Order", "OtherLines"] siblingNumber.id (parent "Total") with
          | .error (.scopeMismatch producerScope suffixScope) =>
              producerScope == [10] && suffixScope == [20]
          | _ => false
      | none => false) = true ∧
    (match cascade? with
      | some cascade =>
          match checkRepeatableNumberAggregateStringRowCascade cascade
              ["Order", "Lines", "Details"] nestedLabel.id
                (ancestor 2 "Total") with
          | .error (.scopeMismatch producerScope suffixScope) =>
              producerScope == [10] && suffixScope == [10, 30]
          | _ => false
      | none => false) = true := by
  native_decide

/- The suffix target cannot close a back edge into a field read by the aggregate prefix. -/
example :
    (match cascade? with
      | some cascade =>
          match checkRepeatableNumberAggregateStringRowCascade cascade
              ["Order", "Lines"] quantity.id (parent "Total") with
          | .error (.cycle field) => field == quantity.id
          | _ => false
      | none => false) = true := by
  native_decide

end A12Kernel.Conformance.RepeatableNumberAggregateStringRowCascade
