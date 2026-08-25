import A12Kernel.Elaboration.RepeatableNumberAggregateStringRowCascade

/-! # Nested aggregate state round-trip locks -/

namespace A12Kernel.Conformance.RepeatableNumberNestedAggregateCascade

open A12Kernel

private def number (id : FieldId) (name : String) (group : GroupPath)
    (scope : List RepeatableLevel := []) : FlatFieldDecl where
  id
  name
  groupPath := group
  repeatableScope := scope
  policy := { kind := .number { scale := 2, signed := true } }
  numericTargetConstraints := { minFractionalDigits := 2 }

private def nestedPath : GroupPath := ["Shop", "Pricing", "Items"]

private def best := number 1 "Best" ["Shop"]
private def price := number 2 "Price" nestedPath [10, 20]
private def helper := number 3 "Helper" nestedPath [10, 20]

private def label : FlatFieldDecl where
  id := 4
  name := "Label"
  groupPath := nestedPath
  repeatableScope := [10, 20]
  policy := { kind := .string }
  stringPolicy := { maxLength := some 15 }

private def model : FlatModel where
  fields := [best, price, helper, label]
  repeatableGroups := [
    {
      level := 10
      path := ["Shop", "Pricing"]
      repeatability := some 3
    },
    {
      level := 20
      path := nestedPath
      repeatability := some 3
    }]

private def world : World := { now := { epochMillis := 0 } }

private def prepared :
    PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext world builtinStringPatternCompiler model).toOption.get
    (by native_decide)

private def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

private def ancestor (depth : Nat) (field : String) : SurfaceFieldPath :=
  { base := .relative depth, groups := [], field }

private def nestedStar (field : String) : SurfaceStarFieldPath := {
  base := .absolute
  groups := [
    { name := "Shop" },
    { name := "Pricing", starred := true },
    { name := "Items", starred := true }]
  field
}

private def leafOnlyNestedStar (field : String) : SurfaceStarFieldPath := {
  base := .absolute
  groups := [
    { name := "Shop" },
    { name := "Pricing" },
    { name := "Items", starred := true }]
  field
}

private def cascade? : Option (CheckedRepeatableNumberAggregateCascade model) :=
  (checkRepeatableNumberAggregateCascade model
    nestedPath helper.id (bare "Price")
    ["Shop"] best.id (nestedStar "Helper") .maximum).toOption

private def plan? :
    Option (CheckedRepeatableNumberAggregateStringRowCascade model) := do
  let cascade ← cascade?
  (checkRepeatableNumberAggregateStringRowCascade cascade
    nestedPath label.id (ancestor 2 "Best")).toOption

private def decimalCell (field : FieldId) (path : List Nat)
    (stored : String) (unscaled : Int) : ClassifiedCellInput := {
  address := { field, path }
  stored
  raw := .parsed (.num (unscaled / 100))
  numericDecimal := some { unscaled, scale := 2 }
}

private def invalidPrice : ClassifiedCellInput := {
  address := { field := price.id, path := [1, 2] }
  stored := "4.001"
  raw := .rejected .declaredConstraint
}

private inductive ObservedStringOutcome where
  | noValue
  | accepted (text : String)
  | errored (attempted : String) (cause : StringTargetError)
  | poison (cause : FormalCause)
  deriving Repr, DecidableEq

private def observeString : StringTargetOutcome → ObservedStringOutcome
  | .noValue => .noValue
  | .accepted value => .accepted value.text
  | .errored attempted cause => .errored attempted.text cause
  | .poison cause => .poison cause

private structure NestedSummary where
  analysis : RepeatableNumberAggregateStringRowCascadeAnalysis
  rows : List (CellAddr × NumericTargetOutcome)
  aggregate : NumericTargetOutcome
  suffix : List (CellAddr × ObservedStringOutcome)
  deriving Repr, DecidableEq

private def input? (middlePrice : ClassifiedCellInput) :
    Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := [
      { group := 10, path := [1] },
      { group := 10, path := [2] },
      { group := 20, path := [1, 1] },
      { group := 20, path := [2, 1] },
      { group := 20, path := [1, 2] }]
    cells := [
      decimalCell price.id [1, 1] "1.00" 100,
      decimalCell price.id [2, 1] "9.00" 900,
      middlePrice,
      decimalCell helper.id [1, 1] "71.00" 7100,
      decimalCell helper.id [2, 1] "72.00" 7200,
      decimalCell helper.id [1, 2] "73.00" 7300,
      decimalCell best.id [] "99.99" 9999,
      { address := { field := label.id, path := [1, 1] }
        stored := "71.00", raw := .parsed (.str "71.00") },
      { address := { field := label.id, path := [2, 1] }
        stored := "72.00", raw := .parsed (.str "72.00") },
      { address := { field := label.id, path := [1, 2] }
        stored := "73.00", raw := .parsed (.str "73.00") }]
  }).toOption

private def summary? (middlePrice : ClassifiedCellInput) :
    Option NestedSummary := do
  let plan ← plan?
  let input ← input? middlePrice
  let outcomes ← (plan.execute world prepared.patterns input).toOption
  pure {
    analysis := plan.analyze
    rows := outcomes.cascade.rows.map fun row =>
      (row.targetField, row.outcome)
    aggregate := outcomes.cascade.aggregate.outcome
    suffix := outcomes.suffix.map fun row =>
      (row.targetField, observeString row.outcome)
  }

/- Analyze and Execute retain both nested coordinates while fresh row state crosses the root aggregate and fans back to every exact leaf. -/
example :
    summary? (decimalCell price.id [1, 2] "4.00" 400) = some {
      analysis := {
        cascade := {
          producer := .direct
          consumer := .plain
          operation := .maximum
          repeatableScope := [10, 20]
          fieldDependencies := [
            (helper.id, [price.id]), (best.id, [helper.id])]
        }
        suffixTarget := label.id
        repeatableScope := [10, 20]
        fieldDependencies := [
          (helper.id, [price.id]),
          (best.id, [helper.id]),
          (label.id, [best.id])]
      }
      rows := [
        ({ field := helper.id, path := [1, 1] },
          .accepted { unscaled := 100, scale := 2 }),
        ({ field := helper.id, path := [2, 1] },
          .accepted { unscaled := 900, scale := 2 }),
        ({ field := helper.id, path := [1, 2] },
          .accepted { unscaled := 400, scale := 2 })]
      aggregate := .accepted { unscaled := 900, scale := 2 }
      suffix := [
        ({ field := label.id, path := [1, 1] },
          .accepted "9.00"),
        ({ field := label.id, path := [2, 1] },
          .accepted "9.00"),
        ({ field := label.id, path := [1, 2] },
          .accepted "9.00")]
    } := by
  native_decide

/- One invalid nested producer poisons the root aggregate and every reached String suffix row without erasing the exact leaf addresses. -/
example :
    (summary? invalidPrice).map (fun result =>
      (result.aggregate, result.suffix)) =
      some (
        .inheritedPoison .computedDependency,
        [
          ({ field := label.id, path := [1, 1] },
            .poison .computedDependency),
          ({ field := label.id, path := [2, 1] },
            .poison .computedDependency),
          ({ field := label.id, path := [1, 2] },
            .poison .computedDependency)]) := by
  native_decide

/- A root aggregate cannot leave an outer repeatable level bound by a surrounding environment that does not exist. -/
example :
    (match checkRepeatableNumberAggregateCascade model
        nestedPath helper.id (bare "Price")
        ["Shop"] best.id (leafOnlyNestedStar "Helper") .maximum with
      | .error (.aggregateBindingRequired levels) => levels == [10]
      | _ => false) = true := by
  native_decide

end A12Kernel.Conformance.RepeatableNumberNestedAggregateCascade
