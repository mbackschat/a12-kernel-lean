import A12Kernel.Elaboration.RepeatableNumberAggregateMixedRun

/-! # Aggregate-seeded mixed scalar-run locks -/

namespace A12Kernel.Conformance.RepeatableNumberAggregateMixedRun

open A12Kernel

private def number (id : FieldId) (name : String) (group : GroupPath)
    (scope : List RepeatableLevel := []) : FlatFieldDecl where
  id
  name
  groupPath := group
  repeatableScope := scope
  policy := { kind := .number { scale := 0, signed := true } }

private def numericString (id : FieldId) (name : String) : FlatFieldDecl where
  id
  name
  groupPath := ["Order"]
  policy := { kind := .string }
  stringPolicy := { maxLength := some 15 }
  stringPatternSource := some "[0-9]+"

private def total := number 1 "Total" ["Order"]
private def label := numericString 2 "Label"
private def doubled := number 3 "Doubled" ["Order"]
private def gate := numericString 4 "Gate"
private def quantity := number 5 "Qty" ["Order", "Lines"] [10]
private def amount := number 6 "Amount" ["Order", "Lines"] [10]

private def model : FlatModel where
  fields := [total, label, doubled, gate, quantity, amount]
  repeatableGroups := [{
    level := 10
    path := ["Order", "Lines"]
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

private def starAmount : SurfaceStarFieldPath := {
  base := .absolute
  groups := [{ name := "Order" }, { name := "Lines", starred := true }]
  field := "Amount"
}

private def prefix? (source : SurfaceFieldPath := bare "Qty") :
    Option (CheckedRepeatableNumberAggregateCascade model) :=
  (checkRepeatableNumberAggregateCascade model
    ["Order", "Lines"] amount.id source
    ["Order"] total.id starAmount .sum).toOption

private def stringTable? (target : FieldId)
    (rows : List (ComputationCondition × StringExpr SurfaceFieldPath)) :
    Option (CheckedStringComputationTable model) := do
  let alternatives ← rows.mapM fun (precondition, expression) => do
    let operation ← (elaborateStringComputationOperation
      model ["Order"] target expression).toOption
    pure ({ precondition, operation } :
      ComputationAlternative (CheckedStringComputationOperation model))
  (certifyStringComputationTable alternatives).toOption

private def rootNumber (field : String) :
    AuthoredNumericExpr SurfaceNumericComputationAtom :=
  .atom (.numeric (.field (bare field)))

private def rootAsNumber (field : String) :
    AuthoredNumericExpr SurfaceNumericComputationAtom :=
  .atom (.numeric (.fieldValueAsNumber (.direct (bare field))))

private def numberTable? (target : FieldId)
    (expression : AuthoredNumericExpr SurfaceNumericComputationAtom) :
    Option (CheckedNumericComputationTable model) := do
  let operation ← (elaborateCompleteNumericTargetComputationOperation
    model ["Order"] target expression).toOption
  (certifyNumericComputationTable [{
    precondition := .fieldFilled label.id
    operation
  }]).toOption

private def mixedRun? (consumeAggregate : Bool := true) :
    Option (CheckedScalarComputationRun model) := do
  let string ← stringTable? label.id (if consumeAggregate then [
      (.fieldFilled gate.id, .literal "WRONG"),
      (.fieldNotFilled gate.id, .fieldValueAsString (bare "Total"))]
    else [(.fieldNotFilled gate.id, .literal "7")])
  let number ← numberTable? doubled.id
    (if consumeAggregate then
      .binary .add (rootAsNumber "Label") (rootNumber "Total")
    else rootAsNumber "Label")
  (certifyScalarComputationRun [.string string, .number number]).toOption

private def plan? : Option (CheckedRepeatableNumberAggregateMixedRun model) := do
  let cascade ← prefix?
  let run ← mixedRun?
  (checkRepeatableNumberAggregateMixedRun cascade run).toOption

private def numberCell (field : FieldId) (path : List Nat) (value : Int) :
    ClassifiedCellInput := {
  address := { field, path }
  stored := toString value
  raw := .parsed (.num value)
  numericDecimal := some { unscaled := value, scale := 0 }
}

private def invalidQuantity : ClassifiedCellInput := {
  address := { field := quantity.id, path := [2] }
  stored := "3.1"
  raw := .rejected .declaredConstraint
}

private def input? (secondQuantity : ClassifiedCellInput) :
    Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := [
      { group := 10, path := [1] },
      { group := 10, path := [2] }]
    cells := [
      numberCell quantity.id [1] 2,
      secondQuantity,
      numberCell amount.id [1] 10,
      numberCell amount.id [2] 10,
      numberCell total.id [] 99,
      { address := { field := label.id, path := [] }
        stored := "8", raw := .parsed (.str "8") },
      numberCell doubled.id [] 7]
  }).toOption

private def summary? (secondQuantity : ClassifiedCellInput) := do
  let plan ← plan?
  let input ← input? secondQuantity
  let outcomes ← (plan.execute world prepared.patterns input).toOption
  pure (plan.analyze, outcomes.cascade.aggregate.outcome, outcomes.scalars)

/- The completed aggregate shadows its stale seed for both consumer families. The first false guard falls through, and the supplied suffix order remains visible to Analyze. -/
example :
    summary? (numberCell quantity.id [2] 3) = some (
      {
        cascade := {
          producer := .direct
          consumer := .plain
          operation := .sum
          repeatableScope := [10]
          fieldDependencies := [(amount.id, [quantity.id]), (total.id, [amount.id])]
        }
        scalarTargets := [(.string, label.id), (.number, doubled.id)]
        computedDependencies := [
          (label.id, [total.id]),
          (doubled.id, [total.id, label.id])]
      },
      .accepted { unscaled := 5, scale := 0 },
      [
        .string label.id (.accepted { text := "5", nonempty := by decide }),
        .number doubled.id (.accepted { unscaled := 10, scale := 0 })]) := by
  native_decide

/- Reached aggregate poison crosses Number-to-String and then String-to-Number as cause-blind dependency poison. -/
example :
    (summary? invalidQuantity).map (fun result => (result.2.1, result.2.2)) = some (
      .inheritedPoison .computedDependency,
      [
        .string label.id (.poison .computedDependency),
        .number doubled.id (.inheritedPoison .computedDependency)]) := by
  native_decide

/- The suffix must consume the aggregate, own disjoint targets, and remain absent from every prefix dependency. -/
example :
    (match prefix?, mixedRun? false with
      | some cascade, some run =>
          match checkRepeatableNumberAggregateMixedRun cascade run with
          | .error (.missingAggregateDependency field) => field == total.id
          | _ => false
      | _, _ => false) = true ∧
    (match prefix?, numberTable? total.id (rootAsNumber "Label") with
      | some cascade, some table =>
          match certifyScalarComputationRun [.number table] with
          | .ok run =>
              match checkRepeatableNumberAggregateMixedRun cascade run with
              | .error (.duplicateTarget field) => field == total.id
              | _ => false
          | .error _ => false
      | _, _ => false) = true ∧
    (match prefix? (parent "Doubled"), mixedRun? with
      | some cascade, some run =>
          match checkRepeatableNumberAggregateMixedRun cascade run with
          | .error (.cycle field) => field == doubled.id
          | _ => false
      | _, _ => false) = true := by
  native_decide

end A12Kernel.Conformance.RepeatableNumberAggregateMixedRun
