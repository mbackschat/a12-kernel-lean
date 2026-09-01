import A12Kernel.Conformance.NumericComputation.Support

/-! # Checked `Sum` self-validation message growth

This capsule closes the measured one-level plain-star `Sum` carrier. It starts from an elaborated
Number computation and one immutable checked document, then derives the exact growth channel used
to type the target's implicit self-validation message. Filtered, nested, mixed, unbounded, and
formally unavailable sources remain explicit unsupported results.
-/

namespace A12Kernel.Conformance.NumericComputation.SumSelfValidationMessage

open A12Kernel
open A12Kernel.Conformance.NumericComputation.Support

private def boundedModel : FlatModel :=
  { model with
      repeatableGroups := model.repeatableGroups.map fun group =>
        if group.level == 10 then { group with repeatability := some 5 } else group }

private def plainSum :
    AuthoredNumericExpr (SurfaceNumericAtom SurfaceNumberEntitySource) :=
  .atom (.aggregate .sum {
    first := .star repeatedStarPath
    rest := [] })

private def filteredSum :
    AuthoredNumericExpr (SurfaceNumericAtom SurfaceNumberEntitySource) :=
  surfaceRepeatableAggregate .sum

private def directSum :
    AuthoredNumericExpr (SurfaceNumericAtom SurfaceNumberEntitySource) :=
  .atom (.aggregate .sum {
    first := .field (surfacePath ["Root"] "Source")
    rest := [.field (surfacePath ["Root"] "Later")] })

private def world : World := { now := { epochMillis := 0 } }

private def rows (count : Nat) : List RowAddr :=
  (List.range count).map fun index => { group := 10, path := [index + 1] }

private def filledCell (index : Nat) : ClassifiedCellInput := {
  address := { field := repeatedId, path := [index] }
  stored := "1"
  raw := .parsed (.num 1)
}

private def filledCells (count : Nat) : List ClassifiedCellInput :=
  (List.range count).map fun index => filledCell (index + 1)

private def documentData (rowCount filledCount : Nat) : DocumentData := {
  instantiatedRows := rows rowCount
  cells := filledCells filledCount
}

private def malformedData : DocumentData := {
  instantiatedRows := rows 2
  cells := [
    filledCell 1,
    { address := { field := repeatedId, path := [2] }
      stored := "bad"
      raw := .rejected .malformed }]
}

private def growthIn (sourceModel : FlatModel)
    (expression : AuthoredNumericExpr (SurfaceNumericAtom SurfaceNumberEntitySource))
    (data : DocumentData) : Option (Option ComputationOperandGrowth) :=
  match prepareFlatStringContext world builtinStringPatternCompiler sourceModel with
  | .error _ => none
  | .ok prepared =>
      match checkDocument prepared "en_US" data with
      | .error _ => none
      | .ok document =>
          match elaborateNumberEntityComputationOperation
              sourceModel ["Root"] targetId expression with
          | .error _ => none
          | .ok checked =>
              match checked.core.expression with
              | .atom (.numeric (.aggregate .sum source)) =>
                  (source.plainStarSumGrowth? document []).toOption
              | _ => none

private def growth (data : DocumentData) : Option (Option ComputationOperandGrowth) :=
  growthIn boundedModel plainSum data

private def referencedIn (sourceModel : FlatModel)
    (expression : AuthoredNumericExpr (SurfaceNumericAtom SurfaceNumberEntitySource)) :
    Option (Option (List FieldId)) :=
  match elaborateNumberEntityComputationOperation
      sourceModel ["Root"] targetId expression with
  | .error _ => none
  | .ok checked =>
      match checked.core.expression with
      | .atom (.numeric (.aggregate .sum source)) =>
          some (source.plainStarSumReferencedFields? targetId)
      | _ => none

private def verdict (stored computed : Rat) (data : DocumentData) : Option Verdict :=
  match growth data with
  | some (some channel) => some (computedNumberSelfValidation stored computed [channel])
  | _ => none

/- One row of remaining capacity keeps an all-filled sum open; exhausting that row closes it. -/
example :
    growth (documentData 4 4) = some (some (.starredRowValues 4 5 true)) ∧
      growth (documentData 5 5) = some (some (.starredRowValues 5 5 true)) := by
  native_decide

/- At capacity, an empty reached value keeps `Sum` open although no row can be added. -/
example :
    growth (documentData 5 4) = some (some (.starredRowValues 5 5 false)) := by
  native_decide

/- Over-limit rows stay in physical topology but not in the sum's operand extent or growth count. -/
example :
    growth (documentData 7 7) = some (some (.starredRowValues 5 5 true)) := by
  native_decide

/- The checked producer reaches the ordinary directional message rule end to end. -/
example :
    verdict 99 4 (documentData 4 4) = some (.fired .omission) ∧
      verdict 99 5 (documentData 5 5) = some (.fired .value) ∧
      verdict 99 4 (documentData 5 4) = some (.fired .omission) ∧
      verdict 1 3 (documentData 3 3) = some (.fired .value) ∧
      verdict 3 3 (documentData 3 3) = some .notFired := by
  native_decide

/- A reached formal cause suppresses the growth channel instead of masquerading as an empty cell. -/
example : growth malformedData = some none := by
  native_decide

/- The inventory follows the field operand, not its enclosing group: `ProductRight` is a sibling. -/
example :
    referencedIn boundedModel plainSum =
      some (some [repeatedId, targetId]) := by
  native_decide

/- The bounded carrier refuses every shape whose movement rule remains outside the measured profile. -/
example :
    growthIn model plainSum (documentData 3 3) = some none ∧
      growthIn boundedModel filteredSum (documentData 3 3) = some none ∧
      growthIn boundedModel directSum (documentData 0 0) = some none := by
  native_decide

/- Inventory and growth share the exact measured carrier rather than widening independently. -/
example :
    referencedIn model plainSum = some none ∧
      referencedIn boundedModel filteredSum = some none ∧
      referencedIn boundedModel directSum = some none := by
  native_decide

end A12Kernel.Conformance.NumericComputation.SumSelfValidationMessage
