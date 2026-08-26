import A12Kernel.Elaboration.RepeatableNumberAggregateCascade

/-! # Enumeration-category conversion rows before a root Number aggregate

The matrix composes the existing checked addressed `FieldValueAsNumber` evaluator with the established rows-before-aggregate boundary.
-/

namespace A12Kernel.Conformance.RepeatableNumberAggregateFieldValueAsNumberProducer

open A12Kernel

private def band : FlatFieldDecl := {
  id := 1
  groupPath := ["Order", "Lines"]
  name := "Band"
  policy := { kind := .enumeration }
  enumeration := some {
    storedTokens := ["1", "2", "3"]
    categories := [{
      name := "Numeric"
      tokens := [".50", "-1.25", "2.00"]
    }]
  }
  repeatableScope := [10]
}

private def number (id : FieldId) (name : String) (groupPath : GroupPath)
    (scope : List RepeatableLevel) (scale : Nat := 2) : FlatFieldDecl := {
  id, name, groupPath, repeatableScope := scope
  policy := { kind := .number { scale, signed := true } }
  numericTargetConstraints := { minFractionalDigits := scale }
}

private def produced := number 2 "Produced" ["Order", "Lines"] [10]
private def total := number 3 "Total" ["Order"] []
private def wrong := number 4 "Wrong" ["Order", "Lines"] [10]
private def scale0Produced :=
  number 5 "Scale0Produced" ["Order", "Lines"] [10] 0

private def model : FlatModel := {
  fields := [band, produced, total, wrong, scale0Produced]
  repeatableGroups := [{
    level := 10
    path := ["Order", "Lines"]
    repeatability := some 4
  }]
}

private def prepared :
    PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

private def star (field : String) : SurfaceStarFieldPath := {
  base := .absolute
  groups := [{ name := "Order" }, { name := "Lines", starred := true }]
  field
}

private def soleStar (field : String) : SurfaceNumberEntitySource := {
  first := .star (star field)
  rest := []
}

private def categorySource (name : String) : SurfaceTextFieldOperand :=
  .category (bare "Band") name

private def cascade? :=
  (checkRepeatableFieldValueAsNumberStarListAggregateCascade model
    ["Order", "Lines"] produced.id (categorySource "Numeric")
    ["Order"] total.id (soleStar "Produced") .sum).toOption

private def enumerationCell (row : Nat) (token : String) :
    ClassifiedCellInput := {
  address := { field := band.id, path := [row] }
  stored := token
  raw := .parsed (.enum token)
}

private def numberCell (field : FieldId) (path : List Nat)
    (unscaled : Int) : ClassifiedCellInput := {
  address := { field, path }
  stored := StoredNumber.render { unscaled, scale := 2 }
  raw := .parsed (.num (unscaled / 100))
  numericDecimal := some { unscaled, scale := 2 }
}

private def input? (secondBand : Option ClassifiedCellInput) :
    Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := [
      { group := 10, path := [1] },
      { group := 10, path := [2] }]
    cells := [
      enumerationCell 1 "1",
      numberCell produced.id [1] 9900,
      numberCell produced.id [2] 8800,
      numberCell total.id [] 7700
    ] ++ secondBand.toList
  }).toOption

private structure Snapshot where
  rows : List NumericTargetOutcome
  aggregate : NumericTargetOutcome
  deriving Repr, DecidableEq

private def snapshot? (input : Option (CheckedDocument model)) : Option Snapshot := do
  let plan ← cascade?
  let checked ← input
  let outcomes ← (plan.execute { now := { epochMillis := 0 } } checked).toOption
  pure { rows := outcomes.rows.map (·.outcome), aggregate := outcomes.aggregate.outcome }

private def accepted (unscaled : Int) : NumericTargetOutcome :=
  .accepted { unscaled, scale := 2 }

private def expectedAnalysis : RepeatableNumberAggregateCascadeAnalysis := {
  producer := .fieldValueAsNumber (.category "Numeric")
  consumer := .plain
  operation := .sum
  repeatableScope := [10]
  fieldDependencies := [
    (produced.id, [band.id]),
    (total.id, [produced.id])]
}

private def producerMetadataMatches
    (plan : CheckedRepeatableNumberAggregateCascade model) : Bool :=
  plan.row.targetField == produced.id &&
    plan.row.targetDeclaration.id == produced.id &&
    plan.row.declaringGroup == produced.groupPath &&
    plan.row.targetDeclaration.repeatableScope == produced.repeatableScope

/- Analyze retains conversion and category identity, the typed source edge, and exact target placement. -/
example :
    cascade?.map CheckedRepeatableNumberAggregateCascade.analyze =
      some expectedAnalysis ∧
    cascade?.map producerMetadataMatches = some true := by
  native_decide

/- Category values replace stale row targets before aggregation; absence and poison retain the addressed conversion semantics. -/
example :
    snapshot? (input? (some (enumerationCell 2 "2"))) = some {
      rows := [accepted 50, accepted (-125)]
      aggregate := accepted (-75)
    } ∧
    snapshot? (input? none) = some {
      rows := [accepted 50, accepted 0]
      aggregate := accepted 50
    } ∧
    snapshot? (input? (some (enumerationCell 2 "BOGUS"))) = some {
      rows := [accepted 50, .inheritedPoison .declaredConstraint]
      aggregate := .inheritedPoison .computedDependency
    } := by
  native_decide

/- Conversion admission failures retain their producer tag before aggregate certification. -/
example :
    (match checkRepeatableFieldValueAsNumberStarListAggregateCascade model
        ["Order", "Lines"] produced.id (.direct (bare "Wrong"))
        ["Order"] total.id (soleStar "Produced") .sum with
      | .error (.fieldValueAsNumber
          (.sourceKindMismatch path .number)) => path == wrong.path
      | _ => false) = true ∧
    (match checkRepeatableFieldValueAsNumberStarListAggregateCascade model
        ["Order", "Lines"] scale0Produced.id (categorySource "Numeric")
        ["Order"] total.id (soleStar "Produced") .sum with
      | .error (.fieldValueAsNumber (.scaleMismatch 0 2)) => true
      | _ => false) = true ∧
    (match checkRepeatableFieldValueAsNumberStarListAggregateCascade model
        ["Order", "Lines"] produced.id (categorySource "Missing")
        ["Order"] total.id (soleStar "Produced") .sum with
      | .error (.fieldValueAsNumber (.sourceNotConvertible path)) =>
          path == band.path
      | _ => false) = true := by
  native_decide

end A12Kernel.Conformance.RepeatableNumberAggregateFieldValueAsNumberProducer
