import A12Kernel.Elaboration.RepeatableNumberAggregateCascade

/-! # String-length rows before a root Number aggregate

The matrix composes the existing checked addressed UTF-16 length evaluator with the established rows-before-aggregate boundary.
-/

namespace A12Kernel.Conformance.RepeatableNumberAggregateStringLengthProducer

open A12Kernel

private def text : FlatFieldDecl := {
  id := 1
  groupPath := ["Order", "Lines"]
  name := "Text"
  policy := { kind := .string }
  stringPolicy := { lineBreaksPermitted := true, maxLength := some 8 }
  repeatableScope := [10]
}

private def number (id : FieldId) (name : String) (groupPath : GroupPath)
    (scope : List RepeatableLevel) (scale : Nat := 0) : FlatFieldDecl := {
  id, name, groupPath, repeatableScope := scope
  policy := { kind := .number { scale, signed := false } }
}

private def produced := number 2 "Produced" ["Order", "Lines"] [10]
private def total := number 3 "Total" ["Order"] []
private def wrong := number 4 "Wrong" ["Order", "Lines"] [10]
private def scaledProduced :=
  number 5 "ScaledProduced" ["Order", "Lines"] [10] 1

private def model : FlatModel := {
  fields := [text, produced, total, wrong, scaledProduced]
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

private def cascade? :=
  (checkRepeatableStringLengthStarListAggregateCascade model
    ["Order", "Lines"] produced.id (bare "Text")
    ["Order"] total.id (soleStar "Produced") .sum).toOption

private def textCell (row : Nat) (stored : String) (raw : RawCell) :
    ClassifiedCellInput := {
  address := { field := text.id, path := [row] }
  stored
  raw
}

private def numberCell (field : FieldId) (path : List Nat) (value : Int) :
    ClassifiedCellInput := {
  address := { field, path }
  stored := toString value
  raw := .parsed (.num value)
}

private def input? (secondText : Option ClassifiedCellInput) :
    Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := [
      { group := 10, path := [1] },
      { group := 10, path := [2] }]
    cells := [
      textCell 1 "A😀B" (.parsed (.str "A😀B")),
      numberCell produced.id [1] 99,
      numberCell produced.id [2] 88,
      numberCell total.id [] 77
    ] ++ secondText.toList
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

private def accepted (value : Int) : NumericTargetOutcome :=
  .accepted { unscaled := value, scale := 0 }

private def expectedAnalysis : RepeatableNumberAggregateCascadeAnalysis := {
  producer := .stringLength, consumer := .plain, operation := .sum
  repeatableScope := [10]
  fieldDependencies := [
    (produced.id, [text.id]),
    (total.id, [produced.id])]
}

private def producerMetadataMatches
    (plan : CheckedRepeatableNumberAggregateCascade model) : Bool :=
  plan.row.targetField == produced.id &&
    plan.row.targetDeclaration.id == produced.id &&
    plan.row.declaringGroup == produced.groupPath &&
    plan.row.targetDeclaration.repeatableScope == produced.repeatableScope

/- Analyze retains String-length identity, the typed source edge, and exact target placement. -/
example :
    cascade?.map CheckedRepeatableNumberAggregateCascade.analyze =
      some expectedAnalysis ∧
    cascade?.map producerMetadataMatches = some true := by
  native_decide

/- UTF-16 length replaces stale row targets before aggregation; absent and malformed text retain zero and poison. -/
example :
    snapshot? (input? (some (textCell 2 "xy" (.parsed (.str "xy"))))) = some {
      rows := [accepted 4, accepted 2]
      aggregate := accepted 6
    } ∧
    snapshot? (input? none) = some {
      rows := [accepted 4, accepted 0]
      aggregate := accepted 4
    } ∧
    snapshot? (input? (some (textCell 2 "bad" (.rejected .malformed)))) = some {
      rows := [accepted 4, .inheritedPoison .malformed]
      aggregate := .inheritedPoison .computedDependency
    } := by
  native_decide

/- String-length admission failures retain their producer tag before aggregate certification. -/
example :
    (match checkRepeatableStringLengthStarListAggregateCascade model
        ["Order", "Lines"] produced.id (bare "Wrong")
        ["Order"] total.id (soleStar "Produced") .sum with
      | .error (.stringLength (.sourceNotEvaluatedString path)) =>
          path == wrong.path
      | _ => false) = true ∧
    (match checkRepeatableStringLengthStarListAggregateCascade model
        ["Order", "Lines"] scaledProduced.id (bare "Text")
        ["Order"] total.id (soleStar "Produced") .sum with
      | .error (.stringLength (.scaleMismatch 1 0)) => true
      | _ => false) = true := by
  native_decide

end A12Kernel.Conformance.RepeatableNumberAggregateStringLengthProducer
