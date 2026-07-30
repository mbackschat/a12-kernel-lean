import A12Kernel.Elaboration.ScalarComputationRun

/-! # Finite mixed scalar computation-run locks

The matrix alternates checked String and Number tables in both directions. It separates typed completed overlays from stale source state, ordinary input reads, reached poison, an unread dependency, and the supplied-order plan gates.
-/

namespace A12Kernel.Conformance.ScalarComputationRun

open A12Kernel

private def inputStringId : FieldId := 0
private def inputNumberId : FieldId := 1
private def firstStringId : FieldId := 2
private def firstNumberId : FieldId := 3
private def secondStringId : FieldId := 4
private def secondNumberId : FieldId := 5
private def gateId : FieldId := 6

private def stringDeclaration (id : FieldId) (name : String)
    (numeric : Bool := false) : FlatFieldDecl where
  id
  groupPath := ["Form"]
  name
  policy := { kind := .string }
  stringPolicy := if numeric then { maxLength := some 15 } else {}
  stringPatternSource := if numeric then some "[0-9]+" else none

private def numberDeclaration (id : FieldId) (name : String) :
    FlatFieldDecl where
  id
  groupPath := ["Form"]
  name
  policy := { kind := .number { scale := 0, signed := true } }

private def model : FlatModel :=
  { fields := [
      stringDeclaration inputStringId "InputString" true,
      numberDeclaration inputNumberId "InputNumber",
      stringDeclaration firstStringId "FirstString" true,
      numberDeclaration firstNumberId "FirstNumber",
      stringDeclaration secondStringId "SecondString",
      numberDeclaration secondNumberId "SecondNumber",
      stringDeclaration gateId "Gate"] }

private def world : World := { now := { epochMillis := 0 } }

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext world builtinStringPatternCompiler model).toOption.get
    (by native_decide)

private def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

private def stringTable? (target : FieldId)
    (rows : List (ComputationCondition × StringExpr SurfaceFieldPath)) :
    Option (CheckedStringComputationTable model) := do
  let alternatives ← rows.mapM fun (guard, expression) => do
    let operation ← (elaborateStringComputationOperation
      model ["Form"] target expression).toOption
    pure ({ precondition := guard, operation } :
      ComputationAlternative (CheckedStringComputationOperation model))
  (certifyStringComputationTable alternatives).toOption

private def numberTable? (target : FieldId)
    (rows : List
      (ComputationCondition × AuthoredNumericExpr SurfaceNumericAtom)) :
    Option (CheckedNumericComputationTable model) := do
  let alternatives ← rows.mapM fun (guard, expression) => do
    let operation ← (elaborateNumericTargetComputationOperation
      model ["Form"] target expression).toOption
    pure ({ precondition := guard, operation } :
      ComputationAlternative
        (CheckedNumericTargetComputationOperation model))
  (certifyNumericComputationTable alternatives).toOption

private def literalNumber (value : Rat) :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .literal { value, authoredScale := 0 }

private def asNumber (field : String) :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.fieldValueAsNumber (.direct (bare field)))

private def holding : ComputationCondition := .fieldNotFilled gateId

private def firstStringValue :=
  (stringTable? firstStringId [(holding, .literal "7")]).get
    (by native_decide)

private def invalidFirstString :=
  (stringTable? firstStringId [(holding, .literal "BAD")]).get
    (by native_decide)

private def firstNumberFromString :=
  (numberTable? firstNumberId [(holding,
    .binary .add (asNumber "FirstString")
      (asNumber "InputString"))]).get (by native_decide)

private def firstNumberFromStringOnly :=
  (numberTable? firstNumberId [(holding,
    asNumber "FirstString")]).get (by native_decide)

private def firstNumberUnreadString :=
  (numberTable? firstNumberId [
    (holding, literalNumber 3),
    (holding, asNumber "FirstString")]).get (by native_decide)

private def secondStringFromNumber :=
  (stringTable? secondStringId [(holding,
    .concat (.fieldValueAsString (bare "FirstNumber"))
      (.concat (.literal "/")
        (.fieldValueAsString (bare "InputNumber"))))]).get
          (by native_decide)

private def secondStringFromNumberOnly :=
  (stringTable? secondStringId [(holding,
    .fieldValueAsString (bare "FirstNumber"))]).get
      (by native_decide)

private def firstNumberValue :=
  (numberTable? firstNumberId [(holding, literalNumber 7)]).get
    (by native_decide)

private def firstStringFromNumber :=
  (stringTable? firstStringId [(holding,
    .fieldValueAsString (bare "FirstNumber"))]).get
      (by native_decide)

private def secondNumberFromString :=
  (numberTable? secondNumberId [(holding,
    .binary .add (asNumber "FirstString")
      (asNumber "InputString"))]).get (by native_decide)

private def stringCell (field : FieldId) (stored : String) :
    ClassifiedCellInput :=
  { address := { field, path := [] }
    stored
    raw := .parsed (.str stored) }

private def numberCell (field : FieldId) (amount : Int) :
    ClassifiedCellInput :=
  { address := { field, path := [] }
    stored := toString amount
    raw := .parsed (.num amount)
    numericDecimal := some { unscaled := amount, scale := 0 } }

private def checkedDocument (cells : List ClassifiedCellInput) :
    Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" { instantiatedRows := [], cells }).toOption

private def outcomes? (steps : List (CheckedScalarComputationStep model))
    (cells : List ClassifiedCellInput := []) :
    Option (List ScalarComputationOutcome) := do
  let run ← (certifyScalarComputationRun steps).toOption
  let input ← checkedDocument cells
  (run.execute world prepared.patterns input).toOption

private def stringNumberString : List (CheckedScalarComputationStep model) :=
  [.string firstStringValue,
    .number firstNumberFromString,
    .string secondStringFromNumber]

private def numberStringNumber : List (CheckedScalarComputationStep model) :=
  [.number firstNumberValue,
    .string firstStringFromNumber,
    .number secondNumberFromString]

/- Both alternating orders consume completed typed values instead of stale target cells, while ordinary String and Number reads stay on the immutable document paths. -/
example :
    outcomes? stringNumberString [
      stringCell inputStringId "2",
      numberCell inputNumberId 4,
      stringCell firstStringId "8",
      numberCell firstNumberId 80,
      stringCell secondStringId "OLD"] =
      some [
        .string firstStringId (.accepted { text := "7", nonempty := by decide }),
        .number firstNumberId (.accepted { unscaled := 9, scale := 0 }),
        .string secondStringId
          (.accepted { text := "9/4", nonempty := by decide })] ∧
    outcomes? numberStringNumber [
      stringCell inputStringId "2",
      numberCell firstNumberId 80,
      stringCell firstStringId "8",
      numberCell secondNumberId 90] =
      some [
        .number firstNumberId (.accepted { unscaled := 7, scale := 0 }),
        .string firstStringId (.accepted { text := "7", nonempty := by decide }),
        .number secondNumberId
          (.accepted { unscaled := 9, scale := 0 })] := by
  native_decide

/- Reached invalidity crosses both family boundaries as cause-blind poison. An earlier selected Number row leaves the same later syntactic conversion unread, so the final String remains valid. -/
example :
    outcomes? [
      .string invalidFirstString,
      .number firstNumberFromStringOnly,
      .string secondStringFromNumberOnly] =
      some [
        .string firstStringId
          (.errored { text := "BAD", nonempty := by decide } .pattern),
        .number firstNumberId
          (.inheritedPoison .computedDependency),
        .string secondStringId (.poison .computedDependency)] ∧
    outcomes? [
      .string invalidFirstString,
      .number firstNumberUnreadString,
      .string secondStringFromNumberOnly] =
      some [
        .string firstStringId
          (.errored { text := "BAD", nonempty := by decide } .pattern),
        .number firstNumberId
          (.accepted { unscaled := 3, scale := 0 }),
        .string secondStringId
          (.accepted { text := "3", nonempty := by decide })] := by
  native_decide

/- Mixed plans require preconsolidated unique targets and backward-only dependencies. -/
example :
    (certifyScalarComputationRun [
      .string firstStringValue,
      .string firstStringValue]).toOption = none ∧
    (certifyScalarComputationRun [
      .number firstNumberFromStringOnly,
      .string firstStringValue]).toOption = none := by
  native_decide

end A12Kernel.Conformance.ScalarComputationRun
