import A12Kernel.Elaboration.AddressedNumericOperationConsumer

/-! # Addressed numeric-operation Analyze/Transform probe

The bounded probe consumes checked same-scope repeatable conversion, direct Number, root `Abs`, root Round, and field/literal/operand-local-wrapper operand-list extrema. It recovers exact bounded read/write impact, compares transformation-sensitive fingerprints without claiming equivalence, and exercises exact identity as the sole admitted Transform.
-/

namespace A12Kernel.Conformance.AddressedNumericOperationConsumer

open A12Kernel

private def band : FlatFieldDecl := {
  id := 1
  groupPath := ["Order", "Rows"]
  name := "Band"
  policy := { kind := .enumeration }
  enumeration := some {
    storedTokens := ["1.00", "2.00"]
    categories := [{
      name := "Numeric"
      tokens := ["3.00", "4.00"]
    }]
  }
  repeatableScope := [10]
}

private def converted : FlatFieldDecl := {
  id := 2
  groupPath := ["Order", "Rows"]
  name := "Converted"
  policy := { kind := .number { scale := 2, signed := true } }
  numericTargetConstraints := { minFractionalDigits := 2 }
  repeatableScope := [10]
}

private def code : FlatFieldDecl := {
  id := 3
  groupPath := ["Order", "Rows"]
  name := "Code"
  policy := { kind := .string }
  stringPolicy := { maxLength := some 5 }
  repeatableScope := [10]
}

private def selected : FlatFieldDecl := {
  id := 4
  groupPath := ["Order", "Rows"]
  name := "Selected"
  policy := { kind := .number { scale := 0, signed := false } }
  repeatableScope := [10]
}

private def amount : FlatFieldDecl := {
  id := 5
  groupPath := ["Order", "Rows"]
  name := "Amount"
  policy := { kind := .number { scale := 2, signed := true } }
  repeatableScope := [10]
}

private def sameScaleTarget : FlatFieldDecl := {
  amount with id := 6, name := "SameScaleTarget"
}

private def rounded0 : FlatFieldDecl := {
  amount with
    id := 7
    name := "Rounded0"
    policy := { kind := .number { scale := 0, signed := true } }
}

private def rounded1 : FlatFieldDecl := {
  amount with
    id := 8
    name := "Rounded1"
    policy := { kind := .number { scale := 1, signed := true } }
}

private def precise : FlatFieldDecl := {
  amount with
    id := 9
    name := "Precise"
    policy := { kind := .number { scale := 3, signed := true } }
}

private def extremumTarget : FlatFieldDecl := {
  precise with id := 10, name := "ExtremumTarget"
}

private def model : FlatModel := {
  fields := [band, converted, code, selected, amount, sameScaleTarget,
    rounded0, rounded1, precise, extremumTarget]
  repeatableGroups := [{
    level := 10
    path := ["Order", "Rows"]
    repeatability := some 2
  }]
}

private def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

private def storedLeaf? : Option (CheckedAddressedNumericOperation model) := do
  let operation ←
    (checkAddressedFieldValueAsNumber model ["Order", "Rows"]
      converted.id (.direct (bare "Band"))).toOption
  pure (.fieldValueAsNumber operation)

private def categoryLeaf? : Option (CheckedAddressedNumericOperation model) := do
  let operation ←
    (checkAddressedFieldValueAsNumber model ["Order", "Rows"]
      converted.id (.category (bare "Band") "Numeric")).toOption
  pure (.fieldValueAsNumber operation)

private def rangeLeaf? (finish : Nat) :
    Option (CheckedAddressedNumericOperation model) := do
  let operation ←
    (checkAddressedRangeAsNumber model ["Order", "Rows"]
      selected.id (bare "Code") 2 finish).toOption
  pure (.rangeAsNumber operation)

private def numberFieldLeaf? : Option (CheckedAddressedNumericOperation model) := do
  let operation ←
    (checkAddressedNumberField model ["Order", "Rows"]
      sameScaleTarget.id (bare "Amount")).toOption
  pure (.numberField operation)

private def absLeaf? : Option (CheckedAddressedNumericOperation model) := do
  let operation ←
    (checkAddressedNumberAbs model ["Order", "Rows"]
      sameScaleTarget.id (bare "Amount")).toOption
  pure (.abs operation)

private def roundLeaf? (target : FlatFieldDecl)
    (mode : DecimalRoundingMode) (places : RoundingPlaces) :
    Option (CheckedAddressedNumericOperation model) := do
  let operation ←
    (checkAddressedNumberRound model ["Order", "Rows"]
      target.id (bare "Amount") mode places).toOption
  pure (.round operation)

private def extremumLeaf? (op : NumericExtremumOp)
    (target : FlatFieldDecl) (first : String) (rest : List String) :
    Option (CheckedAddressedNumericOperation model) := do
  let operation ←
    (checkAddressedNumberExtremumList model ["Order", "Rows"]
      target.id (bare first) (rest.map bare) op).toOption
  pure (.extremum operation)

private def extremumField (name : String) :
    SurfaceAddressedNumberExtremumOperand :=
  .field (bare name)

private def extremumAbs (name : String) :
    SurfaceAddressedNumberExtremumOperand :=
  .abs (bare name)

private def extremumRound (name : String) (mode : DecimalRoundingMode)
    (places : RoundingPlaces) :
    SurfaceAddressedNumberExtremumOperand :=
  .round (bare name) mode places

private def extremumLiteral (value : Rat) (authoredScale : Int) :
    SurfaceAddressedNumberExtremumOperand :=
  .literal { value, authoredScale }

private def literalExtremumLeaf? (op : NumericExtremumOp)
    (target : FlatFieldDecl)
    (first : SurfaceAddressedNumberExtremumOperand)
    (rest : List SurfaceAddressedNumberExtremumOperand) :
    Option (CheckedAddressedNumericOperation model) := do
  let operation ←
    (checkAddressedNumberExtremumOperands model ["Order", "Rows"]
      target.id first rest op).toOption
  pure (.extremum operation)

private def places0 : RoundingPlaces := ⟨0, by decide⟩
private def places1 : RoundingPlaces := ⟨1, by decide⟩

private structure AnalysisSummary where
  targetField : FieldId
  sourceFields : List FieldId
  scope : List RepeatableLevel
  parameters : AddressedNumericOperationParameters
  deriving Repr, DecidableEq

private def analyzed?
    (leaf : Option (CheckedAddressedNumericOperation model)) :
    Option AnalysisSummary :=
  leaf.map fun checked =>
    let analysis := checked.analyze
    {
      targetField := analysis.targetField
      sourceFields := analysis.sourceFields
      scope := analysis.scope
      parameters := analysis.parameters
    }

private def fingerprintMatch?
    (before after : Option (CheckedAddressedNumericOperation model)) :
    Option AddressedNumericOperationAnalysis := do
  let before ← before
  let after ← after
  before.matchingFingerprint? after

private def targetPolicy?
    (leaf : Option (CheckedAddressedNumericOperation model)) :
    Option NumericTargetPolicy :=
  leaf.map fun checked => checked.analyze.targetPolicy

private structure ImpactSummary where
  storedReadsBand : Bool
  storedReadsConvertedOperand : Bool
  storedReadsConvertedState : Bool
  storedExecutionReadsBand : Bool
  storedExecutionReadsConverted : Bool
  storedWritesConverted : Bool
  rangeReadsCode : Bool
  rangeWritesSelected : Bool
  deriving Repr, DecidableEq

/- Analyze recovers the exact target, source, repeatable scope, selected Enumeration projection, derived scale, and range interval. -/
example :
    analyzed? storedLeaf? =
      some {
        targetField := converted.id
        sourceFields := [band.id]
        scope := [10]
        parameters := .fieldValueAsNumber .stored 2
      } ∧
    analyzed? categoryLeaf? =
      some {
        targetField := converted.id
        sourceFields := [band.id]
        scope := [10]
        parameters := .fieldValueAsNumber (.category "Numeric") 2
      } ∧
    analyzed? (rangeLeaf? 4) =
      some {
        targetField := selected.id
        sourceFields := [code.id]
        scope := [10]
        parameters := .rangeAsNumber 2 4
      } := by
  native_decide

/- Analyze preserves direct, absolute-value, and rounding identity together with each operation's result scale. -/
example :
    analyzed? numberFieldLeaf? =
      some {
        targetField := sameScaleTarget.id
        sourceFields := [amount.id]
        scope := [10]
        parameters := .numberField 2
      } ∧
    analyzed? absLeaf? =
      some {
        targetField := sameScaleTarget.id
        sourceFields := [amount.id]
        scope := [10]
        parameters := .abs 2
      } ∧
    analyzed? (roundLeaf? rounded0 .floor places0) =
      some {
        targetField := rounded0.id
        sourceFields := [amount.id]
        scope := [10]
        parameters := .round .floor 0
      } ∧
    analyzed? (roundLeaf? rounded1 .ceiling places1) =
      some {
        targetField := rounded1.id
        sourceFields := [amount.id]
        scope := [10]
        parameters := .round .ceiling 1
      } := by
  native_decide

/- Extrema expose their authored operation identity, complete ordered source list, and maximum result scale without expression reconstruction. -/
example :
    analyzed? (extremumLeaf? .minimum sameScaleTarget "Amount" []) =
      some {
        targetField := sameScaleTarget.id
        sourceFields := [amount.id]
        scope := [10]
        parameters := .extremum .minimum 2 [.field amount.id]
      } ∧
    analyzed? (extremumLeaf? .maximum extremumTarget "Selected"
        ["Amount", "Precise"]) =
      some {
        targetField := extremumTarget.id
        sourceFields := [selected.id, amount.id, precise.id]
        scope := [10]
        parameters := .extremum .maximum 3
          [.field selected.id, .field amount.id, .field precise.id]
      } := by
  native_decide

/- Analyze retains one immediate literal's exact authored position, value, and syntax-derived scale while field dependencies remain field-only. -/
example :
    analyzed? (literalExtremumLeaf? .minimum extremumTarget
      (extremumField "Selected") [extremumLiteral (5 / 4) 3]) =
      some {
        targetField := extremumTarget.id
        sourceFields := [selected.id]
        scope := [10]
        parameters := .extremum .minimum 3
          [.field selected.id,
            .literal { value := 5 / 4, authoredScale := 3 }]
      } ∧
    analyzed? (literalExtremumLeaf? .minimum extremumTarget
      (extremumLiteral (5 / 4) 3) [extremumField "Selected"]) =
      some {
        targetField := extremumTarget.id
        sourceFields := [selected.id]
        scope := [10]
        parameters := .extremum .minimum 3
          [.literal { value := 5 / 4, authoredScale := 3 },
            .field selected.id]
      } ∧
    analyzed? (literalExtremumLeaf? .maximum extremumTarget
      (extremumField "Selected")
      [extremumField "Amount", extremumLiteral (-5 / 4) 3]) =
      some {
        targetField := extremumTarget.id
        sourceFields := [selected.id, amount.id]
        scope := [10]
        parameters := .extremum .maximum 3
          [.field selected.id, .field amount.id,
            .literal { value := -5 / 4, authoredScale := 3 }]
      } ∧
    analyzed? (literalExtremumLeaf? .maximum extremumTarget
      (extremumField "Selected")
      [extremumLiteral (-5 / 4) 3, extremumField "Amount"]) =
      some {
        targetField := extremumTarget.id
        sourceFields := [selected.id, amount.id]
        scope := [10]
        parameters := .extremum .maximum 3
          [.field selected.id,
            .literal { value := -5 / 4, authoredScale := 3 },
            .field amount.id]
      } := by
  native_decide

/- Analyze retains an operand-local `Abs` independently from a direct read of the same field, while dependencies remain exact fields in authored order. -/
example :
    analyzed? (literalExtremumLeaf? .minimum sameScaleTarget
      (extremumAbs "Amount") [extremumField "Selected"]) =
      some {
        targetField := sameScaleTarget.id
        sourceFields := [amount.id, selected.id]
        scope := [10]
        parameters := .extremum .minimum 2
          [.abs amount.id, .field selected.id]
      } ∧
    fingerprintMatch?
      (literalExtremumLeaf? .minimum sameScaleTarget
        (extremumAbs "Amount") [extremumField "Selected"])
      (literalExtremumLeaf? .minimum sameScaleTarget
        (extremumField "Amount") [extremumField "Selected"]) = none := by
  native_decide

/- Analyze retains operand-local rounding mode, places, position, and exact field dependency. Same-target controls separate both mode and places from otherwise coincident outer metadata. -/
example :
    analyzed? (literalExtremumLeaf? .minimum rounded1
      (extremumRound "Amount" .floor places1)
      [extremumField "Selected"]) =
      some {
        targetField := rounded1.id
        sourceFields := [amount.id, selected.id]
        scope := [10]
        parameters := .extremum .minimum 1
          [.round amount.id .floor 1, .field selected.id]
      } ∧
    fingerprintMatch?
      (literalExtremumLeaf? .minimum rounded1
        (extremumRound "Amount" .floor places1)
        [extremumField "Selected"])
      (literalExtremumLeaf? .minimum rounded1
        (extremumRound "Amount" .ceiling places1)
        [extremumField "Selected"]) = none ∧
    fingerprintMatch?
      (literalExtremumLeaf? .minimum rounded1
        (extremumRound "Amount" .floor places0)
        [extremumLiteral (5 / 4) 1])
      (literalExtremumLeaf? .minimum rounded1
        (extremumRound "Amount" .floor places1)
        [extremumLiteral (5 / 4) 1]) = none := by
  native_decide

/- Operation, source order, and list cardinality remain independently transformation-sensitive. -/
example :
    fingerprintMatch?
      (extremumLeaf? .minimum sameScaleTarget "Amount" [])
      (extremumLeaf? .maximum sameScaleTarget "Amount" []) = none ∧
    fingerprintMatch?
      (extremumLeaf? .minimum sameScaleTarget "Selected" ["Amount"])
      (extremumLeaf? .minimum sameScaleTarget "Amount" ["Selected"]) = none ∧
    fingerprintMatch?
      (extremumLeaf? .minimum sameScaleTarget "Selected" ["Amount"])
      (extremumLeaf? .minimum sameScaleTarget "Selected"
        ["Amount", "Rounded1"]) = none := by
  native_decide

/- Literal order and authored scale remain transformation-sensitive even when the selected amount or derived target scale coincides. -/
example :
    fingerprintMatch?
      (literalExtremumLeaf? .minimum extremumTarget
        (extremumField "Selected") [extremumLiteral (5 / 4) 3])
      (literalExtremumLeaf? .minimum extremumTarget
        (extremumLiteral (5 / 4) 3) [extremumField "Selected"]) = none ∧
    fingerprintMatch?
      (literalExtremumLeaf? .minimum extremumTarget
        (extremumField "Precise") [extremumLiteral (5 / 4) 2])
      (literalExtremumLeaf? .minimum extremumTarget
        (extremumField "Precise") [extremumLiteral (5 / 4) 3]) = none := by
  native_decide

/- The impact query distinguishes expression-operand reads, source-relative target-state reads, their complete union, and writes. -/
example :
    (do
      let stored ← storedLeaf?
      let range ← rangeLeaf? 4
      pure ({
        storedReadsBand := stored.readsOperand band.id
        storedReadsConvertedOperand := stored.readsOperand converted.id
        storedReadsConvertedState := stored.readsTargetState converted.id
        storedExecutionReadsBand := stored.readsDuringExecution band.id
        storedExecutionReadsConverted :=
          stored.readsDuringExecution converted.id
        storedWritesConverted := stored.writesTo converted.id
        rangeReadsCode := range.readsOperand code.id
        rangeWritesSelected := range.writesTo selected.id
      } : ImpactSummary)) =
      some ({
        storedReadsBand := true
        storedReadsConvertedOperand := false
        storedReadsConvertedState := true
        storedExecutionReadsBand := true
        storedExecutionReadsConverted := true
        storedWritesConverted := true
        rangeReadsCode := true
        rangeWritesSelected := true
      } : ImpactSummary) := by
  native_decide

/- Equal source, target, scope, target policy, and result scale do not erase operation identity. -/
example :
    fingerprintMatch? numberFieldLeaf? absLeaf? = none ∧
    fingerprintMatch? (roundLeaf? rounded0 .floor places0)
      (roundLeaf? rounded0 .halfUp places0) = none := by
  native_decide

/- The fingerprint retains the exact nondefault target policy instead of merely target identity. -/
example :
    targetPolicy? storedLeaf? = converted.toNumericTargetPolicy? ∧
    targetPolicy? (rangeLeaf? 4) = selected.toNumericTargetPolicy? := by
  native_decide

/- Exact identity matches, while changing only stored/category projection or only the range endpoint does not. Cross-family fingerprints differ too; this Analyze result is not a semantic-equivalence certificate. -/
example :
    (fingerprintMatch? storedLeaf? storedLeaf?).isSome = true ∧
    fingerprintMatch? storedLeaf? categoryLeaf? = none ∧
    fingerprintMatch? (rangeLeaf? 4) (rangeLeaf? 3) = none ∧
    fingerprintMatch? storedLeaf? (rangeLeaf? 4) = none := by
  native_decide

end A12Kernel.Conformance.AddressedNumericOperationConsumer
