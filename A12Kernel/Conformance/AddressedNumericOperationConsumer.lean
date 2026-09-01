import A12Kernel.Elaboration.AddressedNumericOperationConsumer

/-! # Addressed numeric-operation Analyze/Transform probe

The bounded probe consumes checked repeatable conversion, direct Number, root `Abs`, root Round, and field/literal/operand-local-wrapper/one-level-nested operand-list extrema, including division and power children. It recovers exact bounded read/write impact, compares transformation-sensitive fingerprints without claiming equivalence, and exercises exact identity as the sole admitted Transform.
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

private def extremumAddition (left right : String) :
    SurfaceAddressedNumberExtremumOperand :=
  .arithmetic .add (.field (bare left)) (.field (bare right))

private def extremumSubtraction (left right : String) :
    SurfaceAddressedNumberExtremumOperand :=
  .arithmetic .subtract (.field (bare left)) (.field (bare right))

private def extremumMultiplication (left right : String) :
    SurfaceAddressedNumberExtremumOperand :=
  .arithmetic .multiply (.field (bare left)) (.field (bare right))

private def extremumDivision (left right : String) :
    SurfaceAddressedNumberExtremumOperand :=
  .division (.field (bare left)) (.field (bare right))

private def extremumPower (base exponent : String) :
    SurfaceAddressedNumberExtremumOperand :=
  .power
    (.field (bare base))
    (.field (bare exponent))

/-- One product whose right operand is an immediate literal carrying its own authored scale. Identity-Transform preservation is not rechecked per case: `identityTransform_analyze` owns it universally. -/
private def extremumMultiplicationLiteral (left : String)
    (value : Rat) (authoredScale : Int) :
    SurfaceAddressedNumberExtremumOperand :=
  .arithmetic .multiply (.field (bare left)) (.literal { value, authoredScale })

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

private def suppressedExtremumLeaf? (op : NumericExtremumOp)
    (target : FlatFieldDecl)
    (first : SurfaceAddressedNumberExtremumOperand)
    (rest : List SurfaceAddressedNumberExtremumOperand) :
    Option (CheckedAddressedNumericOperation model) := do
  let operation ←
    (checkAddressedNumberExtremumOperands model ["Order", "Rows"] target.id
      first rest op (suppressExactScaleWarning := true)).toOption
  pure (.extremum operation)

private def places0 : RoundingPlaces := ⟨0, by decide⟩
private def places1 : RoundingPlaces := ⟨1, by decide⟩

private def nestedAbs (name : String) : SurfaceAddressedNumberExtremumLeaf :=
  .abs (bare name)

private def nestedRound (name : String) (mode : DecimalRoundingMode)
    (places : RoundingPlaces) : SurfaceAddressedNumberExtremumLeaf :=
  .round (bare name) mode places

private def nestedArithmetic (op : NumericArithmeticOp) (left right : String) :
    SurfaceAddressedNumberExtremumLeaf :=
  .arithmetic op (.field (bare left)) (.field (bare right))

private def nestedDivision (left right : String) :
    SurfaceAddressedNumberExtremumLeaf :=
  .division (.field (bare left)) (.field (bare right))

private def nestedPower (base exponent : String) :
    SurfaceAddressedNumberExtremumLeaf :=
  .power (.field (bare base)) (.field (bare exponent))

/-- One constant-only product: an operand that reads no field, so a list of only these references nothing at all. -/
private def extremumConstantProduct (left right : Rat)
    (leftScale rightScale : Int) : SurfaceAddressedNumberExtremumOperand :=
  .arithmetic .multiply
    (.literal { value := left, authoredScale := leftScale })
    (.literal { value := right, authoredScale := rightScale })

private def admittedScales?
    (leaf : Option (CheckedAddressedNumericOperation model)) :
    Option (List Nat) :=
  leaf.map fun checked => checked.analyze.admittedTargetScales

private structure AnalysisSummary where
  targetField : FieldId
  sourceFields : List FieldId
  scope : List RepeatableLevel
  suppressExactScaleWarning : Bool := false
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
      suppressExactScaleWarning := analysis.suppressExactScaleWarning
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
        parameters := .extremum .minimum { scale := .exact 2, canExpandScale := false } [.field amount.id]
      } ∧
    analyzed? (extremumLeaf? .maximum extremumTarget "Selected"
        ["Amount", "Precise"]) =
      some {
        targetField := extremumTarget.id
        sourceFields := [selected.id, amount.id, precise.id]
        scope := [10]
        parameters := .extremum .maximum
          { scale := .exact 3, canExpandScale := false }
          [.field selected.id, .field amount.id, .field precise.id]
      } ∧
    analyzed? (literalExtremumLeaf? .minimum sameScaleTarget
      (.extremum .maximum (.field (bare "Amount"))
        [.literal { value := 1, authoredScale := 0 }, .field (bare "Converted")]) []) =
      some {
        targetField := sameScaleTarget.id
        sourceFields := [amount.id, converted.id]
        scope := [10]
        parameters := .extremum .minimum
          { scale := .exact 2, canExpandScale := false }
          [.extremum .maximum
            [.field amount.id, .literal { value := 1, authoredScale := 0 }, .field converted.id]]
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
        parameters := .extremum .minimum
          { scale := .exact 3, canExpandScale := false }
          [.field selected.id,
            .literal { value := 5 / 4, authoredScale := 3 }]
      } ∧
    analyzed? (literalExtremumLeaf? .minimum extremumTarget
      (extremumLiteral (5 / 4) 3) [extremumField "Selected"]) =
      some {
        targetField := extremumTarget.id
        sourceFields := [selected.id]
        scope := [10]
        parameters := .extremum .minimum
          { scale := .exact 3, canExpandScale := false }
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
        parameters := .extremum .maximum
          { scale := .exact 3, canExpandScale := false }
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
        parameters := .extremum .maximum
          { scale := .exact 3, canExpandScale := false }
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
        parameters := .extremum .minimum
          { scale := .exact 2, canExpandScale := false }
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
        parameters := .extremum .minimum
          { scale := .exact 1, canExpandScale := false }
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

/- Analyze retains addition as one outer operand while flattening its two ordered dependencies. Inner order, outer position, and operation identity remain independently transformation-sensitive. -/
example :
    analyzed? (literalExtremumLeaf? .minimum sameScaleTarget
      (extremumAddition "Amount" "Selected")
      [extremumField "Converted"]) =
      some {
        targetField := sameScaleTarget.id
        sourceFields := [amount.id, selected.id, converted.id]
        scope := [10]
        parameters := .extremum .minimum
          { scale := .exact 2, canExpandScale := false }
          [.arithmetic .add (.field amount.id) (.field selected.id), .field converted.id]
      } ∧
    fingerprintMatch?
      (literalExtremumLeaf? .minimum sameScaleTarget
        (extremumAddition "Amount" "Selected")
        [extremumField "Converted"])
      (literalExtremumLeaf? .minimum sameScaleTarget
        (extremumAddition "Selected" "Amount")
        [extremumField "Converted"]) = none ∧
    fingerprintMatch?
      (literalExtremumLeaf? .minimum sameScaleTarget
        (extremumAddition "Amount" "Selected")
        [extremumField "Converted"])
      (literalExtremumLeaf? .minimum sameScaleTarget
        (extremumField "Converted")
        [extremumAddition "Amount" "Selected"]) = none := by
  native_decide

/- Analyze and identity Transform retain subtraction as distinct from addition while preserving both ordered dependencies, outer position, and derived scale. -/
example :
    analyzed? (literalExtremumLeaf? .minimum sameScaleTarget
      (extremumSubtraction "Amount" "Selected")
      [extremumField "Converted"]) =
      some {
        targetField := sameScaleTarget.id
        sourceFields := [amount.id, selected.id, converted.id]
        scope := [10]
        parameters := .extremum .minimum
          { scale := .exact 2, canExpandScale := false }
          [.arithmetic .subtract (.field amount.id) (.field selected.id), .field converted.id]
      } ∧
    fingerprintMatch?
      (literalExtremumLeaf? .minimum sameScaleTarget
        (extremumSubtraction "Amount" "Selected")
        [extremumField "Converted"])
      (literalExtremumLeaf? .minimum sameScaleTarget
        (extremumAddition "Amount" "Selected")
        [extremumField "Converted"]) = none := by
  native_decide

/- Multiplication is the separator that operation identity alone must carry: over a scale-2 and a scale-0 source it derives the same outer scale 2 as addition, so an account that kept only dependencies, order, and derived scale would conflate the two. Identity Transform preserves the product node exactly. -/
example :
    analyzed? (literalExtremumLeaf? .minimum sameScaleTarget
      (extremumMultiplication "Amount" "Selected")
      [extremumField "Converted"]) =
      some {
        targetField := sameScaleTarget.id
        sourceFields := [amount.id, selected.id, converted.id]
        scope := [10]
        parameters := .extremum .minimum
          { scale := .exact 2, canExpandScale := false }
          [.arithmetic .multiply (.field amount.id) (.field selected.id), .field converted.id]
      } ∧
    fingerprintMatch?
      (literalExtremumLeaf? .minimum sameScaleTarget
        (extremumMultiplication "Amount" "Selected")
        [extremumField "Converted"])
      (literalExtremumLeaf? .minimum sameScaleTarget
        (extremumAddition "Amount" "Selected")
        [extremumField "Converted"]) = none ∧
    fingerprintMatch?
      (literalExtremumLeaf? .minimum sameScaleTarget
        (extremumMultiplication "Amount" "Selected")
        [extremumField "Converted"])
      (literalExtremumLeaf? .minimum sameScaleTarget
        (extremumMultiplication "Selected" "Amount")
        [extremumField "Converted"]) = none ∧
    fingerprintMatch?
      (literalExtremumLeaf? .minimum sameScaleTarget
        (extremumMultiplication "Amount" "Selected")
        [extremumField "Converted"])
      (literalExtremumLeaf? .minimum sameScaleTarget
        (extremumField "Converted")
        [extremumMultiplication "Amount" "Selected"]) = none := by
  native_decide

/- Analyze retains division rather than flattening it into ordinary arithmetic, preserves its ordered dependencies and unknown scale, and carries the authored warning suppression into the only target-scale decision procedure. -/
example :
    analyzed? (suppressedExtremumLeaf? .minimum rounded0
      (extremumDivision "Amount" "Selected")
      [extremumLiteral 3 0]) =
      some {
        targetField := rounded0.id
        sourceFields := [amount.id, selected.id]
        scope := [10]
        suppressExactScaleWarning := true
        parameters := .extremum .minimum
          { scale := .unknown, canExpandScale := false }
          [.division (.field amount.id) (.field selected.id),
            .literal { value := 3, authoredScale := 0 }]
      } ∧
    admittedScales? (suppressedExtremumLeaf? .minimum rounded0
      (extremumDivision "Amount" "Selected")
      [extremumLiteral 3 0]) = some (List.range 15) := by
  native_decide

/- Analyze retains power, both ordered field dependencies, unknown derived scale, and warning suppression. A division over the same fields cannot share its fingerprint. -/
example :
    analyzed? (suppressedExtremumLeaf? .minimum rounded0
      (extremumPower "Amount" "Selected") [extremumLiteral 3 0]) =
      some {
        targetField := rounded0.id
        sourceFields := [amount.id, selected.id]
        scope := [10]
        suppressExactScaleWarning := true
        parameters := .extremum .minimum
          { scale := .unknown, canExpandScale := false }
          [.power (.field amount.id) (.field selected.id),
            .literal { value := 3, authoredScale := 0 }]
      } := by
  native_decide

/- Analyze retains nested wrapper identity and leaf order rather than flattening the child into outer operands. -/
example :
    analyzed? (literalExtremumLeaf? .minimum sameScaleTarget
      (.extremum .minimum (nestedAbs "Amount")
        [nestedRound "Selected" .floor places0])
      [extremumField "Converted"]) =
      some {
        targetField := sameScaleTarget.id
        sourceFields := [amount.id, selected.id, converted.id]
        scope := [10]
        parameters := .extremum .minimum
          { scale := .exact 2, canExpandScale := false }
          [.extremum .minimum
            [.abs amount.id, .round selected.id .floor 0],
            .field converted.id]
      } ∧
    analyzed? (literalExtremumLeaf? .minimum sameScaleTarget
      (.extremum .minimum (nestedAbs "Amount")
        [nestedRound "Selected" .ceiling places1])
      [extremumField "Converted"]) =
      some {
        targetField := sameScaleTarget.id
        sourceFields := [amount.id, selected.id, converted.id]
        scope := [10]
        parameters := .extremum .minimum
          { scale := .exact 2, canExpandScale := false }
          [.extremum .minimum
            [.abs amount.id, .round selected.id .ceiling 1],
            .field converted.id]
      } ∧
    fingerprintMatch?
      (literalExtremumLeaf? .minimum sameScaleTarget
        (.extremum .minimum (nestedAbs "Amount")
          [nestedRound "Selected" .floor places0])
        [extremumField "Converted"])
      (literalExtremumLeaf? .minimum sameScaleTarget
        (.extremum .minimum (nestedAbs "Amount")
          [nestedRound "Selected" .ceiling places1])
        [extremumField "Converted"]) = none ∧
    (analyzed? (literalExtremumLeaf? .minimum sameScaleTarget
      (.extremum .minimum (nestedRound "Selected" .floor places0)
        [nestedAbs "Amount"])
      [extremumField "Converted"])).isSome = true ∧
    fingerprintMatch?
      (literalExtremumLeaf? .minimum sameScaleTarget
        (.extremum .minimum (nestedAbs "Amount")
          [nestedRound "Selected" .floor places0])
        [extremumField "Converted"])
      (literalExtremumLeaf? .minimum sameScaleTarget
        (.extremum .minimum (nestedRound "Selected" .floor places0)
          [nestedAbs "Amount"])
        [extremumField "Converted"]) = none := by
  native_decide

/- Analyze keeps an arithmetic leaf inside the nested selector and distinguishes its ordered children without flattening either call. -/
example :
    analyzed? (literalExtremumLeaf? .minimum sameScaleTarget
      (.extremum .minimum
        (nestedArithmetic .subtract "Selected" "Amount")
        [.literal { value := 0, authoredScale := 0 }])
      [extremumField "Converted"]) =
      some {
        targetField := sameScaleTarget.id
        sourceFields := [selected.id, amount.id, converted.id]
        scope := [10]
        parameters := .extremum .minimum
          { scale := .exact 2, canExpandScale := false }
          [.extremum .minimum
            [.arithmetic .subtract (.field selected.id) (.field amount.id),
              .literal { value := 0, authoredScale := 0 }],
            .field converted.id]
      } ∧
    (analyzed? (literalExtremumLeaf? .minimum sameScaleTarget
      (.extremum .minimum
        (nestedArithmetic .subtract "Amount" "Selected")
        [.literal { value := 0, authoredScale := 0 }])
      [extremumField "Converted"])).isSome = true ∧
    fingerprintMatch?
      (literalExtremumLeaf? .minimum sameScaleTarget
        (.extremum .minimum
          (nestedArithmetic .subtract "Selected" "Amount")
          [.literal { value := 0, authoredScale := 0 }])
        [extremumField "Converted"])
      (literalExtremumLeaf? .minimum sameScaleTarget
        (.extremum .minimum
          (nestedArithmetic .subtract "Amount" "Selected")
          [.literal { value := 0, authoredScale := 0 }])
        [extremumField "Converted"]) = none := by
  native_decide

/- Analyze keeps nested division and power as distinct complete leaves with the same ordered dependencies and outer structure. -/
example :
    analyzed? (suppressedExtremumLeaf? .minimum rounded0
      (.extremum .minimum (nestedDivision "Amount" "Selected")
        [.literal { value := 3, authoredScale := 0 }])
      [extremumField "Converted"]) =
      some {
        targetField := rounded0.id
        sourceFields := [amount.id, selected.id, converted.id]
        scope := [10]
        suppressExactScaleWarning := true
        parameters := .extremum .minimum
          { scale := .unknown, canExpandScale := false }
          [.extremum .minimum
            [.division (.field amount.id) (.field selected.id),
              .literal { value := 3, authoredScale := 0 }],
            .field converted.id]
      } ∧
    analyzed? (suppressedExtremumLeaf? .minimum rounded0
      (.extremum .minimum (nestedPower "Amount" "Selected")
        [.literal { value := 3, authoredScale := 0 }])
      [extremumField "Converted"]) =
      some {
        targetField := rounded0.id
        sourceFields := [amount.id, selected.id, converted.id]
        scope := [10]
        suppressExactScaleWarning := true
        parameters := .extremum .minimum
          { scale := .unknown, canExpandScale := false }
          [.extremum .minimum
            [.power (.field amount.id) (.field selected.id),
              .literal { value := 3, authoredScale := 0 }],
            .field converted.id]
      } ∧
    fingerprintMatch?
      (suppressedExtremumLeaf? .minimum rounded0
        (.extremum .minimum (nestedDivision "Amount" "Selected")
          [.literal { value := 3, authoredScale := 0 }])
        [extremumField "Converted"])
      (suppressedExtremumLeaf? .minimum rounded0
        (.extremum .minimum (nestedPower "Amount" "Selected")
          [.literal { value := 3, authoredScale := 0 }])
        [extremumField "Converted"]) = none := by
  native_decide

/- An inner literal is retained as an operand identity, not folded into the derived scale: two products differing only in the literal's authored scale keep distinct fingerprints even though their values agree, and moving the literal to the other inner position also stays distinct. -/
example :
    analyzed? (literalExtremumLeaf? .minimum sameScaleTarget
      (extremumMultiplicationLiteral "Amount" 1 0)
      [extremumField "Converted"]) =
      some {
        targetField := sameScaleTarget.id
        sourceFields := [amount.id, converted.id]
        scope := [10]
        parameters := .extremum .minimum
          { scale := .exact 2, canExpandScale := false }
          [.arithmetic .multiply (.field amount.id)
            (.literal { value := 1, authoredScale := 0 }), .field converted.id]
      } ∧
    fingerprintMatch?
      (literalExtremumLeaf? .minimum sameScaleTarget
        (extremumMultiplicationLiteral "Amount" 1 0)
        [extremumField "Converted"])
      (literalExtremumLeaf? .minimum sameScaleTarget
        (extremumMultiplication "Amount" "Selected")
        [extremumField "Converted"]) = none := by
  native_decide

/- Consumer probe: a fieldless list reports an empty read set, so a consumer ordering work by dependency must not treat it as depending on anything, while its write target and repeatable scope are unchanged. -/
example :
    analyzed? (literalExtremumLeaf? .minimum rounded1
      (extremumConstantProduct (3 / 2) 2 1 0) []) =
      some {
        targetField := rounded1.id
        sourceFields := []
        scope := [10]
        parameters := .extremum .minimum
          { scale := .exact 1, canExpandScale := true }
          [.arithmetic .multiply
            (.literal { value := 3 / 2, authoredScale := 1 })
            (.literal { value := 2, authoredScale := 0 })]
      } ∧
    ((literalExtremumLeaf? .minimum rounded1
      (extremumConstantProduct (3 / 2) 2 1 0) []).map
        (·.readsOperand amount.id)) = some false := by
  native_decide

/- Consumer probe, the decision the fingerprint must support: two operations with the SAME derived scale 1 admit different declared target scales, because only the constant-only one is capability-carrying. A retargeting consumer reading scale alone would get this wrong; reading the retained summary through the shared gate gets it right. -/
example :
    admittedScales? (literalExtremumLeaf? .minimum rounded1
      (extremumConstantProduct (3 / 2) 2 1 0) []) =
      some [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14] ∧
    admittedScales? (literalExtremumLeaf? .minimum rounded1
      (extremumRound "Amount" .floor places1) []) = some [1] := by
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
