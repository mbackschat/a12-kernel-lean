import A12Kernel.Elaboration.Correlation

/-! # Numeric expressions inside `Having` filters

A filter body is the ordinary condition production, so a Number field is compared with a literal by
the ordinary operator and the ordinary literal scale gate. The
[filter-leaf grid](../../docs/sources/having-filter-probes.md#src-having-number-leaf-grid) admits all
six operators and a literal on either side, refuses `==` and `!=` whose literal carries more fraction
digits than the field's scale with `MVK_INVALID_COMPARE_DEC_PLACES`, and exempts ordering from that
gate. The cases below lock that admission and the leaf's truth: an empty field compares as zero, a
malformed one is unknown on validation and poison on computation.
-/

namespace A12Kernel.Conformance.HavingNumberLiteral

local instance [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .ok a, .ok b => decidable_of_iff (a = b) (by simp)
  | .error a, .error b => decidable_of_iff (a = b) (by simp)
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

open A12Kernel

private def rows : RepeatableLevel := 10

private def numberField (id : FieldId) (name : String) (scale : Nat) : FlatFieldDecl :=
  { id, groupPath := ["Probe", "Rows"], name, repeatableScope := [rows]
    policy := { kind := .number { scale, signed := true } } }

private def model : FlatModel :=
  { fields := [numberField 0 "V" 0, numberField 1 "W" 2,
      { id := 2, groupPath := ["Probe", "Rows"], name := "S", repeatableScope := [rows]
        policy := { kind := .string } }]
    repeatableGroups := [{ level := rows, path := ["Probe", "Rows"], repeatability := some 5 }] }

private def literal (value : Rat) (authoredScale : Int := 0) : DecodedNumericLiteral :=
  { value, authoredScale }

private def leaf (op : SurfaceComparisonOp) (field : String) (value : DecodedNumericLiteral) :
    SurfaceCorrelatedHaving :=
  .compareNumberLiteral op
    { origin := .inner, field := { base := .absolute, groups := ["Probe", "Rows"], field } } value

/-- Elaborate one filter over `Rows*/V` from the root group. -/
private def checked? (having : SurfaceCorrelatedHaving) :
    Except CorrelationElabError CorrelatedHaving := do
  let star ← (elaborateStarFieldPath model ["Probe"]
    { base := .absolute, groups := [{ name := "Probe" }, { name := "Rows", starred := true }]
      field := "V" }).mapError fun _ => .incoherentCore
  pure (← elaborateStarHavingCore model ["Probe"] star having).condition

private def refusal? (having : SurfaceCorrelatedHaving) : Option CorrelationElabError :=
  match checked? having with
  | .error error => some error
  | .ok _ => none

/- Every operator is admitted against a literal; under `==` and `!=` the literal must fit the field's
scale, counting a written trailing zero, while every ordering operator is exempt; the refusal
projects to the measured class. -/
example :
    [SurfaceComparisonOp.equal, .notEqual, .less, .lessEqual, .greater, .greaterEqual].all
        (fun op => (checked? (leaf op "V" (literal 6))).isOk) &&
      refusal? (leaf .equal "V" (literal (3 / 2) 1)) ==
        some (.literalScaleMismatch ["Probe", "Rows", "V"] 0 1) &&
      refusal? (leaf .equal "V" (literal 1 1)) ==
        some (.literalScaleMismatch ["Probe", "Rows", "V"] 0 1) &&
      refusal? (leaf .notEqual "V" (literal (3 / 2) 1)) ==
        some (.literalScaleMismatch ["Probe", "Rows", "V"] 0 1) &&
      refusal? (leaf .notEqual "V" (literal 1 1)) ==
        some (.literalScaleMismatch ["Probe", "Rows", "V"] 0 1) &&
      [SurfaceComparisonOp.less, .lessEqual, .greater, .greaterEqual].all
        (fun op => (checked? (leaf op "V" (literal (3 / 2) 1))).isOk) &&
      (checked? (leaf .equal "W" (literal (3 / 2) 1))).isOk &&
      refusal? (leaf .equal "W" (literal (1505 / 1000) 3)) ==
        some (.literalScaleMismatch ["Probe", "Rows", "W"] 2 3) &&
      (checked? (leaf .less "W" (literal (1505 / 1000) 3))).isOk &&
      (CorrelationElabError.literalScaleMismatch ["Probe", "Rows", "V"] 0 1).diagnostic? ==
        some .invalidCompareDecimalPlaces := by
  native_decide

/- A String field ordered against a literal draws the ordering class that reads both sides, and
compared by `==` or `!=` the equality ladder's class against a Number literal, as the grid measures. -/
example :
    ((refusal? (leaf .less "S" (literal 6))).bind CorrelationElabError.diagnostic? ==
        some .invalidTypeForComparison) &&
      [SurfaceComparisonOp.equal, .notEqual].all (fun op =>
        (refusal? (leaf op "S" (literal 6))).bind CorrelationElabError.diagnostic? ==
          some .invalidCompareToEnumOrString) := by
  native_decide

private def checkedNumber : RawCell → CheckedCell :=
  formalCheck { kind := .number { scale := 0, signed := true } }

/-- Rows 1–4 hold `5`, an empty cell, `9` and a malformed cell. -/
private def context : CorrelationContext where
  read env _ :=
    match env.uniqueRowAt? rows with
    | some 1 => checkedNumber (.parsed (.num 5))
    | some 3 => checkedNumber (.parsed (.num 9))
    | some 4 => checkedNumber (.rejected .malformed)
    | _ => checkedNumber .empty

private def frame (row : RowIndex) : CorrelationFrame :=
  { innerEnv := [(rows, row)], outerEnv := [] }

private def reference : HavingNumberRef :=
  { origin := .inner, field := { id := 0, info := { scale := 0, signed := true } } }

private def truths (op : CorrelationComparisonOp) (value : Rat) : List K :=
  [1, 2, 3, 4].map fun row =>
    (CorrelatedHaving.compareNumberLiteral op reference (literal value)).evalTruthIn context (frame row)

/- The leaf compares the field's value as the ordinary comparison does: an empty cell as zero, so
it is kept by `< 6` and dropped by `> 6`, the boundary held by the inclusive operators, and a
malformed cell unknown whatever the operator. -/
example :
    [truths .lessThan 6, truths .greaterThan 6, truths .lessEqual 5, truths .greaterEqual 9,
      truths .equal 0, truths .notEqual 5] =
      [[.tru, .tru, .fls, .unknown], [.fls, .fls, .tru, .unknown], [.tru, .tru, .fls, .unknown],
        [.fls, .fls, .tru, .unknown], [.fls, .tru, .fls, .unknown], [.fls, .tru, .tru, .unknown]] := by
  native_decide

/- A repetition leaf's ordering operators compare row indices, the left row against the right. -/
example :
    [CorrelationComparisonOp.lessEqual, .greaterThan, .greaterEqual].map (fun op =>
      [(1, 2), (2, 2), (3, 2)].map fun (left, right) =>
        (CorrelatedHaving.compareRepetitions op
          { origin := .inner, source := .repeatable rows }
          { origin := .outer, source := .repeatable rows }).evalTruthIn context
            { innerEnv := [(rows, left)], outerEnv := [(rows, right)] } == .tru) =
      [[true, true, false], [false, false, true], [false, true, true]] := by
  native_decide

/- On the computation arm the malformed cell is poison, not a dropped row, and an empty one still
compares as zero, so `< 6` holds on it where a skipped row would not. -/
example :
    ([1, 2, 4].map fun row =>
      (CorrelatedHaving.compareNumberLiteral .lessThan reference (literal 6)).evalComputationIn
        context (frame row)) =
      [.ok .holds, .ok .holds, .ok (.poison .malformed)] := by
  native_decide

private def arithmeticFilter : CorrelatedHaving :=
  .leaf (.numeric
    { op := .ordinary .less
      left := .binary .add (.atom (.field reference)) (.literal (literal 1))
      right := .literal (literal 6) })

example :
    ([1, 2, 4].map fun row => arithmeticFilter.evalTruthIn context (frame row)) =
      [.fls, .tru, .unknown] := by
  native_decide

example :
    ([1, 2, 4].map fun row => arithmeticFilter.evalComputationIn context (frame row)) =
      [.ok .notTrue, .ok .holds, .ok (.poison .malformed)] := by
  native_decide

private def surfaceField (name : String) : AuthoredNumericExpr SurfaceHavingNumericAtom :=
  .atom (.field
    { origin := .inner
      field := { base := .absolute, groups := ["Probe", "Rows"], field := name } })

private def surfaceRepetition : AuthoredNumericExpr SurfaceHavingNumericAtom :=
  .atom (.repetition
    { origin := .inner
      group := .path { base := .absolute, groups := ["Probe", "Rows"] } })

example :
    (checked? (.numeric .less
      (.binary .add (surfaceField "V") (.literal (literal 1))) (.literal (literal 6)))).isOk &&
    (checked? (.numeric .greater (.literal (literal 6))
      (.binary .add (surfaceField "V") (.literal (literal 1))))).isOk &&
    (checked? (.numeric .greater
      (.binary .add (surfaceField "V") surfaceRepetition) (.literal (literal 2)))).isOk &&
    [SurfaceComparisonOp.equal, .notEqual, .less, .lessEqual, .greater, .greaterEqual].all
      (fun op => (checked? (.numeric op surfaceRepetition (.literal (literal 2)))).isOk) := by
  native_decide

example :
    refusal? (.numeric .less (.literal (literal 1)) (.literal (literal 2))) =
      some .constantNumericComparison ∧
    CorrelationElabError.constantNumericComparison.diagnostic? =
      some .invalidCompareToConst := by
  native_decide

example :
    [SurfaceComparisonOp.equal, .notEqual].all (fun op =>
      (refusal? (.numeric op (.literal (literal 1 1)) (surfaceField "V"))).bind
        CorrelationElabError.diagnostic? == some .invalidCompareDecimalPlaces) &&
    [SurfaceComparisonOp.equal, .notEqual].all (fun op =>
      (refusal? (.numeric op (.literal (literal 1)) (surfaceField "S"))).bind
        CorrelationElabError.diagnostic? == some .invalidCompareToEnumOrString) := by
  native_decide

private def repetitionLiteralFilter (op : NumericComparisonOp) : CorrelatedHaving :=
  .leaf (.numeric
    { op := .ordinary op
      left := .atom (.repetition { origin := .inner, source := .repeatable rows })
      right := .literal (literal 2) })

example :
    [NumericComparisonOp.equal, .notEqual, .less, .lessEqual, .greater, .greaterEqual].map
      (fun op => [1, 2, 3].map fun row =>
        (repetitionLiteralFilter op).evalTruthIn context (frame row)) =
      [[.fls, .tru, .fls], [.tru, .fls, .tru], [.tru, .fls, .fls],
        [.tru, .tru, .fls], [.fls, .fls, .tru], [.fls, .tru, .tru]] := by
  native_decide

private def composedDependencies : CorrelatedHaving :=
  .leaf (.numeric
    { op := .ordinary .less
      left := .binary .add (.atom (.field reference))
        (.atom (.repetition { origin := .outer, source := .repeatable rows }))
      right := .binary .add (.atom (.field
        { reference with origin := .outer, field := { reference.field with id := 1 } })) (.atom (.field reference)) })

example : composedDependencies.fieldIds = [0, 1] ∧
    composedDependencies.markedFieldIds = [1] ∧ composedDependencies.usesInner = true ∧
    composedDependencies.usesOuter = true := by
  native_decide

private def failureComparison : CorrelatedHaving :=
  .leaf (.numeric
    { op := .ordinary .less
      left := .binary .divide (.literal (literal 1)) (.atom (.field reference))
      right := .atom (.field { reference with field := { reference.field with id := 1 } }) })

private def resolvingContext (left : RawCell) : ResolvingCorrelationContext String where
  read _ id := if id == 0 then .ok (checkedNumber left) else .error "right read"
  bindingError _ := "binding"
  unsupportedDateCalendar := "calendar"
  temporalValueFailure := "value failure"
  worldUnavailable := "world unavailable"
  typeValidityValueFailure := "type validity value failure"
  groupUnavailable := fun _ => "group unavailable"

example : (match failureComparison.evalTruthInResolving
    (resolvingContext (.rejected .malformed)) (frame 1) with
    | .error error => error == "right read"
    | .ok _ => false) = true := by
  native_decide

example : (match failureComparison.evalComputationInResolving
    (resolvingContext (.rejected .malformed)) (frame 1) with
    | .ok (.poison .malformed) => true
    | _ => false) = true := by
  native_decide

example : (match failureComparison.evalComputationInResolving
    (resolvingContext .empty) (frame 1) with
    | .error error => error == "right read"
    | .ok _ => false) = true := by
  native_decide

end A12Kernel.Conformance.HavingNumberLiteral
