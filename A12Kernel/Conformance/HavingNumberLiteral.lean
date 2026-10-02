import A12Kernel.Elaboration.Correlation

/-! # A `Having` filter's Number field compared with a literal

A filter body is the ordinary condition production, so a Number field is compared with a literal by
the ordinary operator and the ordinary literal scale gate. The
[filter-leaf grid](../../docs/sources/having-filter-probes.md#src-having-number-leaf-grid) admits all
six operators and a literal on either side, refuses an equality whose literal carries more fraction
digits than the field's scale with `MVK_INVALID_COMPARE_DEC_PLACES`, and exempts ordering from that
gate. The cases below lock that admission and the leaf's truth: an empty field compares as zero, a
malformed one is unknown on validation and poison on computation.
-/

namespace A12Kernel.Conformance.HavingNumberLiteral

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

/- Every operator is admitted against a literal; an equality literal must fit the field's scale,
counting a written trailing zero, while ordering is exempt; the refusal projects to the measured
class. -/
example :
    [SurfaceComparisonOp.equal, .notEqual, .less, .lessEqual, .greater, .greaterEqual].all
        (fun op => (checked? (leaf op "V" (literal 6))).isOk) &&
      refusal? (leaf .equal "V" (literal (3 / 2) 1)) ==
        some (.literalScaleMismatch ["Probe", "Rows", "V"] 0 1) &&
      refusal? (leaf .equal "V" (literal 1 1)) ==
        some (.literalScaleMismatch ["Probe", "Rows", "V"] 0 1) &&
      (checked? (leaf .less "V" (literal (3 / 2) 1))).isOk &&
      (checked? (leaf .equal "W" (literal (3 / 2) 1))).isOk &&
      refusal? (leaf .equal "W" (literal (1505 / 1000) 3)) ==
        some (.literalScaleMismatch ["Probe", "Rows", "W"] 2 3) &&
      (checked? (leaf .less "W" (literal (1505 / 1000) 3))).isOk &&
      (CorrelationElabError.literalScaleMismatch ["Probe", "Rows", "V"] 0 1).diagnostic? ==
        some .invalidCompareDecimalPlaces := by
  native_decide

/- A String field ordered against a literal draws the ordering class that reads both sides, as the
grid measures; an equality claims none. -/
example :
    ((refusal? (leaf .less "S" (literal 6))).bind CorrelationElabError.diagnostic? ==
        some .invalidTypeForComparison) &&
      (match refusal? (leaf .equal "S" (literal 6)) with
        | some (.equalityFieldNotNumber _ _) => true | _ => false) := by
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

/- On the computation arm the malformed cell is poison, not a dropped row, and an empty one still
compares as zero. -/
example :
    ([1, 2, 4].map fun row =>
      (CorrelatedHaving.compareNumberLiteral .greaterThan reference (literal 6)).evalComputationIn
        context (frame row)) =
      [.notTrue, .notTrue, .poison .malformed] := by
  native_decide

end A12Kernel.Conformance.HavingNumberLiteral
