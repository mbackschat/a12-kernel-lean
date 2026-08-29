import A12Kernel.Elaboration.AddressedNumberExtremum

/-! # Repeatable bounded Number extrema locks -/

namespace A12Kernel.Conformance.AddressedNumberExtremum

open A12Kernel

private def number (id : FieldId) (name : String) (scale : Nat) : FlatFieldDecl := {
  id
  groupPath := ["Probe", "Rows"]
  name
  policy := { kind := .number { scale, signed := true } }
  repeatableScope := [10]
}

private def left := number 1 "A" 0
private def right : FlatFieldDecl := {
  number 2 "B" 2 with
  numericTargetConstraints := { maximum := some 10 }
}
private def minimum : FlatFieldDecl := {
  number 3 "Minimum" 2 with
  numericTargetConstraints := { minimum := some (-999 / 100) }
}
private def maximum : FlatFieldDecl := {
  number 4 "Maximum" 2 with
  numericTargetConstraints := { maximum := some (999 / 100) }
}
private def wrongScale := number 5 "WrongScale" 0

private def model : FlatModel := {
  fields := [left, right, minimum, maximum, wrongScale]
  repeatableGroups := [{
    level := 10
    path := ["Probe", "Rows"]
    repeatability := some 7
  }]
}

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

private def cell (field : FieldId) (row : Nat)
    (stored : String) (raw : RawCell) : ClassifiedCellInput :=
  { address := { field, path := [row] }, stored, raw }

private def decimalCell (field : FieldId) (row : Nat) (stored : String)
    (unscaled scale : Int) (raw : RawCell) : ClassifiedCellInput := {
  address := { field, path := [row] }
  stored
  raw
  numericDecimal := some { unscaled, scale }
}

private def inputResult (extra : List ClassifiedCellInput := []) :=
  checkDocument prepared "en_US" {
    instantiatedRows := (List.range 7).map fun i =>
      { group := 10, path := [i + 1] }
    cells := [
      cell left.id 1 "3" (.parsed (.num 3)),
      cell right.id 1 "5.25" (.parsed (.num (21 / 4))),
      cell right.id 2 "5.25" (.parsed (.num (21 / 4))),
      cell left.id 3 "-2" (.parsed (.num (-2))),
      cell left.id 5 "bad-left" (.rejected .malformed),
      cell right.id 5 "12" (.rejected .declaredConstraint),
      cell left.id 6 "4" (.parsed (.num 4)),
      cell right.id 6 "12" (.rejected .declaredConstraint),
      cell left.id 7 "12" (.parsed (.num 12)),
      cell right.id 7 "4" (.parsed (.num 4))
    ] ++ extra
  }

private def input? (extra : List ClassifiedCellInput := []) :
    Option (CheckedDocument model) := (inputResult extra).toOption

private def operation? (target : FlatFieldDecl) (op : NumericExtremumOp) :
    Option (CheckedAddressedNumberExtremum model) :=
  (checkAddressedNumberExtremum model ["Probe", "Rows"] target.id
    (bare "A") (bare "B") op).toOption

private def addr (field : FieldId) (row : Nat) : CellAddr :=
  { field, path := [row] }

private def stored (unscaled : Int) (scale : Nat) : StoredNumber :=
  { unscaled, scale }

private def outcomes? (target : FlatFieldDecl) (op : NumericExtremumOp) :
    Option (List (CellAddr × NumericTargetOutcome)) := do
  let operation ← operation? target op
  let input ← input?
  let outcomes ← (operation.execute input).toOption
  pure (outcomes.map fun entry => (entry.targetField, entry.outcome))

private def result? (extra : List ClassifiedCellInput) :
    Option (NumericComputationRunView
      (ComputationFormalMessage Unit) CellAddr) := do
  let operation ← operation? maximum .maximum
  let input ← input? extra
  (operation.executeResult input (fun _ => ()) []).toOption

example :
    (operation? minimum .minimum).isSome = true ∧
    (operation? maximum .maximum).isSome = true ∧
    (match checkAddressedNumberExtremum model ["Probe", "Rows"]
        wrongScale.id (bare "A") (bare "B") .minimum with
      | .error (.scaleMismatch 0 summary) =>
          summary.scale == ScaleInfo.exact 2
      | _ => false) = true := by
  native_decide

example : outcomes? minimum .minimum = some [
    (addr minimum.id 1, .accepted (stored 3 0)),
    (addr minimum.id 2, .accepted (stored 0 0)),
    (addr minimum.id 3, .accepted (stored (-2) 0)),
    (addr minimum.id 4, .accepted (stored 0 0)),
    (addr minimum.id 5, .inheritedPoison .malformed),
    (addr minimum.id 6, .inheritedPoison .declaredConstraint),
    (addr minimum.id 7, .accepted (stored 4 0))
  ] := by native_decide

example : outcomes? maximum .maximum = some [
    (addr maximum.id 1, .accepted (stored 525 2)),
    (addr maximum.id 2, .accepted (stored 525 2)),
    (addr maximum.id 3, .accepted (stored 0 0)),
    (addr maximum.id 4, .accepted (stored 0 0)),
    (addr maximum.id 5, .inheritedPoison .malformed),
    (addr maximum.id 6, .inheritedPoison .declaredConstraint),
    (addr maximum.id 7, .rejected (stored 12 0) .aboveMaximum)
  ] := by native_decide

example :
    (do
      let view ← result? [
        decimalCell maximum.id 1 "5.25" 525 2 (.parsed (.num (21 / 4))),
        decimalCell maximum.id 2 "1.00" 100 2 (.parsed (.num 1)),
        decimalCell maximum.id 5 "7.00" 700 2 (.parsed (.num 7))
      ]
      pure (view.withChanges.map (·.targetField), view.cleared,
        view.withErrors.map (·.targetField))) =
      some (
        [addr maximum.id 2, addr maximum.id 3, addr maximum.id 4],
        [addr maximum.id 5],
        [addr maximum.id 7]) := by
  native_decide

private def listNumber (id : FieldId) (name : String)
    (scale : Nat) : FlatFieldDecl := {
  id
  groupPath := ["Probe", "Rows"]
  name
  policy := { kind := .number { scale, signed := true } }
  repeatableScope := [20]
}

private def listA := listNumber 11 "ListA" 0
private def listB : FlatFieldDecl := {
  listNumber 12 "ListB" 2 with
  numericTargetConstraints := { maximum := some 10 }
}
private def listC : FlatFieldDecl := {
  listNumber 13 "ListC" 3 with
  numericTargetConstraints := { minimum := some (-9), maximum := some 8 }
}
private def listMinimum : FlatFieldDecl := {
  listNumber 14 "ListMinimum" 3 with
  numericTargetConstraints := { minimum := some (-999 / 100) }
}
private def listMaximum : FlatFieldDecl := {
  listNumber 15 "ListMaximum" 3 with
  numericTargetConstraints := { maximum := some (999 / 100) }
}
private def listWrongScale := listNumber 16 "ListWrongScale" 2
/-- A real declared group strictly below the targets' own group, so the placement separator refuses
a genuine group rather than an invented path. -/
private def listDeeper : FlatFieldDecl := {
  listNumber 21 "ListDeeper" 3 with groupPath := ["Probe", "Rows", "Deeper"]
}
/-- A real declared group at the targets' own depth that does not contain them, so the separator
covers the shared-prefix account as well as the strictly-below one. -/
private def listBeside : FlatFieldDecl := {
  listNumber 22 "ListBeside" 3 with groupPath := ["Probe", "Beside"], repeatableScope := []
}
private def listSingleTarget : FlatFieldDecl := {
  listNumber 17 "ListSingleTarget" 0 with
  numericTargetConstraints := { maximum := some 10 }
}
private def listAbsTarget : FlatFieldDecl := {
  listNumber 18 "ListAbsTarget" 2 with
  numericTargetConstraints := { maximum := some (999 / 100) }
}
private def listRoundTarget : FlatFieldDecl := {
  listNumber 19 "ListRoundTarget" 1 with
  numericTargetConstraints := { maximum := some (99 / 10) }
}
private def listRoundSource : FlatFieldDecl := {
  listNumber 20 "ListRoundSource" 2 with
  numericTargetConstraints := { maximum := some 99 }
}

private def listModel : FlatModel := {
  fields := [listA, listB, listC, listMinimum, listMaximum, listWrongScale,
    listSingleTarget, listAbsTarget, listRoundTarget, listRoundSource,
    listDeeper, listBeside]
  repeatableGroups := [{
    level := 20
    path := ["Probe", "Rows"]
    repeatability := some 10
  }]
}

private def listPrepared :
    PreparedFlatStringContext listModel builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler listModel).toOption.get (by native_decide)

private def listInput? (extra : List ClassifiedCellInput := []) :
    Option (CheckedDocument listModel) :=
  (checkDocument listPrepared "en_US" {
    instantiatedRows := (List.range 10).map fun i =>
      { group := 20, path := [i + 1] }
    cells := [
      cell listA.id 1 "3" (.parsed (.num 3)),
      decimalCell listB.id 1 "5.25" 525 2 (.parsed (.num (21 / 4))),
      decimalCell listC.id 1 "4.5" 45 1 (.parsed (.num (9 / 2))),
      decimalCell listB.id 2 "5.25" 525 2 (.parsed (.num (21 / 4))),
      decimalCell listC.id 2 "4.5" 45 1 (.parsed (.num (9 / 2))),
      cell listA.id 3 "-2" (.parsed (.num (-2))),
      decimalCell listC.id 3 "-1.5" (-15) 1 (.parsed (.num (-3 / 2))),
      cell listA.id 5 "bad-a" (.rejected .malformed),
      cell listB.id 5 "12" (.rejected .declaredConstraint),
      decimalCell listC.id 5 "7.0" 70 1 (.parsed (.num 7)),
      cell listA.id 6 "4" (.parsed (.num 4)),
      cell listB.id 6 "12" (.rejected .declaredConstraint),
      cell listC.id 6 "bad-c" (.rejected .malformed),
      cell listA.id 7 "4" (.parsed (.num 4)),
      decimalCell listB.id 7 "5.00" 500 2 (.parsed (.num 5)),
      decimalCell listC.id 7 "9.0" 90 1 (.rejected .declaredConstraint),
      cell listA.id 8 "12" (.parsed (.num 12)),
      decimalCell listB.id 8 "4.00" 400 2 (.parsed (.num 4)),
      decimalCell listC.id 8 "6.0" 60 1 (.parsed (.num 6)),
      cell listA.id 9 "4" (.parsed (.num 4)),
      decimalCell listB.id 9 "5.00" 500 2 (.parsed (.num 5)),
      decimalCell listC.id 9 "8.0" 80 1 (.parsed (.num 8)),
      cell listA.id 10 "4" (.parsed (.num 4)),
      decimalCell listB.id 10 "5.00" 500 2 (.parsed (.num 5)),
      decimalCell listC.id 10 "-1.5" (-15) 1 (.parsed (.num (-3 / 2)))
    ] ++ extra
  }).toOption

private def listOperation? (target : FlatFieldDecl)
    (op : NumericExtremumOp) :
    Option (CheckedAddressedNumberExtremum listModel) :=
  (checkAddressedNumberExtremumList listModel ["Probe", "Rows"] target.id
    (bare "ListA") [(bare "ListB"), (bare "ListC")] op).toOption

private def listOutcomes? (target : FlatFieldDecl) (op : NumericExtremumOp) :
    Option (List (CellAddr × NumericTargetOutcome)) := do
  let operation ← listOperation? target op
  let input ← listInput?
  let outcomes ← (operation.execute input).toOption
  pure (outcomes.map fun entry => (entry.targetField, entry.outcome))

private def listResult? (extra : List ClassifiedCellInput) :
    Option (NumericComputationRunView
      (ComputationFormalMessage Unit) CellAddr) := do
  let operation ← listOperation? listMaximum .maximum
  let input ← listInput? extra
  (operation.executeResult input (fun _ => ()) []).toOption

private def singleOperation? (op : NumericExtremumOp) :
    Option (CheckedAddressedNumberExtremum listModel) :=
  (checkAddressedNumberExtremumList listModel ["Probe", "Rows"]
    listSingleTarget.id (bare "ListA") [] op).toOption

private def singleOutcomes? (op : NumericExtremumOp) :
    Option (List (CellAddr × NumericTargetOutcome)) := do
  let operation ← singleOperation? op
  let input ← listInput?
  let outcomes ← (operation.execute input).toOption
  pure (outcomes.map fun entry => (entry.targetField, entry.outcome))

example :
    (listOperation? listMinimum .minimum).isSome = true ∧
    (listOperation? listMaximum .maximum).isSome = true ∧
    (match checkAddressedNumberExtremumList listModel ["Probe", "Rows"]
        listWrongScale.id (bare "ListA") [(bare "ListB"), (bare "ListC")]
        .minimum with
      | .error (.scaleMismatch 2 summary) =>
          summary.scale == ScaleInfo.exact 3
      | _ => false) = true := by
  native_decide

example : listOutcomes? listMinimum .minimum = some [
    (addr listMinimum.id 1, .accepted (stored 3 0)),
    (addr listMinimum.id 2, .accepted (stored 0 0)),
    (addr listMinimum.id 3, .accepted (stored (-2) 0)),
    (addr listMinimum.id 4, .accepted (stored 0 0)),
    (addr listMinimum.id 5, .inheritedPoison .malformed),
    (addr listMinimum.id 6, .inheritedPoison .declaredConstraint),
    (addr listMinimum.id 7, .inheritedPoison .declaredConstraint),
    (addr listMinimum.id 8, .accepted (stored 4 0)),
    (addr listMinimum.id 9, .accepted (stored 4 0)),
    (addr listMinimum.id 10, .accepted (stored (-15) 1))
  ] := by native_decide

example : listOutcomes? listMaximum .maximum = some [
    (addr listMaximum.id 1, .accepted (stored 525 2)),
    (addr listMaximum.id 2, .accepted (stored 525 2)),
    (addr listMaximum.id 3, .accepted (stored 0 0)),
    (addr listMaximum.id 4, .accepted (stored 0 0)),
    (addr listMaximum.id 5, .inheritedPoison .malformed),
    (addr listMaximum.id 6, .inheritedPoison .declaredConstraint),
    (addr listMaximum.id 7, .inheritedPoison .declaredConstraint),
    (addr listMaximum.id 8, .rejected (stored 12 0) .aboveMaximum),
    (addr listMaximum.id 9, .accepted (stored 8 0)),
    (addr listMaximum.id 10, .accepted (stored 5 0))
  ] := by native_decide

example :
    (singleOperation? .minimum).isSome = true ∧
    (singleOperation? .maximum).isSome = true := by
  native_decide

example :
    singleOutcomes? .minimum = singleOutcomes? .maximum ∧
    singleOutcomes? .minimum = some [
      (addr listSingleTarget.id 1, .accepted (stored 3 0)),
      (addr listSingleTarget.id 2, .accepted (stored 0 0)),
      (addr listSingleTarget.id 3, .accepted (stored (-2) 0)),
      (addr listSingleTarget.id 4, .accepted (stored 0 0)),
      (addr listSingleTarget.id 5, .inheritedPoison .malformed),
      (addr listSingleTarget.id 6, .accepted (stored 4 0)),
      (addr listSingleTarget.id 7, .accepted (stored 4 0)),
      (addr listSingleTarget.id 8,
        .rejected (stored 12 0) .aboveMaximum),
      (addr listSingleTarget.id 9, .accepted (stored 4 0)),
      (addr listSingleTarget.id 10, .accepted (stored 4 0))
    ] := by
  native_decide

example :
    (do
      let view ← listResult? [
        decimalCell listMaximum.id 1 "5.25" 525 2 (.parsed (.num (21 / 4))),
        decimalCell listMaximum.id 2 "1.00" 100 2 (.parsed (.num 1)),
        decimalCell listMaximum.id 5 "7.00" 700 2 (.parsed (.num 7)),
        decimalCell listMaximum.id 7 "7.00" 700 2 (.parsed (.num 7))
      ]
      pure (view.withChanges.map (·.targetField), view.cleared,
        view.withErrors.map (·.targetField),
        view.formalErrorsInOperands.map (·.pointer))) =
      some (
        [addr listMaximum.id 2, addr listMaximum.id 3,
          addr listMaximum.id 4, addr listMaximum.id 9,
          addr listMaximum.id 10],
        [addr listMaximum.id 5, addr listMaximum.id 7],
        [addr listMaximum.id 8],
        []) := by
  native_decide

private def fieldOperand (name : String) :
    SurfaceAddressedNumberExtremumOperand :=
  .field (bare name)

private def literalOperand (value : Rat) (authoredScale : Int) :
    SurfaceAddressedNumberExtremumOperand :=
  .literal { value, authoredScale }

private def absOperand (name : String) :
    SurfaceAddressedNumberExtremumOperand :=
  .abs (bare name)

private def roundOperand (name : String) (mode : DecimalRoundingMode)
    (places : RoundingPlaces) :
    SurfaceAddressedNumberExtremumOperand :=
  .round (bare name) mode places

private def literalOperation? (target : FlatFieldDecl)
    (op : NumericExtremumOp)
    (first : SurfaceAddressedNumberExtremumOperand)
    (rest : List SurfaceAddressedNumberExtremumOperand) :
    Option (CheckedAddressedNumberExtremum listModel) :=
  (checkAddressedNumberExtremumOperands listModel ["Probe", "Rows"]
    target.id first rest op).toOption

private def literalOutcomes?
    (op : NumericExtremumOp)
    (first : SurfaceAddressedNumberExtremumOperand)
    (rest : List SurfaceAddressedNumberExtremumOperand) :
    Option (List (CellAddr × NumericTargetOutcome)) := do
  let operation ← literalOperation? listMaximum op first rest
  let input ← listInput?
  let outcomes ← (operation.execute input).toOption
  pure (outcomes.map fun entry => (entry.targetField, entry.outcome))

/- The addressed specialization admits one immediate literal anywhere beside at least one field-backed source, preserves its authored scale in the result-scale gate, and rejects a second literal before target checking. A literal-only call stays outside this bounded addressed capsule without claiming kernel rejection. -/
example :
    (literalOperation? listMaximum .minimum
      (fieldOperand "ListA") [literalOperand (5 / 4) 3]).isSome = true ∧
    (literalOperation? listMaximum .minimum
      (literalOperand (5 / 4) 3) [fieldOperand "ListA"]).isSome = true ∧
    (literalOperation? listMaximum .maximum
      (fieldOperand "ListA")
      [fieldOperand "ListB", literalOperand (-5 / 4) 3]).isSome = true ∧
    (literalOperation? listMaximum .maximum
      (fieldOperand "ListA")
      [literalOperand (-5 / 4) 3, fieldOperand "ListB"]).isSome = true ∧
    (match checkAddressedNumberExtremumOperands listModel ["Probe", "Rows"]
        listWrongScale.id (fieldOperand "ListA")
        [literalOperand (5 / 4) 3] .minimum with
      | .error (.scaleMismatch 2 summary) =>
          summary.scale == ScaleInfo.exact 3
      | _ => false) = true ∧
    (match checkAddressedNumberExtremumOperands listModel ["Probe", "Rows"]
        listMaximum.id (fieldOperand "ListA")
        [literalOperand (5 / 4) 3, literalOperand 2 0] .minimum with
      | .error .tooManyLiterals => true
      | _ => false) = true ∧
    (checkAddressedNumberExtremumOperands listModel ["Probe", "Rows"]
      listMaximum.id (literalOperand (5 / 4) 3) [] .minimum).toOption.isSome
      = true := by
  native_decide

/- The target-only half of the shared numeric placement admits by containment as well: a constant-only call, which reaches that gate without resolving any source, is taken from an ancestor declaring group, refused from a declared group strictly below the target, refused from a declared group beside it at the target's own depth, and refused from an unrepresentable declaring group. -/
example :
    (checkAddressedNumberExtremumOperands listModel ["Probe"]
      listMaximum.id (literalOperand (5 / 4) 3) [] .minimum).isOk = true ∧
    (match checkAddressedNumberExtremumOperands listModel ["Probe", "Rows", "Deeper"]
        listMaximum.id (literalOperand (5 / 4) 3) [] .minimum with
      | .error (.target (.targetOutsideDeclaringGroup path declaringGroup)) =>
          path == listMaximum.path && declaringGroup == ["Probe", "Rows", "Deeper"]
      | _ => false) = true ∧
    (match checkAddressedNumberExtremumOperands listModel ["Probe", "Beside"]
        listMaximum.id (literalOperand (5 / 4) 3) [] .minimum with
      | .error (.target (.targetOutsideDeclaringGroup path declaringGroup)) =>
          path == listMaximum.path && declaringGroup == ["Probe", "Beside"]
      | _ => false) = true ∧
    (match checkAddressedNumberExtremumOperands listModel []
        listMaximum.id (literalOperand (5 / 4) 3) [] .minimum with
      | .error (.target (.target (.invalidRuleGroup group))) => group == []
      | _ => false) = true := by
  native_decide

/- Field/literal order is retained even though clean extrema commute. Empty Number still contributes zero, a negative literal remains a value, and a reached malformed field still poisons the call on either side of the literal. -/
example :
    literalOutcomes? .minimum
      (fieldOperand "ListA") [literalOperand (5 / 4) 3] =
      literalOutcomes? .minimum
        (literalOperand (5 / 4) 3) [fieldOperand "ListA"] ∧
    literalOutcomes? .minimum
      (fieldOperand "ListA") [literalOperand (5 / 4) 3] = some [
        (addr listMaximum.id 1, .accepted (stored 125 2)),
        (addr listMaximum.id 2, .accepted (stored 0 0)),
        (addr listMaximum.id 3, .accepted (stored (-2) 0)),
        (addr listMaximum.id 4, .accepted (stored 0 0)),
        (addr listMaximum.id 5, .inheritedPoison .malformed),
        (addr listMaximum.id 6, .accepted (stored 125 2)),
        (addr listMaximum.id 7, .accepted (stored 125 2)),
        (addr listMaximum.id 8, .accepted (stored 125 2)),
        (addr listMaximum.id 9, .accepted (stored 125 2)),
        (addr listMaximum.id 10, .accepted (stored 125 2))
      ] ∧
    literalOutcomes? .maximum
      (fieldOperand "ListA") [literalOperand (-5 / 4) 3] = some [
        (addr listMaximum.id 1, .accepted (stored 3 0)),
        (addr listMaximum.id 2, .accepted (stored 0 0)),
        (addr listMaximum.id 3, .accepted (stored (-125) 2)),
        (addr listMaximum.id 4, .accepted (stored 0 0)),
        (addr listMaximum.id 5, .inheritedPoison .malformed),
        (addr listMaximum.id 6, .accepted (stored 4 0)),
        (addr listMaximum.id 7, .accepted (stored 4 0)),
        (addr listMaximum.id 8,
          .rejected (stored 12 0) .aboveMaximum),
        (addr listMaximum.id 9, .accepted (stored 4 0)),
        (addr listMaximum.id 10, .accepted (stored 4 0))
      ] := by
  native_decide

private def absInput? : Option (CheckedDocument listModel) :=
  (checkDocument listPrepared "en_US" {
    instantiatedRows := (List.range 8).map fun i =>
      { group := 20, path := [i + 1] }
    cells := [
      decimalCell listB.id 1 "-5.25" (-525) 2 (.parsed (.num (-21 / 4))),
      cell listA.id 1 "7" (.parsed (.num 7)),
      decimalCell listB.id 2 "3.50" 350 2 (.parsed (.num (7 / 2))),
      cell listA.id 2 "7" (.parsed (.num 7)),
      cell listA.id 3 "7" (.parsed (.num 7)),
      cell listB.id 4 "bad-b" (.rejected .malformed),
      cell listA.id 4 "-9" (.parsed (.num (-9))),
      decimalCell listB.id 5 "-12.34" (-1234) 2
        (.parsed (.num (-617 / 50))),
      cell listA.id 5 "20" (.parsed (.num 20)),
      decimalCell listB.id 6 "-5.25" (-525) 2 (.parsed (.num (-21 / 4))),
      cell listA.id 6 "bad-a" (.rejected .malformed),
      decimalCell listB.id 7 "-5.25" (-525) 2 (.parsed (.num (-21 / 4))),
      cell listA.id 7 "-8" (.parsed (.num (-8))),
      cell listB.id 8 "12" (.rejected .declaredConstraint),
      cell listA.id 8 "bad-a" (.rejected .malformed)
    ]
  }).toOption

private def absOutcomes?
    (first : SurfaceAddressedNumberExtremumOperand)
    (rest : List SurfaceAddressedNumberExtremumOperand) :
    Option (List (CellAddr × NumericTargetOutcome)) := do
  let operation ← literalOperation? listAbsTarget .minimum first rest
  let input ← absInput?
  let outcomes ← (operation.execute input).toOption
  pure (outcomes.map fun entry => (entry.targetField, entry.outcome))

/- One operand-local `Abs` preserves its Number source's scale and exact list position. A sibling literal remains governed by the outer call's one-literal budget. -/
example :
    (literalOperation? listAbsTarget .minimum
      (absOperand "ListB") [fieldOperand "ListA"]).isSome = true ∧
    (literalOperation? listAbsTarget .minimum
      (fieldOperand "ListA") [absOperand "ListB"]).isSome = true ∧
    (literalOperation? listMaximum .minimum
      (absOperand "ListB")
      [fieldOperand "ListA", literalOperand (5 / 4) 3]).isSome = true ∧
    (match checkAddressedNumberExtremumOperands listModel ["Probe", "Rows"]
        listSingleTarget.id (absOperand "ListB")
        [fieldOperand "ListA"] .minimum with
      | .error (.scaleMismatch 0 summary) =>
          summary.scale == ScaleInfo.exact 2
      | _ => false) = true := by
  native_decide

/- Operand-local `Abs` maps only its own reached value before the authored-order extremum fold; empty remains zero, either reached field poison wins, the first of two poison causes is retained, and target policy still applies after selection. -/
example :
    absOutcomes? (absOperand "ListB") [fieldOperand "ListA"] = some [
      (addr listAbsTarget.id 1, .accepted (stored 525 2)),
      (addr listAbsTarget.id 2, .accepted (stored 35 1)),
      (addr listAbsTarget.id 3, .accepted (stored 0 0)),
      (addr listAbsTarget.id 4, .inheritedPoison .malformed),
      (addr listAbsTarget.id 5,
        .rejected (stored 1234 2) .aboveMaximum),
      (addr listAbsTarget.id 6, .inheritedPoison .malformed),
      (addr listAbsTarget.id 7, .accepted (stored (-8) 0)),
      (addr listAbsTarget.id 8, .inheritedPoison .declaredConstraint)
    ] ∧
    absOutcomes? (fieldOperand "ListA") [absOperand "ListB"] = some [
      (addr listAbsTarget.id 1, .accepted (stored 525 2)),
      (addr listAbsTarget.id 2, .accepted (stored 35 1)),
      (addr listAbsTarget.id 3, .accepted (stored 0 0)),
      (addr listAbsTarget.id 4, .inheritedPoison .malformed),
      (addr listAbsTarget.id 5,
        .rejected (stored 1234 2) .aboveMaximum),
      (addr listAbsTarget.id 6, .inheritedPoison .malformed),
      (addr listAbsTarget.id 7, .accepted (stored (-8) 0)),
      (addr listAbsTarget.id 8, .inheritedPoison .malformed)
    ] := by
  native_decide

private def roundPlaces1 : RoundingPlaces := ⟨1, by decide⟩

private def roundInput? : Option (CheckedDocument listModel) :=
  (checkDocument listPrepared "en_US" {
    instantiatedRows := (List.range 8).map fun i =>
      { group := 20, path := [i + 1] }
    cells := [
      decimalCell listRoundSource.id 1 "-1.25" (-125) 2
        (.parsed (.num (-5 / 4))),
      cell listA.id 1 "7" (.parsed (.num 7)),
      decimalCell listRoundSource.id 2 "1.25" 125 2
        (.parsed (.num (5 / 4))),
      cell listA.id 2 "7" (.parsed (.num 7)),
      cell listA.id 3 "7" (.parsed (.num 7)),
      cell listRoundSource.id 4 "bad-source" (.rejected .malformed),
      cell listA.id 4 "-9" (.parsed (.num (-9))),
      decimalCell listRoundSource.id 5 "12.34" 1234 2
        (.parsed (.num (617 / 50))),
      cell listA.id 5 "20" (.parsed (.num 20)),
      decimalCell listRoundSource.id 6 "-5.25" (-525) 2
        (.parsed (.num (-21 / 4))),
      cell listA.id 6 "bad-a" (.rejected .malformed),
      decimalCell listRoundSource.id 7 "-5.25" (-525) 2
        (.parsed (.num (-21 / 4))),
      cell listA.id 7 "-8" (.parsed (.num (-8))),
      cell listRoundSource.id 8 "100" (.rejected .declaredConstraint),
      cell listA.id 8 "bad-a" (.rejected .malformed)
    ]
  }).toOption

private def roundOutcomes?
    (first : SurfaceAddressedNumberExtremumOperand)
    (rest : List SurfaceAddressedNumberExtremumOperand) :
    Option (List (CellAddr × NumericTargetOutcome)) := do
  let operation ← literalOperation? listRoundTarget .minimum first rest
  let input ← roundInput?
  let outcomes ← (operation.execute input).toOption
  pure (outcomes.map fun entry => (entry.targetField, entry.outcome))

/- Every scalar rounding mode is an operand-local tag with its authored places and outer derived scale. A literal sibling belongs to the outer extremum call. -/
example :
    (literalOperation? listRoundTarget .minimum
      (roundOperand "ListRoundSource" .floor roundPlaces1)
      [fieldOperand "ListA"]).isSome = true ∧
    (literalOperation? listRoundTarget .minimum
      (fieldOperand "ListA")
      [roundOperand "ListRoundSource" .floor roundPlaces1]).isSome = true ∧
    (literalOperation? listRoundTarget .minimum
      (roundOperand "ListRoundSource" .ceiling roundPlaces1)
      [fieldOperand "ListA"]).isSome = true ∧
    (literalOperation? listRoundTarget .minimum
      (roundOperand "ListRoundSource" .halfUp roundPlaces1)
      [fieldOperand "ListA"]).isSome = true ∧
    (literalOperation? listMaximum .minimum
      (roundOperand "ListRoundSource" .floor roundPlaces1)
      [fieldOperand "ListA", literalOperand (5 / 4) 3]).isSome = true ∧
    (match checkAddressedNumberExtremumOperands listModel ["Probe", "Rows"]
        listWrongScale.id
        (roundOperand "ListRoundSource" .floor roundPlaces1)
        [fieldOperand "ListA"] .minimum with
      | .error (.scaleMismatch 2 summary) =>
          summary.scale == ScaleInfo.exact 1
      | _ => false) = true := by
  native_decide

/- Floor supplies the complete empty, poison, first-cause, target, and direct-field-winner matrix. Ceiling and half-up remain distinct on the signed tie rows. -/
example :
    roundOutcomes? (roundOperand "ListRoundSource" .floor roundPlaces1)
      [fieldOperand "ListA"] = some [
        (addr listRoundTarget.id 1, .accepted (stored (-13) 1)),
        (addr listRoundTarget.id 2, .accepted (stored 12 1)),
        (addr listRoundTarget.id 3, .accepted (stored 0 0)),
        (addr listRoundTarget.id 4, .inheritedPoison .malformed),
        (addr listRoundTarget.id 5,
          .rejected (stored 123 1) .aboveMaximum),
        (addr listRoundTarget.id 6, .inheritedPoison .malformed),
        (addr listRoundTarget.id 7, .accepted (stored (-8) 0)),
        (addr listRoundTarget.id 8,
          .inheritedPoison .declaredConstraint)
      ] ∧
    (roundOutcomes? (roundOperand "ListRoundSource" .ceiling roundPlaces1)
      [fieldOperand "ListA"]).map (·.take 2) = some [
        (addr listRoundTarget.id 1, .accepted (stored (-12) 1)),
        (addr listRoundTarget.id 2, .accepted (stored 13 1))
      ] ∧
    (roundOutcomes? (roundOperand "ListRoundSource" .halfUp roundPlaces1)
      [fieldOperand "ListA"]).map (·.take 2) = some [
        (addr listRoundTarget.id 1, .accepted (stored (-13) 1)),
        (addr listRoundTarget.id 2, .accepted (stored 13 1))
      ] ∧
    (roundOutcomes? (fieldOperand "ListA")
      [roundOperand "ListRoundSource" .floor roundPlaces1]).bind (·.getLast?) =
        some (addr listRoundTarget.id 8,
          .inheritedPoison .malformed) := by
  native_decide

end A12Kernel.Conformance.AddressedNumberExtremum
