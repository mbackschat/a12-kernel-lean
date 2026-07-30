import A12Kernel.Elaboration.NumericComputation.RunApplication

/-! # Checked Number source-target locks -/

namespace A12Kernel.Conformance.NumericComputation.SourceTarget

open A12Kernel

private def target : FlatFieldDecl :=
  { id := 1
    groupPath := ["Order"]
    name := "Total"
    policy := { kind := .number { scale := 2, signed := false } } }

private def model : FlatModel := { fields := [target] }

private def checked? (source : DocumentData) :
    Option (CheckedDocument model) := do
  let prepared ←
    (prepareFlatStringContext { now := { epochMillis := 0 } }
      builtinStringPatternCompiler model).toOption
  (checkDocument prepared "en_US" source).toOption

private def stateResult? (source : DocumentData) :
    Option (Except NumericSourceTargetError NumericTargetState) := do
  let checked ← checked? source
  pure (checked.numericTargetState 1)

private def state? (source : DocumentData) : Option NumericTargetState :=
  (stateResult? source).bind Except.toOption

private def repeatedTarget : FlatFieldDecl := {
  target with
    groupPath := ["Order", "Lines"]
    repeatableScope := [10]
}

private def repeatedStringTarget : FlatFieldDecl := {
  repeatedTarget with
    id := 2
    name := "Label"
    policy := { kind := .string }
}

private def repeatedModel : FlatModel := {
  fields := [repeatedTarget, repeatedStringTarget]
  repeatableGroups := [{
    level := 10
    path := ["Order", "Lines"]
    repeatability := some 2
  }]
}

private def repeatedCheckedFrom? (source : DocumentData) :
    Option (CheckedDocument repeatedModel) := do
  let prepared ←
    (prepareFlatStringContext { now := { epochMillis := 0 } }
      builtinStringPatternCompiler repeatedModel).toOption
  (checkDocument prepared "en_US" source).toOption

private def repeatedChecked? : Option (CheckedDocument repeatedModel) :=
  repeatedCheckedFrom? {
    instantiatedRows := [
      { group := 10, path := [1] },
      { group := 10, path := [2] }
    ]
    cells := [{
      address := { field := 1, path := [1] }
      stored := "7.00"
      raw := .parsed (.num 7)
      numericDecimal := some { unscaled := 700, scale := 2 }
    }]
  }

/- Exact addressed source projection distinguishes a filled repeatable target from an absent sibling, while the scalar entry point keeps rejecting the repeatable declaration. -/
example :
    (do
      let checked ← repeatedChecked?
      let first ←
        (checked.numericTargetStateAt { field := 1, path := [1] }).toOption
      let second ←
        (checked.numericTargetStateAt { field := 1, path := [2] }).toOption
      pure (first, second,
        match checked.numericTargetState 1 with
        | .error (.repeatableTarget 1) => true
        | _ => false)) =
      some (
        NumericTargetState.presentValue
          (.decimal { unscaled := 700, scale := 2 }),
        NumericTargetState.absent,
        true) := by
  native_decide

/- The result classifier is shared by scalar and exact-addressed targets; source-relative change detection is independent of the target-key representation. -/
example :
    let address : CellAddr := { field := 1, path := [1] }
    let source : NumericTargetState :=
      .presentValue (.decimal { unscaled := 7, scale := 0 })
    let view : NumericComputationRunView Bool CellAddr :=
      NumericComputationRunView.fromPartitionedSourceOutcomes [] [
        {
          targetField := address
          outcome := .accepted { unscaled := 700, scale := 2 }
          source
        }
      ]
    view.withoutErrors = [
      { targetField := address, value := { unscaled := 700, scale := 2 } }
    ] ∧
      view.withChanges = [
        { targetField := address, value := { unscaled := 700, scale := 2 } }
      ] := by
  native_decide

private def repeatedAddress : CellAddr := { field := 1, path := [2] }

private def repeatedRow (index : Nat) : RowAddr :=
  { group := 10, path := [index] }

private def addressedViewAt (address : CellAddr)
    (source : NumericTargetState)
    (outcome : NumericTargetOutcome) :
    NumericComputationRunView Bool CellAddr :=
  NumericComputationRunView.fromPartitionedSourceOutcomes [] [{
    targetField := address
    outcome
    source
  }]

private def addressedView (source : NumericTargetState)
    (outcome : NumericTargetOutcome) :
    NumericComputationRunView Bool CellAddr :=
  addressedViewAt repeatedAddress source outcome

private def repeatedDestinationWith (rows : List Nat)
    (target : Option StoredNumber := none) :
    Option (CheckedDocument repeatedModel) :=
  let cells := match target with
    | none => []
    | some stored => [{
        address := repeatedAddress
        stored := stored.render
        raw := .parsed (.num stored.amount)
        numericDecimal := some {
          unscaled := stored.unscaled
          scale := stored.scale
        }
      }]
  repeatedCheckedFrom? {
    instantiatedRows := rows.map repeatedRow
    cells
  }

private def checkedApplicationMatrixHolds : Bool :=
  let sourceFilled : NumericTargetState :=
      .presentValue (.decimal { unscaled := 9, scale := 0 })
  (do
    let missingRows ← repeatedDestinationWith []
    let existingRows ← repeatedDestinationWith [1, 2]
    let filled ← repeatedDestinationWith [1, 2]
      (some { unscaled := 8, scale := 0 })
    let clearedMissing ←
      (addressedView sourceFilled .noValue).applyToChecked missingRows
        |>.toOption
    let clearedExisting ←
      (addressedView sourceFilled .noValue).applyToChecked existingRows
        |>.toOption
    let silent ←
      (addressedView .absent .noValue).applyToChecked missingRows
        |>.toOption
    let errored ←
      (addressedView sourceFilled
        (.rejected { unscaled := 10, scale := 0 } .aboveMaximum))
        |>.applyToChecked missingRows |>.toOption
    let changed ←
      (addressedView sourceFilled
        (.accepted { unscaled := 7, scale := 0 }))
        |>.applyToChecked missingRows |>.toOption
    let clearedFilled ←
      (addressedView sourceFilled .noValue).applyToChecked filled
        |>.toOption
    pure (
      clearedMissing.stateAt repeatedAddress ==
        NumericTargetState.presentEmpty &&
      clearedMissing.createdRow (repeatedRow 2) &&
      clearedExisting.stateAt repeatedAddress ==
        NumericTargetState.presentEmpty &&
      !clearedExisting.createdRow (repeatedRow 2) &&
      silent.stateAt repeatedAddress == NumericTargetState.absent &&
      !silent.createdRow (repeatedRow 2) &&
      errored.stateAt repeatedAddress == NumericTargetState.absent &&
      !errored.createdRow (repeatedRow 2) &&
      changed.stateAt repeatedAddress ==
        NumericTargetState.presentValue
          (.decimal { unscaled := 7, scale := 0 }) &&
      changed.createdRow (repeatedRow 2) &&
      clearedFilled.stateAt repeatedAddress ==
        NumericTargetState.presentEmpty)
  ).getD false

/- Checked retained-result application creates the exact addressed repeatable ancestor and target for CLEARED and VALUE, while silence and ERRORED preserve an absent destination. The projection deliberately makes no claim about unobserved predecessor padding. -/
example : checkedApplicationMatrixHolds = true := by
  native_decide

private def checkedApplicationError? (address : CellAddr) :
    Option NumericComputationDocumentApplicationError := do
  let destination ← repeatedDestinationWith []
  let source : NumericTargetState :=
    .presentValue (.decimal { unscaled := 9, scale := 0 })
  match (addressedViewAt address source .noValue).applyToChecked destination with
  | .error error => some error
  | .ok _ => none

/- The checked destination projection rejects unknown, non-Number, wrong-depth, and zero-coordinate targets before applying an action. -/
example :
    let unknown : CellAddr := { field := 99, path := [2] }
    let nonNumeric : CellAddr := { field := 2, path := [2] }
    let wrongDepth : CellAddr := { field := 1, path := [] }
    let zeroCoordinate : CellAddr := { field := 1, path := [0] }
    checkedApplicationError? unknown =
        some (.targetField unknown (.unknownFieldId 99)) ∧
      checkedApplicationError? nonNumeric =
        some (.nonNumericTarget nonNumeric) ∧
      checkedApplicationError? wrongDepth =
        some (.invalidTargetDepth wrongDepth 1) ∧
      checkedApplicationError? zeroCoordinate =
        some (.zeroTargetCoordinate zeroCoordinate) := by
  native_decide

private def sourceWith (stored : String) (raw : RawCell)
    (identity : Option NumericSourceIdentity) : DocumentData :=
  { instantiatedRows := []
    cells := [{
      address := { field := 1, path := [] }
      stored
      raw
      numericDecimal := identity.bind fun source => match source with
        | .decimal value => some {
            unscaled := value.unscaled
            scale := value.scale
          }
        | .nonComputedForm => none
    }] }

private def viewResult? (source : DocumentData)
    (outcome : NumericTargetOutcome)
    (supplied : List (ComputationFormalMessage Bool) := []) :
    Option (Except NumericSourceTargetError
      (NumericComputationRunView (ComputationFormalMessage Bool))) := do
  let checked ← checked? source
  pure (NumericComputationRunView.fromOutcomes checked
    (fun _ => true) supplied [(1, outcome)])

private def view? (source : DocumentData) (outcome : NumericTargetOutcome)
    (supplied : List (ComputationFormalMessage Bool) := []) :
    Option (NumericComputationRunView (ComputationFormalMessage Bool)) :=
  (viewResult? source outcome supplied).bind Except.toOption

private def destination : NumericComputationDestination
  | 1 => .presentValue (.decimal { unscaled := 9, scale := 0 })
  | 2 => .presentValue .nonComputedForm
  | _ => .absent

private def appliedTo? (source : DocumentData)
    (outcome : NumericTargetOutcome)
    (destination : NumericComputationDestination)
    (field : FieldId) : Option NumericTargetState := do
  let view ← view? source outcome
  let applied ← view.applyTo destination |>.toOption
  pure (applied field)

private def applied? (source : DocumentData) (outcome : NumericTargetOutcome)
    (field : FieldId) : Option NumericTargetState :=
  appliedTo? source outcome destination field

private def duplicateApplication?
    (view : NumericComputationRunView ResidualMessage) :
    Option FieldId :=
  match view.applyTo destination with
  | .error (.duplicateActionTarget field) => some field
  | .ok _ => none

/- Placement remains independent from typed source-value identity. -/
example :
    state? { instantiatedRows := [], cells := [] } =
        some .absent ∧
      state? (sourceWith "" .presentEmpty none) = some .presentEmpty := by
  native_decide

/- Decimal identity retains scale, while a source form outside computed BigDecimal output can never be unchanged. -/
example :
    state? (sourceWith "7" (.parsed (.num 7))
      (some (.decimal { unscaled := 7, scale := 0 }))) =
          some (.presentValue (.decimal { unscaled := 7, scale := 0 })) ∧
      (NumericTargetOutcome.accepted { unscaled := 700, scale := 2 }).projectDelta
          (.filled (.decimal { unscaled := 7, scale := 0 })) =
        some (.value { unscaled := 700, scale := 2 }) ∧
      state? (sourceWith "7.00" (.parsed (.num 7))
        (some (.decimal { unscaled := 700, scale := 2 }))) =
          some (.presentValue (.decimal { unscaled := 700, scale := 2 })) ∧
      (NumericTargetOutcome.accepted { unscaled := 700, scale := 2 }).projectDelta
          (.filled (.decimal { unscaled := 700, scale := 2 })) = none ∧
      state? (sourceWith "7.00" (.parsed (.num 7))
        (some .nonComputedForm)) =
          some (.presentValue .nonComputedForm) ∧
      (NumericTargetOutcome.accepted { unscaled := 700, scale := 2 }).projectDelta
          (.filled .nonComputedForm) =
        some (.value { unscaled := 700, scale := 2 }) := by
  native_decide

/- A filled Number without an explicit decimal annotation is the exact String-valued regime, while a decimal identity inconsistent with stored text fails structurally. -/
example :
    state? (sourceWith "7" (.parsed (.num 7)) none) =
        some (.presentValue .nonComputedForm) ∧
      (checked? (sourceWith "7.00" (.parsed (.num 7))
        (some (.decimal { unscaled := 7, scale := 0 })))).isNone = true := by
  native_decide

/- Exact decimal identity suppresses only the changed subset; a different scale or non-computed source form remains a public change. -/
example :
    (do
      let view ← view? (sourceWith "7.00" (.parsed (.num 7))
        (some (.decimal { unscaled := 700, scale := 2 })))
        (.accepted { unscaled := 700, scale := 2 })
      pure (view.withoutErrors, view.withChanges)) =
        some ([⟨1, { unscaled := 700, scale := 2 }⟩], []) ∧
    (do
      let view ← view? (sourceWith "7" (.parsed (.num 7))
        (some (.decimal { unscaled := 7, scale := 0 })))
        (.accepted { unscaled := 700, scale := 2 })
      pure view.withChanges) =
        some [⟨1, { unscaled := 700, scale := 2 }⟩] ∧
    (do
      let view ← view? (sourceWith "7.00" (.parsed (.num 7))
        (some .nonComputedForm))
        (.accepted { unscaled := 700, scale := 2 })
      pure view.withChanges) =
        some [⟨1, { unscaled := 700, scale := 2 }⟩] := by
  native_decide

/- Target rejection owns a computed-error instance, value-less target invalidity derives a residual error, and clean no-value or inherited poison can clear without manufacturing one. -/
example :
    (do
      let view ← view? (sourceWith "7" (.parsed (.num 7))
        (some (.decimal { unscaled := 7, scale := 0 })))
        (.rejected { unscaled := 8, scale := 0 } .aboveMaximum) [{
          pointer := ComputationErrorPointer.ofCellAddr { field := 1, path := [] }
          errorCode := "target-error"
          messageType := .value
          payload := true
        }]
      pure (view.withErrors, view.cleared,
        view.formalErrorsInOperands)) =
        some ([⟨1, { unscaled := 8, scale := 0 }, .aboveMaximum⟩],
          [], []) ∧
    (do
      let view ← view? (sourceWith "7" (.parsed (.num 7))
        (some (.decimal { unscaled := 7, scale := 0 })))
        (.invalidNoValue .calculationValue)
      pure (view.cleared,
        view.formalErrorsInOperands.map (·.errorCode),
        view.noErrorOccurred)) =
        some ([1], [berechnungsWertFehler], false) ∧
    (do
      let view ← view? (sourceWith "7" (.parsed (.num 7))
        (some (.decimal { unscaled := 7, scale := 0 }))) .noValue
      pure (view.cleared, view.formalErrorsInOperands,
        view.noErrorOccurred)) = some ([1], [], true) ∧
    (do
      let view ← view? (sourceWith "7" (.parsed (.num 7))
        (some (.decimal { unscaled := 7, scale := 0 })))
        (.inheritedPoison .computedDependency)
      pure (view.cleared, view.formalErrorsInOperands,
        view.noErrorOccurred)) = some ([1], [], true) := by
  native_decide

/- The implicit String-valued regime reaches result classification and remains unequal to every computed decimal form. -/
example :
    (do
      let view ← view? (sourceWith "7" (.parsed (.num 7)) none) .noValue
      pure (view.cleared, view.noErrorOccurred)) = some ([1], true) := by
  native_decide

/- Application consumes only source-relative actions: an unchanged success cannot overwrite a different destination, while a changed success uses the exact accepted-value transition and preserves every other field. -/
example :
    applied? (sourceWith "7.00" (.parsed (.num 7))
      (some (.decimal { unscaled := 700, scale := 2 })))
      (.accepted { unscaled := 700, scale := 2 }) 1 =
        some (.presentValue (.decimal { unscaled := 9, scale := 0 })) ∧
    applied? (sourceWith "7" (.parsed (.num 7))
      (some (.decimal { unscaled := 7, scale := 0 })))
      (.accepted { unscaled := 700, scale := 2 }) 1 =
        some (.presentValue (.decimal { unscaled := 700, scale := 2 })) ∧
    applied? (sourceWith "7" (.parsed (.num 7))
      (some (.decimal { unscaled := 7, scale := 0 })))
      (.accepted { unscaled := 700, scale := 2 }) 2 =
        some (.presentValue .nonComputedForm) := by
  native_decide

/- Both rejected attempts and source-filled no-value outcomes clear through the one-target owner. -/
example :
    applied? (sourceWith "7" (.parsed (.num 7))
      (some (.decimal { unscaled := 7, scale := 0 })))
      (.rejected { unscaled := 8, scale := 0 } .aboveMaximum) 1 =
        some .presentEmpty ∧
    applied? (sourceWith "7" (.parsed (.num 7))
      (some (.decimal { unscaled := 7, scale := 0 })))
      (.invalidNoValue .calculationValue) 1 = some .presentEmpty := by
  native_decide

/- Retained-result application consumes source-relative actions against a separate destination. CLEARED creates a present-empty target when the destination target was absent, silence and ERRORED preserve absence, VALUE creates its exact decimal state, and a present target is emptied. -/
example :
    let absentDestination : NumericComputationDestination :=
      fun _ => .absent
    appliedTo? (sourceWith "9" (.parsed (.num 9))
      (some (.decimal { unscaled := 9, scale := 0 })))
      .noValue absentDestination 1 = some .presentEmpty ∧
    appliedTo? { instantiatedRows := [], cells := [] }
      .noValue absentDestination 1 = some .absent ∧
    appliedTo? (sourceWith "9" (.parsed (.num 9))
      (some (.decimal { unscaled := 9, scale := 0 })))
      (.rejected { unscaled := 10, scale := 0 } .aboveMaximum)
      absentDestination 1 = some .absent ∧
    appliedTo? (sourceWith "9" (.parsed (.num 9))
      (some (.decimal { unscaled := 9, scale := 0 })))
      (.accepted { unscaled := 7, scale := 0 })
      absentDestination 1 =
        some (.presentValue (.decimal { unscaled := 7, scale := 0 })) ∧
    appliedTo? (sourceWith "9" (.parsed (.num 9))
      (some (.decimal { unscaled := 9, scale := 0 })))
      .noValue destination 1 = some .presentEmpty := by
  native_decide

/- Malformed public action collections fail before clear/error/change order could select a winner. -/
example :
    let source : NumericTargetState :=
      .presentValue (.decimal { unscaled := 1, scale := 0 })
    let view := NumericComputationRunView.fromPartitionedSourceOutcomes
      ([] : List Bool) [
      ⟨1, .rejected { unscaled := 2, scale := 0 } .aboveMaximum, source⟩,
      ⟨1, .accepted { unscaled := 3, scale := 0 }, source⟩
    ]
    duplicateApplication? view = some 1 := by
  native_decide

end A12Kernel.Conformance.NumericComputation.SourceTarget
