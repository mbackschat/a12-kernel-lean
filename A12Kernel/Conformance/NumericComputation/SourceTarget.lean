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

private def isMissingIdentity (field : FieldId)
    (result : Option (Except NumericSourceTargetError α)) : Bool :=
  match result with
  | some (.error (.missingIdentity actual)) => actual == field
  | _ => false

private def repeatedTarget : FlatFieldDecl := {
  target with
    groupPath := ["Order", "Lines"]
    repeatableScope := [10]
}

private def repeatedModel : FlatModel := {
  fields := [repeatedTarget]
  repeatableGroups := [{
    level := 10
    path := ["Order", "Lines"]
    repeatability := some 2
  }]
}

private def repeatedChecked? : Option (CheckedDocument repeatedModel) := do
  let prepared ←
    (prepareFlatStringContext { now := { epochMillis := 0 } }
      builtinStringPatternCompiler repeatedModel).toOption
  (checkDocument prepared "en_US" {
    instantiatedRows := [
      { group := 10, path := [1] },
      { group := 10, path := [2] }
    ]
    cells := [{
      address := { field := 1, path := [1] }
      stored := "7.00"
      raw := .parsed (.num 7)
      numericSourceIdentity :=
        some (.decimal { unscaled := 700, scale := 2 })
    }]
  }).toOption

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

private def sourceWith (stored : String) (raw : RawCell)
    (identity : Option NumericSourceIdentity) : DocumentData :=
  { instantiatedRows := []
    cells := [{
      address := { field := 1, path := [] }
      stored
      raw
      numericSourceIdentity := identity
    }] }

private def viewResult? (source : DocumentData)
    (outcome : NumericTargetOutcome) (residual : List Bool := []) :
    Option (Except NumericSourceTargetError (NumericComputationRunView Bool)) := do
  let checked ← checked? source
  pure (NumericComputationRunView.fromOutcomes checked residual [(1, outcome)])

private def view? (source : DocumentData) (outcome : NumericTargetOutcome)
    (residual : List Bool := []) : Option (NumericComputationRunView Bool) :=
  (viewResult? source outcome residual).bind Except.toOption

private def destination : NumericComputationDestination
  | 1 => .presentValue (.decimal { unscaled := 9, scale := 0 })
  | 2 => .presentValue .nonComputedForm
  | _ => .absent

private def applied? (source : DocumentData) (outcome : NumericTargetOutcome)
    (field : FieldId) : Option NumericTargetState := do
  let view ← view? source outcome
  let applied ← view.applyTo destination |>.toOption
  pure (applied field)

private def duplicateApplication? (view : NumericComputationRunView Bool) :
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

/- Missing typed identity and a decimal identity inconsistent with stored text fail structurally. -/
example :
    isMissingIdentity 1
        (stateResult? (sourceWith "7" (.parsed (.num 7)) none)) = true ∧
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

/- Target rejection owns the computed-error instance; no-value classes clear only a filled source, and residual messages independently control the error predicate. -/
example :
    (do
      let view ← view? (sourceWith "7" (.parsed (.num 7))
        (some (.decimal { unscaled := 7, scale := 0 })))
        (.rejected { unscaled := 8, scale := 0 } .aboveMaximum)
      pure (view.withErrors, view.cleared)) =
        some ([⟨1, { unscaled := 8, scale := 0 }, .aboveMaximum⟩], []) ∧
    (do
      let view ← view? (sourceWith "7" (.parsed (.num 7))
        (some (.decimal { unscaled := 7, scale := 0 })))
        (.invalidNoValue .calculationValue) [true]
      pure (view.cleared, view.formalErrorsInOperands, view.noErrorOccurred)) =
        some ([1], [true], false) ∧
    (do
      let view ← view? (sourceWith "" .presentEmpty none)
        (.inheritedPoison .computedDependency)
      pure view.cleared) = some [] := by
  native_decide

/- A filled source without typed comparison identity fails before public classification. -/
example :
    isMissingIdentity 1
      (viewResult? (sourceWith "7" (.parsed (.num 7)) none) .noValue) = true := by
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

/- Malformed public action collections fail before clear/error/change order could select a winner. -/
example :
    let source : NumericTargetState :=
      .presentValue (.decimal { unscaled := 1, scale := 0 })
    let view := NumericComputationRunView.fromSourceOutcomes ([] : List Bool) [
      ⟨1, .rejected { unscaled := 2, scale := 0 } .aboveMaximum, source⟩,
      ⟨1, .accepted { unscaled := 3, scale := 0 }, source⟩
    ]
    duplicateApplication? view = some 1 := by
  native_decide

end A12Kernel.Conformance.NumericComputation.SourceTarget
