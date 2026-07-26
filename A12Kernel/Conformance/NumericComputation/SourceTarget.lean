import A12Kernel.Elaboration.NumericComputation.SourceTarget

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
    (result : Option (Except NumericSourceTargetError NumericTargetState)) : Bool :=
  match result with
  | some (.error (.missingIdentity actual)) => actual == field
  | _ => false

private def sourceWith (stored : String) (raw : RawCell)
    (identity : Option NumericSourceIdentity) : DocumentData :=
  { instantiatedRows := []
    cells := [{
      address := { field := 1, path := [] }
      stored
      raw
      numericSourceIdentity := identity
    }] }

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

end A12Kernel.Conformance.NumericComputation.SourceTarget
