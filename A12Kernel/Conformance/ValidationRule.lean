import A12Kernel.Elaboration.ValidationRule

/-! # Checked flat whole-rule conformance locks -/

namespace A12Kernel.Conformance.ValidationRule

open A12Kernel

private def amount : FlatFieldDecl :=
  { id := 0, groupPath := ["Order"], name := "Amount",
    policy := { kind := .number { scale := 0, signed := true } } }

private def acknowledged : FlatFieldDecl :=
  { id := 1, groupPath := ["Order"], name := "Acknowledged",
    policy := { kind := .boolean } }

private def unattached : FlatFieldDecl :=
  { id := 2, groupPath := ["Order"], name := "Unattached",
    policy := { kind := .confirm } }

private def repeatedAmount : FlatFieldDecl :=
  { id := 3, groupPath := ["Order", "Items"], name := "Amount",
    policy := { kind := .number { scale := 0, signed := true } },
    repeatableScope := [10] }

private def model : FlatModel :=
  { fields := [amount, acknowledged, unattached, repeatedAmount]
    repeatableGroups := [{ level := 10, path := ["Order", "Items"] }] }

private def path (field : String) : SurfaceFieldPath :=
  { base := .absolute, groups := ["Order"], field }

private def amountNonnegative : SurfaceCondition :=
  .compare .greaterEqual (path "Amount") (.number 0)

private def resolvedText : ResolvedMessageText :=
  { text := "$Amount.value$ stays opaque" }

private def rawAmount (cell : RawCell) : RawFlatContext where
  read id := if id = amount.id then cell else .empty

private def rawBothFilled : RawFlatContext where
  read id :=
    if id = amount.id then .parsed (.num 0)
    else if id = acknowledged.id then .parsed (.bool true)
    else .empty

private def assemble (condition : SurfaceCondition) (errorField : FieldId)
    (severity : ValidationSeverity := .error) :
    Except (ElabError ⊕ FlatRuleAssemblyError)
      (CheckedResolvedFlatRule model) := do
  let checked ← (elaborate model ["Order"] condition).mapError Sum.inl
  (assembleResolvedFlatRule model checked errorField severity
    resolvedText).mapError Sum.inr

private def errorOf : Except ε α → Option ε
  | .ok _ => none
  | .error error => some error

private def outcomeOf (severity : ValidationSeverity) (raw : RawFlatContext)
    (hasContent : Bool := true) : Option FlatRuleOutcome :=
  match assemble amountNonnegative amount.id severity with
  | .error _ => none
  | .ok checked =>
      some (checked.evalFull raw hasContent)

private def outcomeFor (condition : SurfaceCondition) (errorField : FieldId)
    (raw : RawFlatContext) : Option FlatRuleOutcome :=
  match assemble condition errorField with
  | .error _ => none
  | .ok checked => some (checked.evalFull raw true)

private def expectedMessage (severity : ValidationSeverity)
    (messageType : Polarity) : FlatRuleMessage :=
  { errorAddress := { field := amount.id, path := [] }
    severity
    messageType
    text := resolvedText }

/- The same checked rule derives OMISSION for empty zero and VALUE for given zero. -/
example :
    outcomeOf .error (rawAmount .empty) =
        some (.fired (expectedMessage .error .omission)) ∧
      outcomeOf .error (rawAmount (.parsed (.num 0))) =
        some (.fired (expectedMessage .error .value)) := by
  native_decide

/- False and unknown both emit nothing, but the whole-rule result preserves the distinction. -/
example :
    outcomeOf .error (rawAmount (.parsed (.num (-1)))) =
        some .notFired ∧
      outcomeOf .error (rawAmount (.rejected .malformed)) =
        some .unknown := by
  native_decide

/- Metadata cannot bypass the condition's empty-row gate. -/
example :
    outcomeOf .warning (rawAmount .empty) false =
      some .notFired := by
  native_decide

/- Severity changes neither firing nor polarity, while only ERROR invalidates. -/
example :
    outcomeOf .warning (rawAmount (.parsed (.num 0))) =
        some (.fired (expectedMessage .warning .value)) ∧
      outcomeOf .info (rawAmount (.parsed (.num 0))) =
        some (.fired (expectedMessage .info .value)) ∧
      (expectedMessage .error .value).invalidates = true ∧
      (expectedMessage .warning .value).invalidates = false ∧
      (expectedMessage .info .value).invalidates = false := by
  native_decide

/- Error-field reference is checked after condition-path resolution and error-field ID lookup. -/
example :
    (assemble (.and amountNonnegative (.fieldFilled (path "Acknowledged")))
        acknowledged.id).isOk = true ∧
      outcomeFor
          (.and amountNonnegative (.fieldFilled (path "Acknowledged")))
          acknowledged.id rawBothFilled =
        some (.fired {
          errorAddress := { field := acknowledged.id, path := [] }
          severity := .error
          messageType := .value
          text := resolvedText
        }) ∧
      errorOf (assemble amountNonnegative unattached.id) =
        some (.inr (.errorFieldNotReferenced unattached.id)) ∧
      errorOf (assemble amountNonnegative repeatedAmount.id) =
        some (.inr (.repeatableErrorField repeatedAmount.id)) ∧
      errorOf (assemble amountNonnegative 99) =
        some (.inr (.errorField (.unknownFieldId 99))) := by
  native_decide

end A12Kernel.Conformance.ValidationRule
