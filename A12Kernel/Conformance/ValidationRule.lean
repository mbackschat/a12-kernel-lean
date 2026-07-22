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

private def dateTimeComponents : TemporalComponents :=
  { year := true, month := true, day := true,
    hour := true, minute := true, second := true }

private def eventDateTime : FlatFieldDecl :=
  { id := 4, groupPath := ["Order"], name := "EventDateTime",
    policy := { kind := .temporal .dateTime dateTimeComponents } }

private def model : FlatModel :=
  { fields := [amount, acknowledged, unattached, repeatedAmount, eventDateTime]
    repeatableGroups := [{ level := 10, path := ["Order", "Items"] }] }

private def path (field : String) : SurfaceFieldPath :=
  { base := .absolute, groups := ["Order"], field }

private def amountNonnegative : SurfaceCondition :=
  .compare .greaterEqual (path "Amount") (.number 0)

private def amountPositive : SurfaceNumericComparison :=
  { op := .ordinary .greater
    left := .atom (.field (path "Amount"))
    right := .literal { value := 0, authoredScale := 0 } }

private def messagePlan : MessageRenderPlan :=
  { parts := [
      .text "Amount [",
      .fieldValue { displayValue := none, defaultDisplay := "0.00" },
      .text "] raw ",
      .fieldValue { displayValue := some "A\r\nB", defaultDisplay := "" }
    ] }

private def alternateMessagePlan : MessageRenderPlan :=
  { parts := [.text "alternate"] }

private def resolvedText : ResolvedMessageText :=
  messagePlan.render

private def amountName : MessageNameInput :=
  { providerResult := none
    modelLabel := some "Amount"
    debugDisplay := "/Order[1]/Amount" }

private def customerName : MessageNameInput :=
  { providerResult := some "Customer name"
    modelLabel := some "Customer"
    debugDisplay := "/Order[1]/Customer" }

private def emptyScaleZeroNumber : MessageValueInput :=
  { displayValue := none, defaultDisplay := "0" }

private def emptyScaleTwoNumber : MessageValueInput :=
  { displayValue := none, defaultDisplay := "0.00" }

private def emptyString : MessageValueInput :=
  { displayValue := none, defaultDisplay := "" }

private def errorCode : String :=
  "amountNonnegative"

private def rawAmount (cell : RawCell) : RawFlatContext where
  read id := if id = amount.id then cell else .empty

private def rawBothFilled : RawFlatContext where
  read id :=
    if id = amount.id then .parsed (.num 0)
    else if id = acknowledged.id then .parsed (.bool true)
    else .empty

private def rawPositiveAcknowledged : RawFlatContext where
  read id :=
    if id = amount.id then .parsed (.num 1)
    else if id = acknowledged.id then .parsed (.bool true)
    else .empty

private def temporalDateParts : DateParts :=
  { year := 2024, month := 6, day := 25 }

private def temporalClock : TimeOfDay :=
  (TimeOfDay.ofHms? 5 21 7).get (by native_decide)

private def rawEventDateTime (millis : Int) : RawFlatContext where
  read id :=
    if id = eventDateTime.id then
      .parsed (.temporal (.dateTime { epochMillis := millis }
        temporalDateParts temporalClock .storedGregorian))
    else .empty

private def worldAt (millis : Int) : World :=
  { now := { epochMillis := millis } }

private def defaultWorld : World := worldAt 0

private def assembleWithPlan (condition : SurfaceCondition) (errorField : FieldId)
    (severity : ValidationSeverity) (plan : MessageRenderPlan) :
    Except (ElabError ⊕ FlatRuleAssemblyError)
      (CheckedResolvedFlatRule model) := do
  let checked ← (elaborate model ["Order"] condition).mapError Sum.inl
  (assembleResolvedFlatRule model checked errorField errorCode severity
    plan).mapError Sum.inr

private def assemble (condition : SurfaceCondition) (errorField : FieldId)
    (severity : ValidationSeverity := .error) :=
  assembleWithPlan condition errorField severity messagePlan

private def assembleMixed? : Option (CheckedResolvedValidationRule model) := do
  let flat ← (elaborate model ["Order"]
    (.fieldFilled (path "Acknowledged"))).toOption
  let numeric ← (elaborateNumericComparison model ["Order"] amountPositive).toOption
  let flatCondition ← (CheckedValidationCondition.fromFlat flat).toOption
  let numericCondition ← (CheckedValidationCondition.fromNumeric numeric).toOption
  let condition ← (flatCondition.and numericCondition).toOption
  (assembleResolvedValidationRule model condition amount.id errorCode .error
    messagePlan).toOption

private def errorOf : Except ε α → Option ε
  | .ok _ => none
  | .error error => some error

private def outcomeOf (severity : ValidationSeverity) (raw : RawFlatContext)
    (hasContent : Bool := true) : Option FlatRuleOutcome :=
  match assemble amountNonnegative amount.id severity with
  | .error _ => none
  | .ok checked =>
      some (checked.evalFull defaultWorld raw hasContent)

private def outcomeFor (condition : SurfaceCondition) (errorField : FieldId)
    (raw : RawFlatContext) : Option FlatRuleOutcome :=
  match assemble condition errorField with
  | .error _ => none
  | .ok checked => some (checked.evalFull defaultWorld raw true)

private def outcomeForAt (world : World) (condition : SurfaceCondition)
    (errorField : FieldId) (raw : RawFlatContext) : Option FlatRuleOutcome :=
  match assemble condition errorField with
  | .error _ => none
  | .ok checked => some (checked.evalFull world raw true)

private def outcomeWithPlan (plan : MessageRenderPlan) (raw : RawFlatContext) :
    Option FlatRuleOutcome :=
  match assembleWithPlan amountNonnegative amount.id .error plan with
  | .error _ => none
  | .ok checked => some (checked.evalFull defaultWorld raw true)

private def mixedOutcome (raw : RawFlatContext) : Option FlatRuleOutcome := do
  let rule ← assembleMixed?
  pure (rule.evalFull defaultWorld raw true)

private def expectedMessage (severity : ValidationSeverity)
    (messageType : Polarity) : FlatRuleMessage :=
  { errorAddress := { field := amount.id, path := [] }
    severity
    messageType
    errorCode
    text := resolvedText }

/- The same checked rule derives OMISSION for empty zero and VALUE for given zero. -/
example :
    outcomeOf .error (rawAmount .empty) =
        some (.fired (expectedMessage .error .omission)) ∧
      outcomeOf .error (rawAmount (.parsed (.num 0))) =
        some (.fired (expectedMessage .error .value)) := by
  native_decide

/- Mixed checked whole-rule assembly discovers an error field referenced only by the numeric leaf and reuses the existing message outcome. -/
example :
    mixedOutcome rawPositiveAcknowledged =
        some (.fired (expectedMessage .error .value)) ∧
      mixedOutcome (rawAmount (.rejected .malformed)) = some .notFired := by
  native_decide

/- Whole-rule evaluation carries the explicit world through the checked condition, so `Now` observes the supplied millisecond instant before message construction. -/
example :
    outcomeForAt (worldAt 100999)
      (.compareNow .greater .left (path "EventDateTime"))
      eventDateTime.id (rawEventDateTime 100000) =
        some (.fired {
          errorAddress := { field := eventDateTime.id, path := [] }
          severity := .error
          messageType := .value
          errorCode
          text := resolvedText
        }) := by
  native_decide

/- A not-fired or unknown rule is independent of all message inputs, while a fired rule renders the selected structured plan. -/
example :
    outcomeWithPlan messagePlan (rawAmount (.parsed (.num (-1)))) =
        outcomeWithPlan alternateMessagePlan (rawAmount (.parsed (.num (-1)))) ∧
      outcomeWithPlan messagePlan (rawAmount (.rejected .malformed)) =
        outcomeWithPlan alternateMessagePlan (rawAmount (.rejected .malformed)) ∧
      outcomeWithPlan messagePlan (rawAmount (.parsed (.num 0))) ≠
        outcomeWithPlan alternateMessagePlan (rawAmount (.parsed (.num 0))) := by
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
          errorCode
          text := resolvedText
        }) ∧
      errorOf (assemble amountNonnegative unattached.id) =
        some (.inr (.errorFieldNotReferenced unattached.id)) ∧
      errorOf (assemble amountNonnegative repeatedAmount.id) =
        some (.inr (.repeatableErrorField repeatedAmount.id)) ∧
      errorOf (assemble amountNonnegative 99) =
        some (.inr (.errorField (.unknownFieldId 99))) := by
  native_decide

/- Rendering happens once over structured parts: missing values use their format-supplied default, while replacement bytes remain opaque. The first dollar below is decoded literal text; `$Other$` is replacement data. -/
example :
    ({ parts := [
        .text "Amount [",
        .fieldValue emptyScaleZeroNumber,
        .text "], name [",
        .fieldName customerName,
        .text "], cost ",
        .text "$",
        .fieldValue { emptyScaleZeroNumber with displayValue := some "$Other$" }
      ] } : MessageRenderPlan).render =
      { text := "Amount [0], name [Customer name], cost $$Other$" } := by
  native_decide

/- Format defaults are exact display strings: empty String stays empty, an explicitly empty display falls back, and Number scale is not collapsed to a universal `0`. -/
example :
    ({ parts := [
        .text "[",
        .fieldValue emptyString,
        .text "][",
        .fieldValue { emptyScaleZeroNumber with displayValue := some "" },
        .text "][",
        .fieldValue emptyScaleTwoNumber,
        .text "]"
      ] } : MessageRenderPlan).render =
      { text := "[][0][0.00]" } := by
  native_decide

/- Provider output wins even when empty; otherwise a nonempty model label wins before the debug representation. -/
example :
    ({ parts := [
        .fieldName { amountName with providerResult := some "" },
        .text "|",
        .fieldName amountName,
        .text "|",
        .fieldName { amountName with modelLabel := some "" },
        .text "|",
        .fieldName { amountName with modelLabel := none }
      ] } : MessageRenderPlan).render =
      { text := "|Amount|/Order[1]/Amount|/Order[1]/Amount" } := by
  native_decide

/- A present display value is repeated byte-for-byte; this renderer does not normalize display-layer CRLF. -/
example :
    let rawDisplay : MessageValueInput :=
      { displayValue := some "A\r\nB", defaultDisplay := "" }
    ({ parts := [
        .fieldValue rawDisplay,
        .text "|",
        .fieldValue rawDisplay
      ] } : MessageRenderPlan).render =
      { text := "A\r\nB|A\r\nB" } := by
  native_decide

end A12Kernel.Conformance.ValidationRule
