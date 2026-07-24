import A12Kernel.Elaboration.StringContext
import A12Kernel.Elaboration.CheckedStarDocument
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

private def adjustment : FlatFieldDecl :=
  { id := 5, groupPath := ["Order"], name := "Adjustment",
    policy := { kind := .number { scale := 0, signed := true } } }

private def outsider : FlatFieldDecl :=
  { id := 6, groupPath := ["Other"], name := "Outside",
    policy := { kind := .confirm } }

private def detailsValue : FlatFieldDecl :=
  { id := 7, groupPath := ["Order", "Details"], name := "Value",
    policy := { kind := .number { scale := 0, signed := true } } }

private def model : FlatModel :=
  { fields := [amount, acknowledged, unattached, repeatedAmount, eventDateTime,
      adjustment, outsider, detailsValue]
    repeatableGroups := [{ level := 10, path := ["Order", "Items"] }] }

private def path (field : String) : SurfaceFieldPath :=
  { base := .absolute, groups := ["Order"], field }

private def amountNonnegative : SurfaceCondition :=
  .compare .greaterEqual (path "Amount") (.number 0)

private def amountPositive : SurfaceNumericComparison :=
  { op := .ordinary .greater
    left := .atom (.field (path "Amount"))
    right := .literal { value := 0, authoredScale := 0 } }

private def aggregatePositive : SurfaceNumericComparison :=
  { op := .ordinary .greater
    left := .atom (.aggregate .sum {
      first := path "Amount"
      rest := [path "Adjustment"] })
    right := .literal { value := 4, authoredScale := 0 } }

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

private def rawAggregate : RawFlatContext where
  read id :=
    if id = amount.id then .parsed (.num 2)
    else if id = adjustment.id then .parsed (.num 3)
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

private def preparedPattern : FlatFieldDecl :=
  {
    id := 20
    groupPath := ["Order"]
    name := "PatternCode"
    policy := { kind := .string }
    stringPatternSource := some "A+"
  }

private def preparedCustom : FlatFieldDecl :=
  {
    id := 21
    groupPath := ["Order"]
    name := "CustomCode"
    policy := { kind := .string }
    customType := some { name := "ProjectCode" }
  }

private def preparedModel : FlatModel :=
  { fields := [preparedPattern, preparedCustom] }

private def preparedCompiler : StringPatternCompiler := fun source =>
  if source == "A+" then
    some fun value =>
      !value.isEmpty && value.toList.all fun character => character == 'A'
  else
    none

private def preparedRejection : RegisteredCustomRejection where
  projectCode := "PROJECT_CODE_INVALID"

private def preparedValidator : RegisteredCustomFieldValidator := fun value _ =>
  if value == "accepted" then none else some preparedRejection

private def preparedWorld : World where
  now := { epochMillis := 0 }
  customFieldValidator? := fun name =>
    if name == "ProjectCode" then some preparedValidator else none

private def preparedRaw (pattern custom : String) : RawFlatContext where
  read id :=
    if id == preparedPattern.id then .parsed (.str pattern)
    else if id == preparedCustom.id then .parsed (.str custom)
    else .empty

private def preparedRuleVerdict (pattern custom : String) : Option Verdict := do
  let prepared ←
    (prepareFlatStringContext preparedWorld preparedCompiler preparedModel).toOption
  let checked ← (elaborate preparedModel ["Order"]
    (.and
      (.fieldFilled {
        base := .absolute
        groups := ["Order"]
        field := "PatternCode"
      })
      (.fieldFilled {
        base := .absolute
        groups := ["Order"]
        field := "CustomCode"
      }))).toOption
  let rule ← (assembleResolvedFlatRule preparedModel checked preparedPattern.id
    "preparedRule" .error { parts := [] }).toOption
  pure (rule.evalFull prepared "en_US" (preparedRaw pattern custom) true).verdict

private def preparedPatternLengthVerdict (pattern : String) : Option Verdict := do
  let prepared ←
    (prepareFlatStringContext preparedWorld preparedCompiler preparedModel).toOption
  let checked ← (elaborate preparedModel ["Order"]
    (.lengthCompare .lessEqual (path "PatternCode") 3)).toOption
  let rule ← (assembleResolvedFlatRule preparedModel checked preparedPattern.id
    "preparedPatternLength" .error { parts := [] }).toOption
  pure (rule.evalFull prepared "en_US" (preparedRaw pattern "accepted") true).verdict

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

private def assembleAggregate? : Option (CheckedResolvedValidationRule model) := do
  let numeric ←
    (elaborateNumericComparison model ["Order"] aggregatePositive).toOption
  let condition ← (CheckedValidationCondition.fromNumeric numeric).toOption
  (assembleResolvedValidationRule model condition amount.id errorCode .error
    messagePlan).toOption

private def assembleRuleGroup? (errorField : FieldId) :
    Option (CheckedResolvedValidationRule model) := do
  let condition ← (CheckedValidationCondition.fromGroupPresence model ["Order"]
    (.ruleGroup false) .notFilled).toOption
  (assembleResolvedValidationRule model condition errorField errorCode .error
    messagePlan).toOption

private def ruleGroupAssemblyError? (errorField : FieldId) :
    Option FlatRuleAssemblyError := do
  let condition ← (CheckedValidationCondition.fromGroupPresence model ["Order"]
    (.ruleGroup false) .notFilled).toOption
  match assembleResolvedValidationRule model condition errorField errorCode .error
      messagePlan with
  | .ok _ => none
  | .error error => some error

private def preparedContext? (world : World) :
    Option (PreparedFlatStringContext model builtinStringPatternCompiler) :=
  (prepareFlatStringContext world builtinStringPatternCompiler model).toOption

private def evalFlatRule? (rule : CheckedResolvedFlatRule model)
    (world : World) (raw : RawFlatContext) (hasContent : Bool) :
    Option FlatRuleOutcome := do
  let prepared ← preparedContext? world
  pure (rule.evalFull prepared "en_US" raw hasContent)

private def evalValidationRule? (rule : CheckedResolvedValidationRule model)
    (world : World) (raw : RawFlatContext) (groups : GroupPresenceContext)
    (hasContent : Bool) : Option FlatRuleOutcome := do
  let prepared ← preparedContext? world
  (rule.evalFull prepared "en_US" raw groups hasContent).toOption

private def ruleGroupOutcome (state : GroupPresenceState) : Option FlatRuleOutcome := do
  let rule ← assembleRuleGroup? amount.id
  evalValidationRule? rule defaultWorld (rawAmount .empty)
    (fun path => if path == ["Order"] then some state else none) false

private def assembleGroupList? : Option (CheckedResolvedValidationRule model) := do
  let condition ← (CheckedValidationCondition.fromGroupList model ["Order"]
    .groupsNotCollectivelyFilled [
      .field (path "Amount"),
      .group (.path {
        base := .absolute
        groups := ["Order", "Details"]
      })]).toOption
  (assembleResolvedValidationRule model condition amount.id errorCode .error
    messagePlan).toOption

private def groupListOutcome (amountCell : RawCell)
    (detailsState : GroupPresenceState) : Option FlatRuleOutcome := do
  let rule ← assembleGroupList?
  evalValidationRule? rule defaultWorld (rawAmount amountCell)
    (fun path =>
      if path == ["Order", "Details"] then some detailsState else none) true

private def errorOf : Except ε α → Option ε
  | .ok _ => none
  | .error error => some error

private def outcomeOf (severity : ValidationSeverity) (raw : RawFlatContext)
    (hasContent : Bool := true) : Option FlatRuleOutcome :=
  match assemble amountNonnegative amount.id severity with
  | .error _ => none
  | .ok checked => evalFlatRule? checked defaultWorld raw hasContent

private def outcomeFor (condition : SurfaceCondition) (errorField : FieldId)
    (raw : RawFlatContext) : Option FlatRuleOutcome :=
  match assemble condition errorField with
  | .error _ => none
  | .ok checked => evalFlatRule? checked defaultWorld raw true

private def outcomeForAt (world : World) (condition : SurfaceCondition)
    (errorField : FieldId) (raw : RawFlatContext) : Option FlatRuleOutcome :=
  match assemble condition errorField with
  | .error _ => none
  | .ok checked => evalFlatRule? checked world raw true

private def outcomeWithPlan (plan : MessageRenderPlan) (raw : RawFlatContext) :
    Option FlatRuleOutcome :=
  match assembleWithPlan amountNonnegative amount.id .error plan with
  | .error _ => none
  | .ok checked => evalFlatRule? checked defaultWorld raw true

private def mixedOutcome (raw : RawFlatContext) : Option FlatRuleOutcome := do
  let rule ← assembleMixed?
  evalValidationRule? rule defaultWorld raw GroupPresenceContext.unavailable true

private def aggregateOutcome : Option FlatRuleOutcome := do
  let rule ← assembleAggregate?
  evalValidationRule? rule defaultWorld rawAggregate
    GroupPresenceContext.unavailable true

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

/- Whole-rule execution consumes the prepared pattern and custom-validator context rather than reconstructing an unprepared model context. -/
example :
    preparedRuleVerdict "AAA" "accepted" = some (.fired .value) ∧
      preparedRuleVerdict "BBB" "accepted" = some .unknown ∧
      preparedRuleVerdict "AAA" "rejected" = some .unknown := by
  native_decide

/- An arbitrary prepared declaration pattern admits an ordinary String-value consumer; accepted values retain their normalized length and rejected values remain formally unavailable. -/
example :
    preparedPatternLengthVerdict "AAA" = some (.fired .value) ∧
      preparedPatternLengthVerdict "AAAA" = some .notFired ∧
      preparedPatternLengthVerdict "BBB" = some .unknown := by
  native_decide

/- Mixed checked whole-rule assembly discovers an error field referenced only by the numeric leaf and reuses the existing message outcome. -/
example :
    mixedOutcome rawPositiveAcknowledged =
        some (.fired (expectedMessage .error .value)) ∧
      mixedOutcome (rawAmount (.rejected .malformed)) = some .notFired := by
  native_decide

/- A direct aggregate remains a numeric-expression atom through ordinary checked whole-rule assembly and the sole message emitter. -/
example : aggregateOutcome =
    some (.fired (expectedMessage .error .value)) := by
  native_decide

/- A group-presence leaf makes every descendant field a legal error field through the shared checked rule, and clean-empty omission reaches the existing message projection. -/
example :
    ruleGroupOutcome ({
      content := false
      erroneous := false
      relevance := .fullyRelevant
    } : GroupPresenceState) =
        some (.fired (expectedMessage .error .omission)) ∧
      (assembleRuleGroup? unattached.id).isSome = true := by
  native_decide

/- A checked fixed field/group list reaches the sole whole-rule message boundary with its exact omission polarity; a formally unavailable field keeps the collapsed non-fire silent. -/
example :
    groupListOutcome (.parsed (.num 1)) {
      content := false
      erroneous := false
      relevance := .fullyRelevant
    } = some (.fired (expectedMessage .error .omission)) ∧
    groupListOutcome (.rejected .malformed) {
      content := false
      erroneous := false
      relevance := .fullyRelevant
    } = some .unknown := by
  native_decide

/- A sibling field is not referenced by `RuleGroup`, so checked rule assembly rejects it instead of treating group presence as a global reference. -/
example :
    ruleGroupAssemblyError? outsider.id =
      some (.errorFieldNotReferenced outsider.id) := by
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

private def outerAmount : FlatFieldDecl :=
  { id := 30
    groupPath := ["Order", "Sections"]
    name := "OuterAmount"
    policy := { kind := .number { scale := 0, signed := true } }
    repeatableScope := [10] }

private def innerAmount : FlatFieldDecl :=
  { id := 31
    groupPath := ["Order", "Sections", "Items"]
    name := "InnerAmount"
    policy := { kind := .number { scale := 0, signed := true } }
    repeatableScope := [10, 20] }

private def ordinaryIterationModel : FlatModel :=
  { fields := [outerAmount, innerAmount]
    repeatableGroups := [
      { level := 10, path := ["Order", "Sections"], repeatability := some 2 },
      { level := 20, path := ["Order", "Sections", "Items"],
        repeatability := some 2 }] }

private def ordinaryPath (groups : List String) (field : String) :
    SurfaceFieldPath :=
  { base := .absolute, groups, field }

private def ordinaryIterationRule? :
    Option (CheckedResolvedValidationRule ordinaryIterationModel) := do
  let outer ←
    (CheckedValidationCondition.fromRepeatableFieldPresence
      ordinaryIterationModel ["Order"] .filled
      (ordinaryPath ["Order", "Sections"] "OuterAmount")).toOption
  let inner ←
    (CheckedValidationCondition.fromRepeatableFieldPresence
      ordinaryIterationModel ["Order"] .notFilled
      (ordinaryPath ["Order", "Sections", "Items"] "InnerAmount")).toOption
  let condition ← (outer.and inner).toOption
  (assembleResolvedValidationRule ordinaryIterationModel condition innerAmount.id
    "ordinaryIteration" .error { parts := [] }).toOption

private def outerIterationCondition? :
    Option (CheckedValidationCondition ordinaryIterationModel) :=
  (CheckedValidationCondition.fromRepeatableFieldPresence
    ordinaryIterationModel ["Order"] .filled
    (ordinaryPath ["Order", "Sections"] "OuterAmount")).toOption

/- Nested compatible ordinary references derive the deepest scope from the checked tree; the declaring group and error-field argument cannot override it. -/
example :
    (ordinaryIterationRule?.map fun rule =>
      (rule.iterationScope, rule.errorDeclaration.repeatableScope)) =
      some (some [10, 20], [10, 20]) := by
  native_decide

/- A deeper error declaration cannot manufacture a deeper iteration level when the condition references only the outer scope. -/
example :
    (outerIterationCondition?.map fun condition =>
      match assembleResolvedValidationRule ordinaryIterationModel condition
          innerAmount.id "ordinaryIteration" .error { parts := [] } with
      | .ok _ => none
      | .error error => some error) =
      some (some
        (.iterationScopeMismatch innerAmount.id [10] [10, 20])) := by
  native_decide

private def outerEmptyRule? :
    Option (CheckedResolvedValidationRule ordinaryIterationModel) := do
  let condition ←
    (CheckedValidationCondition.fromRepeatableFieldPresence
      ordinaryIterationModel ["Order"] .notFilled
      (ordinaryPath ["Order", "Sections"] "OuterAmount")).toOption
  (assembleResolvedValidationRule ordinaryIterationModel condition outerAmount.id
    "outerEmpty" .error { parts := [] }).toOption

private def ordinaryIterationData : DocumentData :=
  { instantiatedRows := [
      { group := 10, path := [2] },
      { group := 10, path := [1] },
      { group := 20, path := [2, 1] },
      { group := 20, path := [1, 1] }]
    cells := [{
      address := { field := outerAmount.id, path := [1] }
      stored := "1"
      raw := .parsed (.num 1)
    }] }

private def evalOrdinaryRule? (rule :
    CheckedResolvedValidationRule ordinaryIterationModel)
    (data : DocumentData) : Option (List (Env × FlatRuleOutcome)) := do
  let prepared ←
    (prepareFlatStringContext defaultWorld builtinStringPatternCompiler
      ordinaryIterationModel).toOption
  let checked ← (checkDocument prepared "en_US" data).toOption
  (rule.evalOrdinaryRepeatableFull checked).toOption

/- Runtime follows actual deepest-row document order and retains complete parent coordinates in both the consumer-visible environment and emitted error address. -/
example :
    ordinaryIterationRule?.bind (evalOrdinaryRule? · ordinaryIterationData) =
      some [
        ([(10, 2), (20, 1)], .notFired),
        ([(10, 1), (20, 1)], .fired {
          errorAddress := { field := innerAmount.id, path := [1, 1] }
          errorCode := "ordinaryIteration"
          severity := .error
          messageType := .omission
          text := { text := "" }
        })] := by
  native_decide

/- An instantiated empty row is evaluated and may fire, while zero actual rows produce zero rule environments rather than a phantom row. -/
example :
    (outerEmptyRule?.bind fun rule =>
      (evalOrdinaryRule? rule {
        instantiatedRows := [{ group := 10, path := [1] }]
        cells := []
      }).map fun outcomes => outcomes.map fun entry =>
        (entry.1, entry.2.verdict)) =
      some [([(10, 1)], .fired .omission)] ∧
    (outerEmptyRule?.bind fun rule =>
      evalOrdinaryRule? rule { instantiatedRows := [], cells := [] }) =
      some [] := by
  native_decide

end A12Kernel.Conformance.ValidationRule
