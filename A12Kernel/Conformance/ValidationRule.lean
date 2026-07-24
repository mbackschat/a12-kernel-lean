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

private def innerPrice : FlatFieldDecl :=
  { id := 33
    groupPath := ["Order", "Sections", "Items"]
    name := "InnerPrice"
    policy := { kind := .number { scale := 0, signed := true } }
    repeatableScope := [10, 20] }

private def baseAmount : FlatFieldDecl :=
  { id := 34
    groupPath := ["Order"]
    name := "BaseAmount"
    policy := { kind := .number { scale := 0, signed := true } } }

private def innerToken : FlatFieldDecl :=
  { id := 35
    groupPath := ["Order", "Sections", "Items"]
    name := "InnerToken"
    policy := { kind := .string }
    repeatableScope := [10, 20] }

private def baseToken : FlatFieldDecl :=
  { id := 36
    groupPath := ["Order"]
    name := "BaseToken"
    policy := { kind := .string } }

private def innerNumericCode : FlatFieldDecl :=
  { id := 37
    groupPath := ["Order", "Sections", "Items"]
    name := "InnerNumericCode"
    policy := { kind := .string }
    stringPatternSource := some "[0-9]+"
    stringPolicy := { maxLength := some 15 }
    repeatableScope := [10, 20] }

private def innerNumericChoice : FlatFieldDecl :=
  { id := 38
    groupPath := ["Order", "Sections", "Items"]
    name := "InnerNumericChoice"
    policy := { kind := .enumeration }
    enumeration := some {
      storedTokens := ["1.50", "2"]
      categories := [{ name := "Factor", tokens := ["15", "20"] }] }
    repeatableScope := [10, 20] }

private def innerDate : FlatFieldDecl :=
  { id := 39
    groupPath := ["Order", "Sections", "Items"]
    name := "InnerDate"
    policy := { kind := .temporal .date TemporalComponents.fullDate }
    repeatableScope := [10, 20] }

private def innerTime : FlatFieldDecl :=
  { id := 40
    groupPath := ["Order", "Sections", "Items"]
    name := "InnerTime"
    policy := { kind := .temporal .time {
      year := false, month := false, day := false,
      hour := true, minute := true, second := true } }
    repeatableScope := [10, 20] }

private def innerDateTime : FlatFieldDecl :=
  { id := 41
    groupPath := ["Order", "Sections", "Items"]
    name := "InnerDateTime"
    policy := { kind := .temporal .dateTime dateTimeComponents }
    repeatableScope := [10, 20] }

private def innerEarlierDate : FlatFieldDecl :=
  { id := 42
    groupPath := ["Order", "Sections", "Items"]
    name := "InnerEarlierDate"
    policy := { kind := .temporal .date TemporalComponents.fullDate }
    repeatableScope := [10, 20] }

private def sectionDetail : FlatFieldDecl :=
  { id := 32
    groupPath := ["Order", "Sections", "Details"]
    name := "SectionDetail"
    policy := { kind := .number { scale := 0, signed := true } }
    repeatableScope := [10] }

private def ordinaryIterationModel : FlatModel :=
  { fields := [outerAmount, innerAmount, sectionDetail, innerPrice, baseAmount,
      innerToken, baseToken, innerNumericCode, innerNumericChoice, innerDate,
      innerTime, innerDateTime, innerEarlierDate]
    repeatableGroups := [
      { level := 10, path := ["Order", "Sections"], repeatability := some 2 },
      { level := 20, path := ["Order", "Sections", "Items"],
        repeatability := some 2 }] }

private def ordinaryPath (groups : List String) (field : String) :
    SurfaceFieldPath :=
  { base := .absolute, groups, field }

private def outerIterationCondition? :
    Option (CheckedValidationCondition ordinaryIterationModel) :=
  (CheckedValidationCondition.fromRepeatableFieldPresence
    ordinaryIterationModel ["Order"] .filled
    (ordinaryPath ["Order", "Sections"] "OuterAmount")).toOption

private def innerEmptyCondition? :
    Option (CheckedValidationCondition ordinaryIterationModel) :=
  (CheckedValidationCondition.fromRepeatableFieldPresence
    ordinaryIterationModel ["Order"] .notFilled
    (ordinaryPath ["Order", "Sections", "Items"] "InnerAmount")).toOption

private def innerGroupFilledCondition? :
    Option (CheckedValidationCondition ordinaryIterationModel) :=
  (CheckedValidationCondition.fromGroupPresence ordinaryIterationModel
    ["Order"] (.path {
      base := .absolute
      groups := ["Order", "Sections", "Items"]
    }) .filled).toOption

private def nestedUnguardedCondition? :
    Option (CheckedValidationCondition ordinaryIterationModel) := do
  let outer ← outerIterationCondition?
  let inner ← innerEmptyCondition?
  (outer.and inner).toOption

private def ordinaryIterationCondition? :
    Option (CheckedValidationCondition ordinaryIterationModel) := do
  let outer ←
    outerIterationCondition?
  let innerGroup ← innerGroupFilledCondition?
  let inner ← innerEmptyCondition?
  let guardedInner ← (innerGroup.and inner).toOption
  (outer.and guardedInner).toOption

private def ordinaryIterationRule? :
    Option (CheckedResolvedValidationRule ordinaryIterationModel) := do
  let condition ← ordinaryIterationCondition?
  (assembleResolvedValidationRule ordinaryIterationModel condition innerAmount.id
    "ordinaryIteration" .error { parts := [] }).toOption

private def absoluteGroup (groups : GroupPath) : SurfaceGroupReference := .path { base := .absolute, groups }

private def ordinaryGroupPresenceRule?
    (rowGroup : GroupPath) (reference : SurfaceGroupReference)
    (target : FlatFieldDecl) (errorCode : String) :
    Option (CheckedResolvedValidationRule ordinaryIterationModel) := do
  let condition ←
    (CheckedValidationCondition.fromGroupPresence ordinaryIterationModel
      rowGroup reference .filled).toOption
  (assembleResolvedValidationRule ordinaryIterationModel condition target.id
    errorCode .error { parts := [] }).toOption

private def outerGroupPathRule? :=
  ordinaryGroupPresenceRule? ["Order"]
    (absoluteGroup ["Order", "Sections"]) outerAmount "outerGroupPath"

private def outerRuleGroupRule? :=
  ordinaryGroupPresenceRule? ["Order", "Sections"]
    (.ruleGroup false) outerAmount "outerRuleGroup"

private def detailGroupPathRule? :=
  ordinaryGroupPresenceRule? ["Order"]
    (absoluteGroup ["Order", "Sections", "Details"])
    sectionDetail "detailGroupPath"

private def ordinaryRepeatableNumericRuleAt?
    (groups : List String) (field : String)
    (target : FieldId) (errorCode : String) :
    Option (CheckedResolvedValidationRule ordinaryIterationModel) := do
  let numeric ←
    (elaborateRepeatableNumericComparison ordinaryIterationModel
      groups {
        op := .ordinary .greaterEqual
        left := .binary .add
          (.atom (.field
            (ordinaryPath groups field)))
          (.literal { value := 1, authoredScale := 0 })
        right := .literal { value := 1, authoredScale := 0 }
      }).toOption
  let condition ←
    (CheckedValidationCondition.fromOrderedNumeric numeric).toOption
  (assembleResolvedValidationRule ordinaryIterationModel condition target
    errorCode .error { parts := [] }).toOption

private def ordinaryRepeatableNumericRule? :=
  ordinaryRepeatableNumericRuleAt? ["Order", "Sections"]
    "OuterAmount" outerAmount.id "ordinaryNumeric"

private def nestedRepeatableNumericRule? :=
  ordinaryRepeatableNumericRuleAt? ["Order", "Sections", "Items"]
    "InnerAmount" innerAmount.id "nestedNumeric"

private def ancestorCurrentNumericRule? :
    Option (CheckedResolvedValidationRule ordinaryIterationModel) := do
  let numeric ←
    (elaborateRepeatableNumericComparison ordinaryIterationModel
      ["Order", "Sections", "Items"] {
        op := .ordinary .greater
        left := .binary .add
          (.atom (.field
            (ordinaryPath ["Order", "Sections"] "OuterAmount")))
          (.atom (.field
            (ordinaryPath ["Order", "Sections", "Items"] "InnerAmount")))
        right := .literal { value := 4, authoredScale := 0 }
      }).toOption
  let condition ←
    (CheckedValidationCondition.fromOrderedNumeric numeric).toOption
  (assembleResolvedValidationRule ordinaryIterationModel condition innerAmount.id
    "ancestorCurrentNumeric" .error { parts := [] }).toOption

private def directRepeatableNumericLiteralCondition?
    (op : NumericValidationOp) (literalValue : DecodedNumericLiteral)
    (literalOnLeft : Bool := false) :
    Option (CheckedValidationCondition ordinaryIterationModel) := do
  let field : AuthoredNumericExpr SurfaceNumericAtom :=
    .atom (.field
      (ordinaryPath ["Order", "Sections"] "OuterAmount"))
  let literal : AuthoredNumericExpr SurfaceNumericAtom :=
    .literal literalValue
  let numeric ←
    (elaborateRepeatableNumericComparison ordinaryIterationModel
      ["Order", "Sections"] {
        op
        left := if literalOnLeft then literal else field
        right := if literalOnLeft then field else literal
      }).toOption
  (CheckedValidationCondition.fromOrderedNumeric numeric).toOption

private def directRepeatableNumericCondition?
    (op : NumericValidationOp) (expected : Rat)
    (literalOnLeft : Bool := false) :
    Option (CheckedValidationCondition ordinaryIterationModel) :=
  directRepeatableNumericLiteralCondition? op
    { value := expected, authoredScale := 0 } literalOnLeft

private def directRepeatableNumericLiteralLegality?
    (op : NumericValidationOp) (literal : DecodedNumericLiteral)
    (literalOnLeft : Bool := false) :
    Option ValidationCondition.IterationLegality := do
  let condition ←
    directRepeatableNumericLiteralCondition? op literal literalOnLeft
  condition.core.iterationLegality.toOption

private def directRepeatableNumericLegality?
    (op : NumericValidationOp) (expected : Rat)
    (literalOnLeft : Bool := false) :
    Option ValidationCondition.IterationLegality := do
  let condition ←
    directRepeatableNumericCondition? op expected literalOnLeft
  condition.core.iterationLegality.toOption

private def repeatableStringLengthCondition?
    (op : NumericValidationOp) (expected : Rat)
    (literalOnLeft : Bool := false) :
    Option (CheckedValidationCondition ordinaryIterationModel) := do
  let length : AuthoredNumericExpr SurfaceNumericAtom :=
    .atom (.stringLength
      (ordinaryPath ["Order", "Sections", "Items"] "InnerToken"))
  let literal : AuthoredNumericExpr SurfaceNumericAtom :=
    .literal { value := expected, authoredScale := 0 }
  let numeric ←
    (elaborateRepeatableNumericComparison ordinaryIterationModel
      ["Order", "Sections", "Items"] {
        op
        left := if literalOnLeft then literal else length
        right := if literalOnLeft then length else literal
      }).toOption
  (CheckedValidationCondition.fromOrderedNumeric numeric).toOption

private def repeatableStringLengthLegality?
    (op : NumericValidationOp) (expected : Rat)
    (literalOnLeft : Bool := false) :
    Option ValidationCondition.IterationLegality := do
  let condition ←
    repeatableStringLengthCondition? op expected literalOnLeft
  condition.core.iterationLegality.toOption

private def repeatableStringLengthRule? :
    Option (CheckedResolvedValidationRule ordinaryIterationModel) := do
  let condition ←
    repeatableStringLengthCondition? (.ordinary .equal) 3
  (assembleResolvedValidationRule ordinaryIterationModel condition innerToken.id
    "repeatableStringLength" .error { parts := [] }).toOption

private def repeatableFieldValueAsNumberCondition?
    (source : SurfaceTextFieldOperand)
    (op : NumericValidationOp) (expected : Rat)
    (literalOnLeft : Bool := false) :
    Option (CheckedValidationCondition ordinaryIterationModel) := do
  let converted : AuthoredNumericExpr SurfaceNumericAtom :=
    .atom (.fieldValueAsNumber source)
  let literal : AuthoredNumericExpr SurfaceNumericAtom :=
    .literal { value := expected, authoredScale := 0 }
  let numeric ←
    (elaborateRepeatableNumericComparison ordinaryIterationModel
      ["Order", "Sections", "Items"] {
        op
        left := if literalOnLeft then literal else converted
        right := if literalOnLeft then converted else literal
      }).toOption
  (CheckedValidationCondition.fromOrderedNumeric numeric).toOption

private def repeatableFieldValueAsNumberLegality?
    (source : SurfaceTextFieldOperand)
    (op : NumericValidationOp) (expected : Rat)
    (literalOnLeft : Bool := false) :
    Option ValidationCondition.IterationLegality := do
  let condition ←
    repeatableFieldValueAsNumberCondition? source op expected literalOnLeft
  condition.core.iterationLegality.toOption

private def repeatableNumericCode : SurfaceTextFieldOperand :=
  .direct
    (ordinaryPath ["Order", "Sections", "Items"] "InnerNumericCode")

private def repeatableNumericFactor : SurfaceTextFieldOperand :=
  .category
    (ordinaryPath ["Order", "Sections", "Items"] "InnerNumericChoice")
    "Factor"

private def repeatableFieldValueAsNumberRule?
    (source : SurfaceTextFieldOperand) (expected : Rat) (target : FieldId) :
    Option (CheckedResolvedValidationRule ordinaryIterationModel) := do
  let condition ←
    repeatableFieldValueAsNumberCondition? source (.ordinary .equal) expected
  (assembleResolvedValidationRule ordinaryIterationModel condition target
    "repeatableFieldValueAsNumber" .error { parts := [] }).toOption

private def repeatableStringRangeCondition?
    (op : NumericValidationOp) (expected : Rat)
    (start : Nat := 2) (finish : Nat := 3)
    (literalOnLeft : Bool := false) :
    Option (CheckedValidationCondition ordinaryIterationModel) := do
  let range : AuthoredNumericExpr SurfaceNumericAtom :=
    .atom (.stringRange
      (ordinaryPath ["Order", "Sections", "Items"] "InnerToken")
      start finish)
  let literal : AuthoredNumericExpr SurfaceNumericAtom :=
    .literal { value := expected, authoredScale := 0 }
  let numeric ←
    (elaborateRepeatableNumericComparison ordinaryIterationModel
      ["Order", "Sections", "Items"] {
        op
        left := if literalOnLeft then literal else range
        right := if literalOnLeft then range else literal
      }).toOption
  (CheckedValidationCondition.fromOrderedNumeric numeric).toOption

private def repeatableStringRangeLegality?
    (op : NumericValidationOp) (expected : Rat)
    (start : Nat := 2) (finish : Nat := 3)
    (literalOnLeft : Bool := false) :
    Option ValidationCondition.IterationLegality := do
  let condition ←
    repeatableStringRangeCondition? op expected start finish literalOnLeft
  condition.core.iterationLegality.toOption

private def repeatableStringRangeRule?
    (op : NumericValidationOp) (expected : Rat) :
    Option (CheckedResolvedValidationRule ordinaryIterationModel) := do
  let condition ← repeatableStringRangeCondition? op expected
  (assembleResolvedValidationRule ordinaryIterationModel condition innerToken.id
    "repeatableStringRange" .error { parts := [] }).toOption

private def repeatableTemporalPartCondition?
    (field : String) (part : TemporalNumericPart)
    (op : NumericValidationOp) (expected : Rat)
    (literalOnLeft : Bool := false) :
    Option (CheckedValidationCondition ordinaryIterationModel) := do
  let component : AuthoredNumericExpr SurfaceNumericAtom :=
    .atom (.temporalFieldPart
      (ordinaryPath ["Order", "Sections", "Items"] field) part)
  let literal : AuthoredNumericExpr SurfaceNumericAtom :=
    .literal { value := expected, authoredScale := 0 }
  let numeric ←
    (elaborateRepeatableNumericComparison ordinaryIterationModel
      ["Order", "Sections", "Items"] {
        op
        left := if literalOnLeft then literal else component
        right := if literalOnLeft then component else literal
      }).toOption
  (CheckedValidationCondition.fromOrderedNumeric numeric).toOption

private def repeatableTemporalPartLegality?
    (field : String) (part : TemporalNumericPart)
    (op : NumericValidationOp) (expected : Rat)
    (literalOnLeft : Bool := false) :
    Option ValidationCondition.IterationLegality := do
  let condition ←
    repeatableTemporalPartCondition? field part op expected literalOnLeft
  condition.core.iterationLegality.toOption

private def repeatableTemporalPartRule?
    (field : String) (part : TemporalNumericPart)
    (op : NumericValidationOp) (expected : Rat) (target : FieldId) :
    Option (CheckedResolvedValidationRule ordinaryIterationModel) := do
  let condition ← repeatableTemporalPartCondition? field part op expected
  (assembleResolvedValidationRule ordinaryIterationModel condition target
    "repeatableTemporalPart" .error { parts := [] }).toOption

private def repeatableDateDifferenceCondition?
    (unit : DateDifferenceUnit) (left right : String)
    (op : NumericValidationOp) (expected : Rat)
    (literalOnLeft : Bool := false) :
    Option (CheckedValidationCondition ordinaryIterationModel) := do
  let difference : AuthoredNumericExpr SurfaceNumericAtom :=
    .atom (.dateDifference unit
      (.field (ordinaryPath ["Order", "Sections", "Items"] left))
      (.field (ordinaryPath ["Order", "Sections", "Items"] right)))
  let literal : AuthoredNumericExpr SurfaceNumericAtom :=
    .literal { value := expected, authoredScale := 0 }
  let numeric ←
    (elaborateRepeatableNumericComparison ordinaryIterationModel
      ["Order", "Sections", "Items"] {
        op
        left := if literalOnLeft then literal else difference
        right := if literalOnLeft then difference else literal
      }).toOption
  (CheckedValidationCondition.fromOrderedNumeric numeric).toOption

private def repeatableDateDifferenceLegality?
    (op : NumericValidationOp) (expected : Rat)
    (literalOnLeft : Bool := false) :
    Option ValidationCondition.IterationLegality := do
  let condition ← repeatableDateDifferenceCondition? .months
    "InnerDate" "InnerEarlierDate" op expected literalOnLeft
  condition.core.iterationLegality.toOption

private def repeatableDateDifferenceRule?
    (unit : DateDifferenceUnit) (left right : String)
    (op : NumericValidationOp) (expected : Rat) :
    Option (CheckedResolvedValidationRule ordinaryIterationModel) := do
  let condition ←
    repeatableDateDifferenceCondition? unit left right op expected
  (assembleResolvedValidationRule ordinaryIterationModel condition innerDate.id
    "repeatableDateDifference" .error { parts := [] }).toOption

private def compositeRepeatableNumericLegality?
    (op : NumericValidationOp) (expected : Rat) :
    Option ValidationCondition.IterationLegality := do
  let numeric ←
    (elaborateRepeatableNumericComparison ordinaryIterationModel
      ["Order", "Sections"] {
        op
        left := .binary .add
          (.atom (.field
            (ordinaryPath ["Order", "Sections"] "OuterAmount")))
          (.literal { value := 0, authoredScale := 0 })
        right := .literal { value := expected, authoredScale := 0 }
      }).toOption
  let condition ←
    (CheckedValidationCondition.fromOrderedNumeric numeric).toOption
  condition.core.iterationLegality.toOption

private def wrappedRepeatableNumericLegality?
    (wrap : AuthoredNumericExpr SurfaceNumericAtom →
      AuthoredNumericExpr SurfaceNumericAtom)
    (op : NumericValidationOp) (expected : Rat)
    (literalOnLeft : Bool := false) :
    Option ValidationCondition.IterationLegality := do
  let wrapped := wrap (.atom (.field
    (ordinaryPath ["Order", "Sections"] "OuterAmount")))
  let literal : AuthoredNumericExpr SurfaceNumericAtom :=
    .literal { value := expected, authoredScale := 0 }
  let numeric ←
    (elaborateRepeatableNumericComparison ordinaryIterationModel
      ["Order", "Sections"] {
        op
        left := if literalOnLeft then literal else wrapped
        right := if literalOnLeft then wrapped else literal
      }).toOption
  let condition ←
    (CheckedValidationCondition.fromOrderedNumeric numeric).toOption
  condition.core.iterationLegality.toOption

private def deeperInnerAmountStar : SurfaceStarFieldPath :=
  { base := .absolute
    groups := [
      { name := "Order" },
      { name := "Sections" },
      { name := "Items", starred := true }]
    field := "InnerAmount" }

private def deeperInnerPriceStar : SurfaceStarFieldPath :=
  { deeperInnerAmountStar with field := "InnerPrice" }

private def deeperInnerTokenStar : SurfaceStarFieldPath :=
  { deeperInnerAmountStar with field := "InnerToken" }

private def outerWithInnerAggregateCore? :
    Option (OrderedNumericComparison ordinaryIterationModel) := do
  let outerField ← outerAmount.toNumberField?
  let innerSource ←
    (elaborateNumberEntitySource ordinaryIterationModel
      ["Order", "Sections"] {
        first := .star deeperInnerAmountStar
        rest := []
      }).toOption
  let core : OrderedNumericComparison ordinaryIterationModel := {
    op := .ordinary .greater
    left := .binary .add
      (.atom (.ordinary (.field outerField)))
      (.atom (.aggregate .sum innerSource))
    right := .literal { value := 5, authoredScale := 0 }
  }
  pure core

private def outerWithInnerAggregateComparison? :
    Option (CheckedOrderedNumericComparison ordinaryIterationModel) := do
  let core ← outerWithInnerAggregateCore?
  if hCore : core.wellFormedInBool ["Order", "Sections"]
      .sameGroupAddressed = true then
    pure {
      rowGroup := ["Order", "Sections"]
      operandScope := .sameGroupAddressed
      core
      modelWellFormed := by native_decide
      wellFormed := hCore
    }
  else
    none

private def outerWithInnerAggregateRule? :
    Option (CheckedResolvedValidationRule ordinaryIterationModel) := do
  let numeric ← outerWithInnerAggregateComparison?
  let condition ←
    (CheckedValidationCondition.fromOrderedNumeric numeric).toOption
  (assembleResolvedValidationRule ordinaryIterationModel condition outerAmount.id
    "outerWithInnerAggregate" .error { parts := [] }).toOption

private def innerAmountSelfHaving : SurfaceCorrelatedHaving :=
  .compareNumbers .equal
    { origin := .inner
      field := ordinaryPath ["Order", "Sections", "Items"] "InnerAmount" }
    { origin := .inner
      field := ordinaryPath ["Order", "Sections", "Items"] "InnerAmount" }

private def innerAmountBaseHaving : SurfaceCorrelatedHaving :=
  .compareNumbers .notEqual
    { origin := .inner
      field := ordinaryPath ["Order", "Sections", "Items"] "InnerAmount" }
    { origin := .inner
      field := ordinaryPath ["Order"] "BaseAmount" }

private def deeperInnerNumberSource?
    (withFilteredDuplicate : Bool := false) :
    Option (CheckedNumberEntitySource ordinaryIterationModel) :=
  (elaborateNumberEntitySource ordinaryIterationModel
    ["Order", "Sections"] {
      first := .star deeperInnerAmountStar
      rest := if withFilteredDuplicate then
        [.starHaving deeperInnerAmountStar innerAmountSelfHaving]
      else []
    }).toOption

private def mixedDirectStarNumberSource? :
    Option (CheckedNumberEntitySource ordinaryIterationModel) :=
  (elaborateNumberEntitySource ordinaryIterationModel
    ["Order", "Sections"] {
      first := .field (ordinaryPath ["Order"] "BaseAmount")
      rest := [.star deeperInnerAmountStar]
    }).toOption

private def filterMixedReferenceNumberSource? :
    Option (CheckedNumberEntitySource ordinaryIterationModel) :=
  (elaborateNumberEntitySource ordinaryIterationModel
    ["Order", "Sections"] {
      first := .starHaving deeperInnerAmountStar innerAmountBaseHaving
      rest := []
    }).toOption

private def checkedOuterEntityComparison?
    (core : OrderedNumericComparison ordinaryIterationModel) :
    Option (CheckedOrderedNumericComparison ordinaryIterationModel) :=
  if hCore : core.wellFormedInBool ["Order", "Sections"]
      .sameGroupAddressed = true then
    some {
      rowGroup := ["Order", "Sections"]
      operandScope := .sameGroupAddressed
      core
      modelWellFormed := by native_decide
      wellFormed := hCore
    }
  else
    none

private def orderedAtomLiteralLegality?
    (atom : OrderedNumericValidationAtom ordinaryIterationModel)
    (op : NumericValidationOp) (literalValue : DecodedNumericLiteral)
    (literalOnLeft : Bool := false) :
    Option ValidationCondition.IterationLegality := do
  let entity : AuthoredNumericExpr
      (OrderedNumericValidationAtom ordinaryIterationModel) :=
    .atom atom
  let literal : AuthoredNumericExpr
      (OrderedNumericValidationAtom ordinaryIterationModel) :=
    .literal literalValue
  let comparison ← checkedOuterEntityComparison? {
    op
    left := if literalOnLeft then literal else entity
    right := if literalOnLeft then entity else literal
  }
  let condition ←
    (CheckedValidationCondition.fromOrderedNumeric comparison).toOption
  condition.core.iterationLegality.toOption

private def orderedAtomLegality?
    (atom : OrderedNumericValidationAtom ordinaryIterationModel)
    (op : NumericValidationOp) (expected : Rat)
    (literalOnLeft : Bool := false) :
    Option ValidationCondition.IterationLegality :=
  orderedAtomLiteralLegality? atom op
    { value := expected, authoredScale := 0 } literalOnLeft

private def numberEntityLegality?
    (source? : Option
      (CheckedNumberEntitySource ordinaryIterationModel))
    (atomOf : CheckedNumberEntitySource ordinaryIterationModel →
      OrderedNumericValidationAtom ordinaryIterationModel)
    (op : NumericValidationOp) (expected : Rat)
    (literalOnLeft : Bool := false) :
    Option ValidationCondition.IterationLegality := do
  let source ← source?
  orderedAtomLegality? (atomOf source) op expected literalOnLeft

private def plainStarEntityLegality?
    (atomOf : CheckedNumberEntitySource ordinaryIterationModel →
      OrderedNumericValidationAtom ordinaryIterationModel)
    (op : NumericValidationOp) (expected : Rat)
    (literalOnLeft : Bool := false) :
    Option ValidationCondition.IterationLegality :=
  numberEntityLegality? deeperInnerNumberSource? atomOf op expected literalOnLeft

private def mixedDirectStarEntityLegality?
    (atomOf : CheckedNumberEntitySource ordinaryIterationModel →
      OrderedNumericValidationAtom ordinaryIterationModel)
    (op : NumericValidationOp) (expected : Rat)
    (literalOnLeft : Bool := false) :
    Option ValidationCondition.IterationLegality :=
  numberEntityLegality? mixedDirectStarNumberSource?
    atomOf op expected literalOnLeft

private def filteredEntityLegality?
    (atomOf : CheckedNumberEntitySource ordinaryIterationModel →
      OrderedNumericValidationAtom ordinaryIterationModel)
    (op : NumericValidationOp) (expected : Rat) :
    Option ValidationCondition.IterationLegality :=
  numberEntityLegality? (deeperInnerNumberSource? true) atomOf op expected

private def filterMixedReferenceEntityLegality?
    (atomOf : CheckedNumberEntitySource ordinaryIterationModel →
      OrderedNumericValidationAtom ordinaryIterationModel)
    (op : NumericValidationOp) (expected : Rat) :
    Option ValidationCondition.IterationLegality :=
  numberEntityLegality? filterMixedReferenceNumberSource?
    atomOf op expected

private def plainStarTokenValueCountSource? :
    Option (CheckedTokenValueCountSource ordinaryIterationModel) :=
  (elaborateTokenValueCountSource ordinaryIterationModel
    ["Order", "Sections"] "A" {
      first := .star deeperInnerTokenStar .stored
      rest := []
    }).toOption

private def mixedTokenValueCountSource? :
    Option (CheckedTokenValueCountSource ordinaryIterationModel) :=
  (elaborateTokenValueCountSource ordinaryIterationModel
    ["Order", "Sections"] "A" {
      first := .field (.direct (ordinaryPath ["Order"] "BaseToken"))
      rest := [.star deeperInnerTokenStar .stored]
    }).toOption

private def tokenValueCountLegality?
    (source? : Option
      (CheckedTokenValueCountSource ordinaryIterationModel))
    (op : NumericValidationOp) (expected : Rat)
    (literalOnLeft : Bool := false) :
    Option ValidationCondition.IterationLegality := do
  let source ← source?
  orderedAtomLegality? (.tokenValueCount source)
    op expected literalOnLeft

private def outerWithInnerTokenValueCountRule? :
    Option (CheckedResolvedValidationRule ordinaryIterationModel) := do
  let outerField ← outerAmount.toNumberField?
  let source ← plainStarTokenValueCountSource?
  let comparison ← checkedOuterEntityComparison? {
    op := .ordinary .greater
    left := .binary .add
      (.atom (.ordinary (.field outerField)))
      (.atom (.tokenValueCount source))
    right := .literal { value := 2, authoredScale := 0 }
  }
  let condition ←
    (CheckedValidationCondition.fromOrderedNumeric comparison).toOption
  (assembleResolvedValidationRule ordinaryIterationModel condition outerAmount.id
    "outerWithInnerTokenValueCount" .error { parts := [] }).toOption

private def mixedScopeWrappedNumericLegality?
    (op : NumericValidationOp) (expected : Rat) :
    Option ValidationCondition.IterationLegality := do
  let numeric ←
    (elaborateRepeatableNumericComparison ordinaryIterationModel
      ["Order", "Sections", "Items"] {
        op
        left := .extremumCall .minimum
          (.extremum .minimum
            (.atom (.field
              (ordinaryPath ["Order", "Sections"] "OuterAmount")))
            (.atom (.field
              (ordinaryPath ["Order", "Sections", "Items"]
                "InnerAmount"))))
        right := .literal { value := expected, authoredScale := 0 }
      }).toOption
  let condition ←
    (CheckedValidationCondition.fromOrderedNumeric numeric).toOption
  condition.core.iterationLegality.toOption

private def plainStarProductCondition?
    (op : NumericValidationOp) (expected : Rat) :
    Option (CheckedValidationCondition ordinaryIterationModel) := do
  let source ←
    (elaborateNumericProductAggregate ordinaryIterationModel
      ["Order", "Sections"] {
        left := deeperInnerAmountStar
        right := deeperInnerPriceStar
      }).toOption
  let comparison ← checkedOuterEntityComparison? {
    op
    left := .atom (.sumOfProducts source)
    right := .literal { value := expected, authoredScale := 0 }
  }
  (CheckedValidationCondition.fromOrderedNumeric comparison).toOption

private def plainStarProductLegality?
    (op : NumericValidationOp) (expected : Rat) :
    Option ValidationCondition.IterationLegality := do
  let condition ← plainStarProductCondition? op expected
  condition.core.iterationLegality.toOption

private def guardedPlainStarProductRule? :
    Option (CheckedResolvedValidationRule ordinaryIterationModel) := do
  let outer ←
    (CheckedValidationCondition.fromRepeatableFieldPresence
      ordinaryIterationModel ["Order", "Sections"] .filled
      (ordinaryPath ["Order", "Sections"] "OuterAmount")).toOption
  let product ←
    plainStarProductCondition? (.ordinary .greater) 0
  let condition ← (outer.and product).toOption
  (assembleResolvedValidationRule ordinaryIterationModel condition
    outerAmount.id "guardedProduct" .error { parts := [] }).toOption

private def outerWithInnerEntityComparison?
    (atom : OrderedNumericValidationAtom ordinaryIterationModel)
    (right : Rat) :
    Option (CheckedOrderedNumericComparison ordinaryIterationModel) := do
  let outerField ← outerAmount.toNumberField?
  checkedOuterEntityComparison? {
    op := .ordinary .equal
    left := .binary .add
      (.atom (.ordinary (.field outerField)))
      (.atom atom)
    right := .literal { value := right, authoredScale := 0 }
  }

private def outerWithInnerFirstFilledComparison? :
    Option (CheckedOrderedNumericComparison ordinaryIterationModel) := do
  let source ← deeperInnerNumberSource?
  outerWithInnerEntityComparison? (.firstFilled source) 5

private def outerWithInnerValueCountComparison? :
    Option (CheckedOrderedNumericComparison ordinaryIterationModel) := do
  let source ← deeperInnerNumberSource?
  outerWithInnerEntityComparison? (.valueCount 4 source) 2

private def outerWithFilteredInnerFirstFilledComparison? :
    Option (CheckedOrderedNumericComparison ordinaryIterationModel) := do
  let source ← deeperInnerNumberSource? true
  outerWithInnerEntityComparison? (.firstFilled source) 5

private def outerWithFilteredInnerValueCountComparison? :
    Option (CheckedOrderedNumericComparison ordinaryIterationModel) := do
  let source ← deeperInnerNumberSource? true
  outerWithInnerEntityComparison? (.valueCount 4 source) 3

private def outerWithInnerEntityRule?
    (comparison :
      Option (CheckedOrderedNumericComparison ordinaryIterationModel))
    (errorCode : String) :
    Option (CheckedResolvedValidationRule ordinaryIterationModel) := do
  let numeric ← comparison
  let condition ←
    (CheckedValidationCondition.fromOrderedNumeric numeric).toOption
  (assembleResolvedValidationRule ordinaryIterationModel condition outerAmount.id
    errorCode .error { parts := [] }).toOption

private def outerWithInnerFirstFilledRule? :=
  outerWithInnerEntityRule? outerWithInnerFirstFilledComparison?
    "outerWithInnerFirstFilled"

private def outerWithInnerValueCountRule? :=
  outerWithInnerEntityRule? outerWithInnerValueCountComparison?
    "outerWithInnerValueCount"

private def outerWithFilteredInnerFirstFilledRule? :=
  outerWithInnerEntityRule? outerWithFilteredInnerFirstFilledComparison?
    "outerWithFilteredInnerFirstFilled"

private def outerWithFilteredInnerValueCountRule? :=
  outerWithInnerEntityRule? outerWithFilteredInnerValueCountComparison?
    "outerWithFilteredInnerValueCount"

/- Nested compatible ordinary references derive the deepest scope from the checked tree; the declaring group and error-field argument cannot override it. -/
example :
    (ordinaryIterationRule?.map fun rule =>
      (rule.iterationScope, rule.errorDeclaration.repeatableScope)) =
      some (some [10, 20], [10, 20]) := by
  native_decide

/- Date-only completed-period differences preserve their two ordered checked operands while sharing the direct-operation host-zero branch. -/
example :
    repeatableDateDifferenceLegality? (.ordinary .equal) 0 =
      some (.invalid 10) ∧
    repeatableDateDifferenceLegality? (.ordinary .equal) 0 true =
      some (.invalid 10) ∧
    repeatableDateDifferenceLegality? (.ordinary .equal) 17 =
      some .legal ∧
    (repeatableDateDifferenceCondition? .years
      "InnerDateTime" "InnerEarlierDate" (.ordinary .equal) 1).isNone := by
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

/- A repeatable Number comparison must enter the existing ordered numeric condition carrier and derive the current-row scope without a new expression tree. -/
example :
    (ordinaryRepeatableNumericRule?.map fun rule =>
      (rule.iterationScope, rule.requiresAddressedValidation)) =
      some (some [10], true) ∧
    (nestedRepeatableNumericRule?.map fun rule =>
      (rule.iterationScope, rule.requiresAddressedValidation)) =
      some (some [10, 20], true) := by
  native_decide

/- A checked deeper-star aggregate composes with the ordinary current-row Number under the same addressed numeric tree; the star contributes only its captured outer binding to whole-rule iteration. -/
example :
    (outerWithInnerAggregateRule?.map fun rule =>
      (rule.iterationScope, rule.requiresAddressedValidation)) =
      some (some [10], true) := by
  native_decide

/- The existing checked prefix and counting sources enter the same addressed whole-rule bridge and contribute only the fixed outer binding above their reopened star. -/
example :
    (outerWithInnerFirstFilledRule?.map fun rule =>
      (rule.iterationScope, rule.requiresAddressedValidation)) =
        some (some [10], true) ∧
      (outerWithInnerValueCountRule?.map fun rule =>
        (rule.iterationScope, rule.requiresAddressedValidation)) =
        some (some [10], true) := by
  native_decide

/- Ordinary group paths and `RuleGroup` retain distinct authored origins while deriving the same current-row scope. -/
example :
    (outerGroupPathRule?.map fun rule =>
      (rule.iterationScope, rule.requiresAddressedValidation,
        match rule.condition.core with
        | .leaf (.groupPresence _ reference) => reference.origin
        | _ => .ruleGroup)) =
        some (some [10], true, .path) ∧
    (outerRuleGroupRule?.map fun rule =>
      (rule.iterationScope, rule.requiresAddressedValidation,
        match rule.condition.core with
        | .leaf (.groupPresence _ reference) => reference.origin
        | _ => .path)) =
        some (some [10], true, .ruleGroup) := by
  native_decide

/- The addressed entry rejects a scalar-only comparison because the established scalar elaborator already owns that representation. -/
example :
    (elaborateNumericComparison model ["Order"] amountPositive).isOk = true ∧
      (elaborateRepeatableNumericComparison
        model ["Order"] amountPositive).isOk = false := by
  native_decide

private def outerEmptyCondition? :
    Option (CheckedValidationCondition ordinaryIterationModel) :=
  (CheckedValidationCondition.fromRepeatableFieldPresence
    ordinaryIterationModel ["Order"] .notFilled
    (ordinaryPath ["Order", "Sections"] "OuterAmount")).toOption

private def outerEmptyRule? :
    Option (CheckedResolvedValidationRule ordinaryIterationModel) := do
  let condition ← outerEmptyCondition?
  (assembleResolvedValidationRule ordinaryIterationModel condition outerAmount.id
    "outerEmpty" .error { parts := [] }).toOption

private def ordinaryAssemblyError?
    (condition? : Option
      (CheckedValidationCondition ordinaryIterationModel))
    (target : FlatFieldDecl) : Option FlatRuleAssemblyError := do
  let condition ← condition?
  match assembleResolvedValidationRule ordinaryIterationModel condition target.id
      "iterationLegality" .error { parts := [] } with
  | .ok _ => none
  | .error error => some error

private def outerGroupEmptyCondition? :
    Option (CheckedValidationCondition ordinaryIterationModel) :=
  (CheckedValidationCondition.fromGroupPresence ordinaryIterationModel
    ["Order"] (absoluteGroup ["Order", "Sections"]) .notFilled).toOption

private def guardedOrMissingInnerLevelCondition? :
    Option (CheckedValidationCondition ordinaryIterationModel) := do
  let outer ← outerIterationCondition?
  let innerGroup ← innerGroupFilledCondition?
  (outer.or innerGroup).toOption

private def guardedOuterOrCondition? :
    Option (CheckedValidationCondition ordinaryIterationModel) := do
  let outer ← outerIterationCondition?
  let outerGroup ←
    (CheckedValidationCondition.fromGroupPresence ordinaryIterationModel
      ["Order"] (absoluteGroup ["Order", "Sections"]) .filled).toOption
  (outer.or outerGroup).toOption

/- Per-level static legality rejects pure negative field and group conditions at their outer repeatable level. -/
example :
    outerEmptyRule?.isNone = true ∧
    ordinaryAssemblyError? outerEmptyCondition? outerAmount =
      some (.negativeConditionInIteration 10) ∧
    ordinaryAssemblyError? outerGroupEmptyCondition? outerAmount =
      some (.negativeConditionInIteration 10) := by
  native_decide

/- Direct iterating Number comparisons against host-converted zero reproduce the source visitor's exact operator partition in both operand orders. -/
example :
    directRepeatableNumericLegality? (.ordinary .equal) 0 =
      some (.invalid 10) ∧
    directRepeatableNumericLegality? (.ordinary .lessEqual) 0 =
      some (.invalid 10) ∧
    directRepeatableNumericLegality? (.ordinary .greaterEqual) 0 =
      some (.invalid 10) ∧
    directRepeatableNumericLegality? (.ordinary .equal) 0 true =
      some (.invalid 10) ∧
    ordinaryAssemblyError?
      (directRepeatableNumericCondition? (.ordinary .equal) 0)
      outerAmount = some (.negativeConditionInIteration 10) := by
  native_decide

/- Strict, not-equal, tolerance, and converted-nonzero controls are admitted; a rational that is not representable at its asserted authored scale remains explicitly unclassified. -/
example :
    directRepeatableNumericLegality? (.ordinary .notEqual) 0 =
      some .legal ∧
    directRepeatableNumericLegality? (.ordinary .less) 0 =
      some .legal ∧
    directRepeatableNumericLegality? (.ordinary .greater) 0 =
      some .legal ∧
    directRepeatableNumericLegality? (.tolerance .range1) 0 =
      some .legal ∧
    directRepeatableNumericLegality? (.ordinary .equal) 1 =
      some .legal ∧
    directRepeatableNumericLegality? (.ordinary .equal) (2 / 5) =
      some (.insufficient 10) := by
  native_decide

private def halfTieFromBelow : DecodedNumericLiteral :=
  { value := (1 / 2 : Rat) - 1 / (2 ^ 55)
    authoredScale := 55 }

private def belowHalfTie : DecodedNumericLiteral :=
  { value := halfTieFromBelow.value - 1 / (10 ^ 56)
    authoredScale := 56 }

/- The pure conversion owner also retains Java's asymmetric half rounding, long saturation, signed-int wrap, and the checked finite-decimal representation boundary. -/
example :
    DecodedNumericLiteral.iterationHostInt32?
      { value := -1 / 2, authoredScale := 1 } = some 0 ∧
    DecodedNumericLiteral.iterationHostInt32?
      { value := -51 / 100, authoredScale := 2 } = some (-1) ∧
    DecodedNumericLiteral.iterationHostInt32?
      { value := 9223372036854775807, authoredScale := 0 } = some (-1) ∧
    DecodedNumericLiteral.iterationHostInt32?
      { value := -9223372036854775808, authoredScale := 0 } = some 0 ∧
    DecodedNumericLiteral.iterationHostInt32?
      { value := 2 / 5, authoredScale := 0 } = none ∧
    DecodedNumericLiteral.iterationHostInt32?
      { value := 1, authoredScale := -1 } = none := by
  native_decide

/- The checked decimal carrier is sufficient for the kernel host conversion. Binary64 tie-to-even can move an exact value below one half onto one half; Java rounding and signed-32-bit narrowing then determine the static zero test. -/
example :
    directRepeatableNumericLiteralLegality? (.ordinary .greaterEqual)
      { value := 2 / 5, authoredScale := 1 } =
        some (.invalid 10) ∧
    directRepeatableNumericLiteralLegality? (.ordinary .greaterEqual)
      { value := 1 / 2, authoredScale := 1 } =
        some .legal ∧
    directRepeatableNumericLiteralLegality? (.ordinary .greaterEqual)
      halfTieFromBelow = some .legal ∧
    directRepeatableNumericLiteralLegality? (.ordinary .greaterEqual)
      belowHalfTie = some (.invalid 10) ∧
    directRepeatableNumericLiteralLegality? (.ordinary .equal)
      { value := 4294967296, authoredScale := 0 } =
        some (.invalid 10) ∧
    directRepeatableNumericLiteralLegality? (.ordinary .equal)
      { value := 4294967297, authoredScale := 0 } =
        some .legal := by
  native_decide

/- An outer guard cannot legalize an inner negative condition: the first unguarded level remains explicit. Adding the existing inner group-presence guard closes that same level. -/
example :
    (nestedUnguardedCondition?.bind fun condition =>
      condition.core.iterationLegality.toOption) = some (.invalid 20) ∧
    (ordinaryIterationCondition?.bind fun condition =>
      condition.core.iterationLegality.toOption) = some .legal := by
  native_decide

/- `Or` requires every branch to reference and guard each selected level. Two outer guards are legal, but an outer-only branch does not guard the inner level selected by its sibling. -/
example :
    (guardedOuterOrCondition?.bind fun condition =>
      condition.core.iterationLegality.toOption) = some .legal ∧
    (guardedOrMissingInnerLevelCondition?.bind fun condition =>
      condition.core.iterationLegality.toOption) = some (.invalid 20) := by
  native_decide

/- A top-level composite arithmetic operation is admitted even where its direct field/zero counterpart is rejected; the source visitor's direct-zero branch does not erase parse-tree topology. -/
example :
    compositeRepeatableNumericLegality? (.ordinary .equal) 0 =
        some .legal ∧
    (ordinaryRepeatableNumericRule?.bind fun rule =>
      rule.condition.core.iterationLegality.toOption) =
        some .legal ∧
    (nestedRepeatableNumericRule?.bind fun rule =>
      rule.condition.core.iterationLegality.toOption) =
        some .legal := by
  native_decide

/- Direct-field operation-list wrappers retain their distinct zero guard while sharing the same checked expression tree. -/
example :
    wrappedRepeatableNumericLegality? (fun body => .abs body)
      (.ordinary .equal) 0 = some (.invalid 10) ∧
    wrappedRepeatableNumericLegality? (fun body => .abs body)
      (.ordinary .equal) 0 true = some (.invalid 10) ∧
    wrappedRepeatableNumericLegality?
      (fun body => .round .floor omittedRoundingPlaces body)
      (.ordinary .greaterEqual) 0 = some (.invalid 10) ∧
    wrappedRepeatableNumericLegality? (fun body => .abs body)
      (.ordinary .notEqual) 0 = some .legal ∧
    wrappedRepeatableNumericLegality?
      (fun body => .round .floor omittedRoundingPlaces body)
      (.ordinary .equal) 1 = some .legal := by
  native_decide

/- Evaluated String `Length` is a direct field operation with the same host-zero branch; its own repeatable field supplies the ordinary scope. -/
example :
    repeatableStringLengthLegality? (.ordinary .equal) 0 =
      some (.invalid 10) ∧
    repeatableStringLengthLegality? (.ordinary .greaterEqual) 0 =
      some (.invalid 10) ∧
    repeatableStringLengthLegality? (.ordinary .lessEqual) 0 =
      some (.invalid 10) ∧
    repeatableStringLengthLegality? (.ordinary .equal) 0 true =
      some (.invalid 10) ∧
    repeatableStringLengthLegality? (.ordinary .greaterEqual) 0 true =
      some (.invalid 10) ∧
    repeatableStringLengthLegality? (.ordinary .equal) 1 =
      some .legal ∧
    repeatableStringLengthLegality? (.ordinary .less) 0 =
      some .legal := by
  native_decide

/- `FieldValueAsNumber` retains its checked String or category projection while sharing the direct-operation host-zero branch. -/
example :
    repeatableFieldValueAsNumberLegality? repeatableNumericCode
        (.ordinary .equal) 0 =
      some (.invalid 10) ∧
    repeatableFieldValueAsNumberLegality? repeatableNumericCode
        (.ordinary .equal) 0 true =
      some (.invalid 10) ∧
    repeatableFieldValueAsNumberLegality? repeatableNumericCode
        (.ordinary .equal) 7 =
      some .legal ∧
    repeatableFieldValueAsNumberLegality? repeatableNumericFactor
        (.ordinary .greaterEqual) 0 =
      some (.invalid 10) ∧
    repeatableFieldValueAsNumberLegality? repeatableNumericFactor
        (.ordinary .less) 0 =
      some .legal := by
  native_decide

/- `RangeAsNumber` retains its checked interval while sharing the direct-operation host-zero branch. -/
example :
    repeatableStringRangeLegality? (.ordinary .equal) 0 =
      some (.invalid 10) ∧
    repeatableStringRangeLegality? (.ordinary .equal) 0 2 3 true =
      some (.invalid 10) ∧
    repeatableStringRangeLegality? (.ordinary .equal) 12 =
      some .legal ∧
    repeatableStringRangeLegality? (.ordinary .less) 0 =
      some .legal ∧
    repeatableStringRangeLegality? (.ordinary .equal) 12 0 3 =
      none := by
  native_decide

/- Direct temporal component extraction retains its kind/component certificate while sharing the direct-operation host-zero branch. -/
example :
    repeatableTemporalPartLegality? "InnerDate" (.date .day)
        (.ordinary .equal) 0 =
      some (.invalid 10) ∧
    repeatableTemporalPartLegality? "InnerTime" (.time .second)
        (.ordinary .equal) 0 true =
      some (.invalid 10) ∧
    repeatableTemporalPartLegality? "InnerDateTime" (.date .quarter)
        (.ordinary .equal) 2 =
      some .legal ∧
    repeatableTemporalPartLegality? "InnerDate" (.time .hour)
        (.ordinary .equal) 5 =
      none ∧
    repeatableTemporalPartLegality? "InnerTime" (.date .year)
        (.ordinary .equal) 2024 =
      none := by
  native_decide

/- Single-field operand-list Min/Max calls retain the same top-level operation-list guard without being flattened into direct fields. -/
example :
    wrappedRepeatableNumericLegality?
      (fun body => .extremumCall .minimum body)
      (.ordinary .lessEqual) 0 = some (.invalid 10) ∧
    wrappedRepeatableNumericLegality?
      (fun body => .extremumCall .minimum
        (.extremum .minimum body body))
      (.ordinary .equal) 0 = some (.invalid 10) ∧
    wrappedRepeatableNumericLegality?
      (fun body => .extremumCall .maximum body)
      (.ordinary .notEqual) 0 = some .legal := by
  native_decide

/- Plain-star entity-list operations retain distinct zero and positive-threshold admission families. -/
example :
    plainStarEntityLegality? (fun source => .firstFilled source)
      (.ordinary .equal) 0 = some (.invalid 10) ∧
    plainStarEntityLegality? (fun source => .valueCount 4 source)
      (.ordinary .equal) 0 = some (.invalid 10) ∧
    plainStarEntityLegality? (fun source => .aggregate .sum source)
      (.ordinary .greaterEqual) 0 = some (.invalid 10) ∧
    plainStarEntityLegality?
      (fun source => .aggregate .distinctCount source)
      (.ordinary .equal) 0 = some .legal ∧
    plainStarEntityLegality?
      (fun source => .aggregate .distinctCount source)
      (.ordinary .lessEqual) 1 = some (.invalid 10) ∧
    plainStarEntityLegality?
      (fun source => .aggregate .distinctCount source)
      (.ordinary .greaterEqual) 1 true = some (.invalid 10) ∧
    plainStarEntityLegality? (fun source => .firstFilled source)
      (.ordinary .notEqual) 1 = some .legal ∧
    plainStarEntityLegality? (fun source => .valueCount 4 source)
      (.ordinary .notEqual) 1 = some (.invalid 10) := by
  native_decide

/- Mixed-scope operation lists remain all-iterating at their common outer level but reject every numeric-constant comparison at the inner level where one reference stops iterating. -/
example :
    mixedScopeWrappedNumericLegality? (.ordinary .equal) 0 =
        some (.invalid 10) ∧
    mixedScopeWrappedNumericLegality? (.ordinary .equal) 1 =
        some (.invalid 20) ∧
    mixedScopeWrappedNumericLegality? (.ordinary .greater) 1 =
        some (.invalid 20) := by
  native_decide

/- A direct-plus-star entity list is mixed at the star's surrounding level, so every immediate numeric literal is rejected without consulting comparison direction or host conversion. -/
example :
    mixedDirectStarEntityLegality?
      (fun source => .aggregate .sum source)
      (.ordinary .equal) 1 = some (.invalid 10) ∧
    mixedDirectStarEntityLegality?
      (fun source => .firstFilled source)
      (.ordinary .notEqual) (-1) true = some (.invalid 10) ∧
    mixedDirectStarEntityLegality?
      (fun source => .aggregate .distinctCount source)
      (.ordinary .equal) 0 = some (.invalid 10) ∧
    mixedDirectStarEntityLegality?
      (fun source => .valueCount 4 source)
      (.ordinary .greater) (2 / 5) = some (.invalid 10) := by
  native_decide

/- `Having` references do not participate in the operation-list reference classifier. A filtered target keeps its own star scope even when its filter also reads a noniterating field. -/
example :
    filteredEntityLegality?
      (fun source => .aggregate .sum source)
      (.ordinary .equal) 1 = some .legal ∧
    filteredEntityLegality?
      (fun source => .aggregate .sum source)
      (.ordinary .equal) 0 = some (.invalid 10) ∧
    filteredEntityLegality?
      (fun source => .aggregate .distinctCount source)
      (.ordinary .equal) 0 = some .legal ∧
    filterMixedReferenceEntityLegality?
      (fun source => .aggregate .sum source)
      (.ordinary .equal) 1 = some .legal := by
  native_decide

/- String/Enumeration `NumberOfValueInFields` has the same zero and positive-threshold sensitivities as its Number overload. A mixed direct/star target list takes the stronger any-literal branch. -/
example :
    tokenValueCountLegality? plainStarTokenValueCountSource?
      (.ordinary .equal) 0 = some (.invalid 10) ∧
    tokenValueCountLegality? plainStarTokenValueCountSource?
      (.ordinary .lessEqual) 1 = some (.invalid 10) ∧
    tokenValueCountLegality? plainStarTokenValueCountSource?
      (.ordinary .greaterEqual) 1 true = some (.invalid 10) ∧
    tokenValueCountLegality? plainStarTokenValueCountSource?
      (.ordinary .equal) 1 = some .legal ∧
    tokenValueCountLegality? mixedTokenValueCountSource?
      (.ordinary .greater) (2 / 5) = some (.invalid 10) := by
  native_decide

/- Positive-threshold classification observes the same narrowed host integer rather than the exact positive decimal. -/
example :
    (plainStarTokenValueCountSource?.bind fun source =>
      orderedAtomLiteralLegality? (.tokenValueCount source)
        (.ordinary .less)
        { value := 4294967296, authoredScale := 0 }) =
      some .legal ∧
    (plainStarTokenValueCountSource?.bind fun source =>
      orderedAtomLiteralLegality? (.tokenValueCount source)
        (.ordinary .less)
        { value := 4294967297, authoredScale := 0 }) =
      some (.invalid 10) := by
  native_decide

/- `SumOfProducts` shares only the plain-star zero-sensitive branch; a positive not-equal threshold remains admitted. -/
example :
    plainStarProductLegality? (.ordinary .equal) 0 =
        some (.invalid 10) ∧
    plainStarProductLegality? (.ordinary .notEqual) 1 =
        some .legal ∧
    (guardedPlainStarProductRule?.map fun rule =>
      (rule.iterationScope, rule.condition.core.iterationLegality.toOption,
        rule.requiresAddressedValidation)) =
      some (some [10], some .legal, true) := by
  native_decide

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

private def repeatableStringLengthData : DocumentData :=
  { instantiatedRows := [
      { group := 10, path := [1] },
      { group := 20, path := [1, 1] }]
    cells := [{
      address := { field := innerToken.id, path := [1, 1] }
      stored := "ABC"
      raw := .parsed (.str "ABC")
    }] }

private def repeatableStringLengthSnapshot? :
    Option (Option (List RepeatableLevel) × Bool ×
      List (Env × Verdict × Option CellAddr)) := do
  let rule ← repeatableStringLengthRule?
  let outcomes ← evalOrdinaryRule? rule repeatableStringLengthData
  pure (
    rule.iterationScope,
    rule.requiresAddressedValidation,
    outcomes.map fun entry =>
      (entry.1, entry.2.verdict,
        entry.2.message?.map (·.errorAddress)))

private def repeatableStringLengthStructuralFailure? :
    Option CheckedAddressingError := do
  let rule ← repeatableStringLengthRule?
  let prepared ←
    (prepareFlatStringContext defaultWorld builtinStringPatternCompiler
      ordinaryIterationModel).toOption
  let document ←
    (checkDocument prepared "en_US" repeatableStringLengthData).toOption
  let context : AddressedValidationEvaluationContext ordinaryIterationModel := {
    scalar := {
      fields := document.flatContext
      groups := GroupPresenceContext.unavailable
    }
    outer := []
    input := .checked document
  }
  match rule.condition.core.evalAddressed context with
  | .ok _ => none
  | .error error => some error

/- Addressed `Length` reads the checked evaluated String through the existing UTF-16 owner, attaches the message to the complete current row, and preserves a missing binding structurally. -/
example :
    (repeatableStringLengthSnapshot? ==
      some (
        some [10, 20],
        true,
        [(
          [(10, 1), (20, 1)],
          .fired .value,
          some { field := innerToken.id, path := [1, 1] })])) = true ∧
      repeatableStringLengthStructuralFailure? =
        some (.environment (.missingBinding 10)) := by
  native_decide

private def repeatableFieldValueAsNumberData : DocumentData :=
  { instantiatedRows := [
      { group := 10, path := [1] },
      { group := 20, path := [1, 1] }]
    cells := [
      { address := { field := innerNumericCode.id, path := [1, 1] }
        stored := "007"
        raw := .parsed (.str "007") },
      { address := { field := innerNumericChoice.id, path := [1, 1] }
        stored := "1.50"
        raw := .parsed (.enum "1.50") }] }

private def repeatableFieldValueAsNumberSnapshot?
    (source : SurfaceTextFieldOperand) (expected : Rat) (target : FieldId) :
    Option (Option (List RepeatableLevel) × Bool ×
      List (Env × Verdict × Option CellAddr)) := do
  let rule ← repeatableFieldValueAsNumberRule? source expected target
  let outcomes ← evalOrdinaryRule? rule repeatableFieldValueAsNumberData
  pure (
    rule.iterationScope,
    rule.requiresAddressedValidation,
    outcomes.map fun entry =>
      (entry.1, entry.2.verdict,
        entry.2.message?.map (·.errorAddress)))

private def repeatableFieldValueAsNumberStructuralFailure? :
    Option CheckedAddressingError := do
  let rule ←
    repeatableFieldValueAsNumberRule? repeatableNumericFactor 15
      innerNumericChoice.id
  let prepared ←
    (prepareFlatStringContext defaultWorld builtinStringPatternCompiler
      ordinaryIterationModel).toOption
  let document ←
    (checkDocument prepared "en_US"
      repeatableFieldValueAsNumberData).toOption
  let context : AddressedValidationEvaluationContext ordinaryIterationModel := {
    scalar := {
      fields := document.flatContext
      groups := GroupPresenceContext.unavailable
    }
    outer := []
    input := .checked document
  }
  match rule.condition.core.evalAddressed context with
  | .ok _ => none
  | .error error => some error

private def repeatableFieldValueAsNumberRejectedVerdict? : Option Verdict := do
  let rule ←
    repeatableFieldValueAsNumberRule? repeatableNumericCode 7
      innerNumericCode.id
  let data : DocumentData := {
    instantiatedRows := [
      { group := 10, path := [1] },
      { group := 20, path := [1, 1] }]
    cells := [{
      address := { field := innerNumericCode.id, path := [1, 1] }
      stored := "ABC"
      raw := .parsed (.str "ABC")
    }] }
  let outcomes ← evalOrdinaryRule? rule data
  outcomes.head?.map (·.2.verdict)

/- Addressed conversion reuses the checked String policy and exact Enumeration category projection; a missing outer binding remains structural. -/
example :
    (repeatableFieldValueAsNumberSnapshot? repeatableNumericCode 7
      innerNumericCode.id ==
      some (
        some [10, 20],
        true,
        [(
          [(10, 1), (20, 1)],
          .fired .value,
          some { field := innerNumericCode.id, path := [1, 1] })])) = true ∧
    (repeatableFieldValueAsNumberSnapshot? repeatableNumericFactor 15
      innerNumericChoice.id ==
      some (
        some [10, 20],
        true,
        [(
          [(10, 1), (20, 1)],
          .fired .value,
          some { field := innerNumericChoice.id, path := [1, 1] })])) = true ∧
    repeatableFieldValueAsNumberRejectedVerdict? = some .unknown ∧
    repeatableFieldValueAsNumberStructuralFailure? =
      some (.environment (.missingBinding 10)) := by
  native_decide

private def repeatableStringRangeData (raw : Option RawCell) : DocumentData :=
  { instantiatedRows := [
      { group := 10, path := [1] },
      { group := 20, path := [1, 1] }]
    cells := match raw with
      | none => []
      | some cell => [{
          address := { field := innerToken.id, path := [1, 1] }
          stored := match cell with
            | .parsed (.str value) => value
            | _ => ""
          raw := cell
        }] }

private def repeatableStringRangeSnapshot?
    (op : NumericValidationOp) (expected : Rat) (raw : Option RawCell) :
    Option (Option (List RepeatableLevel) × Bool ×
      List (Env × Verdict × Option CellAddr)) := do
  let rule ← repeatableStringRangeRule? op expected
  let outcomes ← evalOrdinaryRule? rule (repeatableStringRangeData raw)
  pure (
    rule.iterationScope,
    rule.requiresAddressedValidation,
    outcomes.map fun entry =>
      (entry.1, entry.2.verdict,
        entry.2.message?.map (·.errorAddress)))

private def repeatableStringRangeStructuralFailure? :
    Option CheckedAddressingError := do
  let rule ← repeatableStringRangeRule? (.ordinary .equal) 12
  let prepared ←
    (prepareFlatStringContext defaultWorld builtinStringPatternCompiler
      ordinaryIterationModel).toOption
  let document ←
    (checkDocument prepared "en_US"
      (repeatableStringRangeData (some (.parsed (.str "A12B"))))).toOption
  let context : AddressedValidationEvaluationContext ordinaryIterationModel := {
    scalar := {
      fields := document.flatContext
      groups := GroupPresenceContext.unavailable
    }
    outer := []
    input := .checked document
  }
  match rule.condition.core.evalAddressed context with
  | .ok _ => none
  | .error error => some error

/- Addressed range selection reuses the checked normalized String. Missing input keeps grow-only omission polarity, a present nondigit fallback is fixed VALUE zero, and missing bindings remain structural. -/
example :
    (repeatableStringRangeSnapshot? (.ordinary .equal) 12
      (some (.parsed (.str "A12B"))) ==
      some (
        some [10, 20],
        true,
        [(
          [(10, 1), (20, 1)],
          .fired .value,
          some { field := innerToken.id, path := [1, 1] })])) = true ∧
    (repeatableStringRangeSnapshot? (.ordinary .less) 100 none ==
      some (
        some [10, 20],
        true,
        [(
          [(10, 1), (20, 1)],
          .fired .omission,
          some { field := innerToken.id, path := [1, 1] })])) = true ∧
    (repeatableStringRangeSnapshot? (.ordinary .less) 100
      (some (.parsed (.str "ABCD"))) ==
      some (
        some [10, 20],
        true,
        [(
          [(10, 1), (20, 1)],
          .fired .value,
          some { field := innerToken.id, path := [1, 1] })])) = true ∧
    repeatableStringRangeStructuralFailure? =
      some (.environment (.missingBinding 10)) := by
  native_decide

private def repeatableTemporalPartData
    (field : FieldId) (stored : String) (raw : Option RawCell) :
    DocumentData :=
  { instantiatedRows := [
      { group := 10, path := [1] },
      { group := 20, path := [1, 1] }]
    cells := raw.toList.map fun cell => {
      address := { field, path := [1, 1] }
      stored
      raw := cell } }

private def repeatableTemporalPartSnapshot?
    (fieldName : String) (field : FieldId) (part : TemporalNumericPart)
    (op : NumericValidationOp) (expected : Rat)
    (stored : String) (raw : Option RawCell) :
    Option (Option (List RepeatableLevel) × Bool ×
      List (Env × Verdict × Option CellAddr)) := do
  let rule ← repeatableTemporalPartRule? fieldName part op expected field
  let outcomes ←
    evalOrdinaryRule? rule (repeatableTemporalPartData field stored raw)
  pure (
    rule.iterationScope,
    rule.requiresAddressedValidation,
    outcomes.map fun entry =>
      (entry.1, entry.2.verdict,
        entry.2.message?.map (·.errorAddress)))

private def repeatableTemporalPartStructuralFailure? :
    Option CheckedAddressingError := do
  let rule ←
    repeatableTemporalPartRule? "InnerDateTime" (.time .minute)
      (.ordinary .equal) 21 innerDateTime.id
  let prepared ←
    (prepareFlatStringContext defaultWorld builtinStringPatternCompiler
      ordinaryIterationModel).toOption
  let data := repeatableTemporalPartData innerDateTime.id
    "2024-06-25T05:21:07"
    (some (.parsed (.temporal (.dateTime { epochMillis := 0 }
      temporalDateParts temporalClock .storedGregorian))))
  let document ← (checkDocument prepared "en_US" data).toOption
  let context : AddressedValidationEvaluationContext ordinaryIterationModel := {
    scalar := {
      fields := document.flatContext
      groups := GroupPresenceContext.unavailable
    }
    outer := []
    input := .checked document
  }
  match rule.condition.core.evalAddressed context with
  | .ok _ => none
  | .error error => some error

private def repeatableTemporalConsumerSnapshot? :
    Option (List String × List RepeatableLevel × FlatTemporalField ×
      TemporalNumericPart × CellAddr × Option String × Verdict) := do
  let declaration ←
    (ordinaryIterationModel.lookupUniqueId innerDateTime.id).toOption
  let temporal ← declaration.toTemporalField?
  let data := repeatableTemporalPartData innerDateTime.id
    "2024-06-25T05:21:07"
    (some (.parsed (.temporal (.dateTime { epochMillis := 0 }
      temporalDateParts temporalClock .storedGregorian))))
  let prepared ←
    (prepareFlatStringContext defaultWorld builtinStringPatternCompiler
      ordinaryIterationModel).toOption
  let document ← (checkDocument prepared "en_US" data).toOption
  let addressed ←
    (document.addressedCell [(10, 1), (20, 1)] innerDateTime.id).toOption
  let rule ←
    repeatableTemporalPartRule? "InnerDateTime" (.date .quarter)
      (.ordinary .equal) 2 innerDateTime.id
  let outcomes ← evalOrdinaryRule? rule data
  let outcome ← outcomes.head?
  pure (declaration.path, declaration.repeatableScope, temporal,
    .date .quarter, addressed.address, addressed.stored, outcome.2.verdict)

private def expectedRepeatableTemporalSnapshot
    (verdict : Verdict) (address : Option CellAddr) :
    Option (Option (List RepeatableLevel) × Bool ×
      List (Env × Verdict × Option CellAddr)) :=
  some (some [10, 20], true, [
    ([(10, 1), (20, 1)], verdict, address)])

/- Addressed temporal extraction reuses the checked decoded Date, Time, and DateTime payload owners. Empty input preserves symmetric omission polarity, formal invalidity remains UNKNOWN, and missing bindings remain structural. -/
example :
    (repeatableTemporalPartSnapshot? "InnerDate" innerDate.id
      (.date .day) (.ordinary .equal) 25 "2024-06-25"
      (some (.parsed (.temporal (.date { epochMillis := 0 }
        temporalDateParts .storedGregorian)))) ==
      expectedRepeatableTemporalSnapshot (.fired .value)
        (some { field := innerDate.id, path := [1, 1] })) = true ∧
    (repeatableTemporalPartSnapshot? "InnerTime" innerTime.id
      (.time .second) (.ordinary .equal) 7 "05:21:07"
      (some (.parsed (.temporal (.time { epochMillis := 0 }
        temporalClock)))) ==
      expectedRepeatableTemporalSnapshot (.fired .value)
        (some { field := innerTime.id, path := [1, 1] })) = true ∧
    (repeatableTemporalPartSnapshot? "InnerDateTime" innerDateTime.id
      (.date .quarter) (.ordinary .equal) 2 "2024-06-25T05:21:07"
      (some (.parsed (.temporal (.dateTime { epochMillis := 0 }
        temporalDateParts temporalClock .storedGregorian)))) ==
      expectedRepeatableTemporalSnapshot (.fired .value)
        (some { field := innerDateTime.id, path := [1, 1] })) = true ∧
    (repeatableTemporalPartSnapshot? "InnerTime" innerTime.id
      (.time .hour) (.ordinary .less) 100 "" none ==
      expectedRepeatableTemporalSnapshot (.fired .omission)
        (some { field := innerTime.id, path := [1, 1] })) = true ∧
    (repeatableTemporalPartSnapshot? "InnerDate" innerDate.id
      (.date .day) (.ordinary .equal) 25 "bad"
      (some (.rejected .malformed)) ==
      expectedRepeatableTemporalSnapshot .unknown none) = true ∧
    repeatableTemporalPartStructuralFailure? =
      some (.environment (.missingBinding 10)) := by
  native_decide

/- Execute uses the same checked DateTime cell whose declaration, exact selected component, complete address, and stored payload remain available to Transform and Explain consumers. -/
example :
    (repeatableTemporalConsumerSnapshot? ==
      some (
        ["Order", "Sections", "Items", "InnerDateTime"],
        [10, 20],
        { id := innerDateTime.id, kind := .dateTime,
          components := dateTimeComponents },
        .date .quarter,
        { field := innerDateTime.id, path := [1, 1] },
        some "2024-06-25T05:21:07",
        .fired .value)) = true := by
  native_decide

private def checkedDateRaw (year : Int) (month day : Nat) : RawCell :=
  .parsed (.temporal (.date { epochMillis := 0 }
    { year, month, day } .storedGregorian))

private def repeatableDateDifferenceData
    (leftStored : String) (leftRaw : Option RawCell)
    (rightStored : String) (rightRaw : Option RawCell) : DocumentData :=
  { instantiatedRows := [
      { group := 10, path := [1] },
      { group := 20, path := [1, 1] }]
    cells :=
      leftRaw.toList.map (fun cell => {
        address := { field := innerDate.id, path := [1, 1] }
        stored := leftStored
        raw := cell }) ++
      rightRaw.toList.map (fun cell => {
        address := { field := innerEarlierDate.id, path := [1, 1] }
        stored := rightStored
        raw := cell }) }

private def repeatableDateDifferenceSnapshot?
    (unit : DateDifferenceUnit) (left right : String)
    (op : NumericValidationOp) (expected : Rat)
    (data : DocumentData) :
    Option (Option (List RepeatableLevel) × Bool × List (Env × Verdict)) := do
  let rule ← repeatableDateDifferenceRule? unit left right op expected
  let outcomes ← evalOrdinaryRule? rule data
  pure (rule.iterationScope, rule.requiresAddressedValidation,
    outcomes.map fun entry => (entry.1, entry.2.verdict))

private def repeatableDateDifferenceStructuralFailure? :
    Option CheckedAddressingError := do
  let rule ← repeatableDateDifferenceRule? .months
    "InnerDate" "InnerEarlierDate" (.ordinary .equal) (-17)
  let prepared ←
    (prepareFlatStringContext defaultWorld builtinStringPatternCompiler
      ordinaryIterationModel).toOption
  let document ←
    (checkDocument prepared "en_US"
      (repeatableDateDifferenceData "2024-06-25"
        (some (checkedDateRaw 2024 6 25)) "2023-01-25"
        (some (checkedDateRaw 2023 1 25)))).toOption
  let context : AddressedValidationEvaluationContext ordinaryIterationModel := {
    scalar := {
      fields := document.flatContext
      groups := GroupPresenceContext.unavailable
    }
    outer := []
    input := .checked document
  }
  match rule.condition.core.evalAddressed context with
  | .ok _ => none
  | .error error => some error

private def repeatableDateDifferenceConsumerSnapshot? :
    Option (List String × List String × List RepeatableLevel ×
      DateDifferenceUnit × CellAddr × Option String × CellAddr × Option String ×
      Verdict) := do
  let leftDeclaration ←
    (ordinaryIterationModel.lookupUniqueId innerDate.id).toOption
  let rightDeclaration ←
    (ordinaryIterationModel.lookupUniqueId innerEarlierDate.id).toOption
  let data := repeatableDateDifferenceData "2024-06-25"
    (some (checkedDateRaw 2024 6 25)) "2023-01-25"
    (some (checkedDateRaw 2023 1 25))
  let prepared ←
    (prepareFlatStringContext defaultWorld builtinStringPatternCompiler
      ordinaryIterationModel).toOption
  let document ← (checkDocument prepared "en_US" data).toOption
  let left ←
    (document.addressedCell [(10, 1), (20, 1)] innerDate.id).toOption
  let right ←
    (document.addressedCell [(10, 1), (20, 1)]
      innerEarlierDate.id).toOption
  let rule ← repeatableDateDifferenceRule? .months
    "InnerDate" "InnerEarlierDate" (.ordinary .equal) (-17)
  let outcomes ← evalOrdinaryRule? rule data
  let outcome ← outcomes.head?
  pure (leftDeclaration.path, rightDeclaration.path,
    leftDeclaration.repeatableScope, .months,
    left.address, left.stored, right.address, right.stored, outcome.2.verdict)

private def expectedRepeatableDateDifference
    (verdict : Verdict) :
    Option (Option (List RepeatableLevel) × Bool × List (Env × Verdict)) :=
  some (some [10, 20], true, [([(10, 1), (20, 1)], verdict)])

/- One addressed ordinary atom now reads two Date operands in authored order. Missing input keeps the symmetric-zero omission account, formal invalidity remains UNKNOWN, and an incomplete structural environment cannot become UNKNOWN. -/
example :
    (repeatableDateDifferenceSnapshot? .months
      "InnerDate" "InnerEarlierDate" (.ordinary .equal) (-17)
      (repeatableDateDifferenceData "2024-06-25"
        (some (checkedDateRaw 2024 6 25)) "2023-01-25"
        (some (checkedDateRaw 2023 1 25))) ==
      expectedRepeatableDateDifference (.fired .value)) = true ∧
    (repeatableDateDifferenceSnapshot? .months
      "InnerEarlierDate" "InnerDate" (.ordinary .equal) 17
      (repeatableDateDifferenceData "2024-06-25"
        (some (checkedDateRaw 2024 6 25)) "2023-01-25"
        (some (checkedDateRaw 2023 1 25))) ==
      expectedRepeatableDateDifference (.fired .value)) = true ∧
    (repeatableDateDifferenceSnapshot? .months
      "InnerDate" "InnerEarlierDate" (.ordinary .less) 1
      (repeatableDateDifferenceData "" none "2023-01-25"
        (some (checkedDateRaw 2023 1 25))) ==
      expectedRepeatableDateDifference (.fired .omission)) = true ∧
    (repeatableDateDifferenceSnapshot? .years
      "InnerDate" "InnerEarlierDate" (.ordinary .equal) 1
      (repeatableDateDifferenceData "2024-06-25"
        (some (checkedDateRaw 2024 6 25)) "bad"
        (some (.rejected .malformed))) ==
      expectedRepeatableDateDifference .unknown) = true ∧
    repeatableDateDifferenceStructuralFailure? =
      some (.environment (.missingBinding 10)) := by
  native_decide

/- Execute, Transform, and Explain can recover both ordered model certificates, both checked addresses and stored payloads, the selected period unit, and the same verdict. -/
example :
    (repeatableDateDifferenceConsumerSnapshot? ==
      some (
        ["Order", "Sections", "Items", "InnerDate"],
        ["Order", "Sections", "Items", "InnerEarlierDate"],
        [10, 20],
        .months,
        { field := innerDate.id, path := [1, 1] },
        some "2024-06-25",
        { field := innerEarlierDate.id, path := [1, 1] },
        some "2023-01-25",
        .fired .value)) = true := by
  native_decide

private def outerInnerTokenValueCountData : DocumentData :=
  { instantiatedRows := [
      { group := 10, path := [1] },
      { group := 20, path := [1, 1] },
      { group := 20, path := [1, 2] }]
    cells := [
      { address := { field := outerAmount.id, path := [1] }
        stored := "1"
        raw := .parsed (.num 1) },
      { address := { field := innerToken.id, path := [1, 1] }
        stored := "A"
        raw := .parsed (.str "A") },
      { address := { field := innerToken.id, path := [1, 2] }
        stored := "A"
        raw := .parsed (.str "A") }] }

private def outerInnerTokenValueCountSnapshot? :
    Option (Option (List RepeatableLevel) × Bool ×
      List (Env × Verdict × Option CellAddr)) := do
  let rule ← outerWithInnerTokenValueCountRule?
  let outcomes ← evalOrdinaryRule? rule outerInnerTokenValueCountData
  pure (
    rule.iterationScope,
    rule.requiresAddressedValidation,
    outcomes.map fun entry =>
      (entry.1, entry.2.verdict,
        entry.2.message?.map (·.errorAddress)))

private def tokenValueCountStructuralFailure? :
    Option CheckedAddressingError := do
  let prepared ←
    (prepareFlatStringContext defaultWorld builtinStringPatternCompiler
      ordinaryIterationModel).toOption
  let document ←
    (checkDocument prepared "en_US" outerInnerTokenValueCountData).toOption
  let source ← plainStarTokenValueCountSource?
  match source.evaluateCheckedDocumentValidation document [] with
  | .ok _ => none
  | .error error => some error

/- The ordinary checked-document route retains the typed token source and its projection-aware count fold, then emits through the same outer-row rule environment. -/
example :
    (outerInnerTokenValueCountSnapshot? ==
      some (
        some [10],
        true,
        [(
          [(10, 1)],
          .fired .value,
          some { field := outerAmount.id, path := [1] })])) = true ∧
      tokenValueCountStructuralFailure? =
        some (.addressing (.missingBinding 10)) := by
  native_decide

private def plainStarProductData (withRightValues : Bool) : DocumentData :=
  { instantiatedRows := [
      { group := 10, path := [1] },
      { group := 20, path := [1, 1] },
      { group := 20, path := [1, 2] }]
    cells := [
      { address := { field := outerAmount.id, path := [1] }
        stored := "1"
        raw := .parsed (.num 1) },
      { address := { field := innerAmount.id, path := [1, 1] }
        stored := "2"
        raw := .parsed (.num 2) },
      { address := { field := innerAmount.id, path := [1, 2] }
        stored := "3"
        raw := .parsed (.num 3) }] ++
      if withRightValues then [
        { address := { field := innerPrice.id, path := [1, 1] }
          stored := "4"
          raw := .parsed (.num 4) },
        { address := { field := innerPrice.id, path := [1, 2] }
          stored := "5"
          raw := .parsed (.num 5) }]
      else [] }

private def plainStarProductVerdict? (withRightValues : Bool) :
    Option (Verdict × Option CellAddr) := do
  let rule ← guardedPlainStarProductRule?
  let outcomes ← evalOrdinaryRule? rule (plainStarProductData withRightValues)
  let outcome ← outcomes.head?
  pure (outcome.2.verdict, outcome.2.message?.map (·.errorAddress))

private def plainStarProductStructuralFailure? :
    Option CheckedAddressingError := do
  let prepared ←
    (prepareFlatStringContext defaultWorld builtinStringPatternCompiler
      ordinaryIterationModel).toOption
  let document ←
    (checkDocument prepared "en_US" (plainStarProductData true)).toOption
  let source ←
    (elaborateNumericProductAggregate ordinaryIterationModel
      ["Order", "Sections"] {
        left := deeperInnerAmountStar
        right := deeperInnerPriceStar
      }).toOption
  match source.evaluateCheckedDocumentAt .validation document [] with
  | .ok _ => none
  | .error error => some error

/- The ordinary checked-document route executes the admitted paired fold. Filled products fire at the outer error field, while empty right operands contribute zero and leave the same rule decided rather than UNKNOWN. -/
example :
    plainStarProductVerdict? true =
        some (.fired .value,
          some { field := outerAmount.id, path := [1] }) ∧
    plainStarProductVerdict? false =
        some (.notFired, none) ∧
    plainStarProductStructuralFailure? =
        some (.addressing (.missingBinding 10)) := by
  native_decide

private def classifiedCell (field : FieldId) (path : List Nat)
    (stored : String) (raw : RawCell) : ClassifiedCellInput :=
  { address := { field, path }, stored, raw }

private def instantiatedEmptySectionsData : DocumentData :=
  { instantiatedRows := [
      { group := 10, path := [2] },
      { group := 10, path := [1] }]
    cells := [] }

private def oneSectionDetailData (cell : Option RawCell) : DocumentData :=
  { instantiatedRows := [{ group := 10, path := [1] }]
    cells := cell.toList.map fun raw =>
      classifiedCell sectionDetail.id [1]
        (match raw with
        | .parsed (.num value) => toString value
        | .presentEmpty => ""
        | .rejected _ => "bad"
        | _ => "")
        raw }

private def groupRuleVerdicts?
    (rule : Option (CheckedResolvedValidationRule ordinaryIterationModel))
    (data : DocumentData) : Option (List (Env × Verdict)) := do
  let checkedRule ← rule
  let outcomes ← evalOrdinaryRule? checkedRule data
  pure (outcomes.map fun entry => (entry.1, entry.2.verdict))

private def checkedOrdinaryIterationDocument?
    (data : DocumentData) : Option (CheckedDocument ordinaryIterationModel) := do
  let prepared ←
    (prepareFlatStringContext defaultWorld builtinStringPatternCompiler
      ordinaryIterationModel).toOption
  (checkDocument prepared "en_US" data).toOption

private def addressedGroupConsumerSnapshot?
    (data : DocumentData) (groupPath : GroupPath) (environment : Env)
    (target : FlatFieldDecl) (relevance : GroupRelevance) :
    Option (GroupPath × CellAddr × GroupPresenceState) := do
  let document ← checkedOrdinaryIterationDocument? data
  let input ←
    (document.groupPresenceInput groupPath environment relevance false).toOption
  let errorTarget ← (document.addressedCell environment target.id).toOption
  pure (groupPath, errorTarget.address, input.derive)

private def detailGroupStructuralFailure? :
    Option CheckedAddressingError := do
  let rule ← detailGroupPathRule?
  let document ←
    checkedOrdinaryIterationDocument? (oneSectionDetailData none)
  let context : AddressedValidationEvaluationContext ordinaryIterationModel := {
    scalar := {
      fields := document.flatContext
      groups := GroupPresenceContext.unavailable
    }
    outer := []
    input := .checked document
  }
  match rule.condition.core.evalAddressed context with
  | .ok _ => none
  | .error error => some error

private def outerInnerAggregateData : DocumentData :=
  { instantiatedRows := [
      { group := 10, path := [2] },
      { group := 10, path := [1] },
      { group := 20, path := [2, 1] },
      { group := 20, path := [2, 2] },
      { group := 20, path := [1, 1] }]
    cells := [
      classifiedCell outerAmount.id [2] "1" (.parsed (.num 1)),
      classifiedCell outerAmount.id [1] "1" (.parsed (.num 1)),
      classifiedCell innerAmount.id [2, 1] "3" (.parsed (.num 3)),
      classifiedCell innerAmount.id [2, 2] "4" (.parsed (.num 4)),
      classifiedCell innerAmount.id [1, 1] "2" (.parsed (.num 2))] }

private def oneOuterAggregateData
    (outer : Option (String × RawCell)) : DocumentData :=
  { instantiatedRows := [
      { group := 10, path := [1] },
      { group := 20, path := [1, 1] },
      { group := 20, path := [1, 2] }]
    cells := outer.toList.map (fun (stored, raw) =>
      classifiedCell outerAmount.id [1] stored raw) ++ [
      classifiedCell innerAmount.id [1, 1] "3" (.parsed (.num 3)),
      classifiedCell innerAmount.id [1, 2] "4" (.parsed (.num 4))] }

private def oneOuterAggregateVerdict?
    (outer : Option (String × RawCell)) : Option Verdict :=
  outerWithInnerAggregateRule?.bind fun rule =>
    (evalOrdinaryRule? rule (oneOuterAggregateData outer)).bind fun outcomes =>
      outcomes.head?.map fun outcome => outcome.2.verdict

private def oneOuterEntityData
    (rows : List RowIndex)
    (cells : List (RowIndex × String × RawCell)) : DocumentData :=
  { instantiatedRows :=
      { group := 10, path := [1] } ::
        rows.map fun row => { group := 20, path := [1, row] }
    cells :=
      classifiedCell outerAmount.id [1] "1" (.parsed (.num 1)) ::
        cells.map fun (row, stored, raw) =>
          classifiedCell innerAmount.id [1, row] stored raw }

private def prefixBeforeMalformedEntityData : DocumentData :=
  oneOuterEntityData [1, 2] [
    (1, "4", .parsed (.num 4)),
    (2, "bad", .rejected .malformed)]

private def emptyBeforeValueEntityData : DocumentData :=
  oneOuterEntityData [1, 2] [(2, "4", .parsed (.num 4))]

private def openTailAfterValueEntityData : DocumentData :=
  oneOuterEntityData [1] [(1, "4", .parsed (.num 4))]

private def entityRuleVerdict?
    (rule :
      Option (CheckedResolvedValidationRule ordinaryIterationModel))
    (data : DocumentData) : Option Verdict := do
  let checkedRule ← rule
  let outcomes ← evalOrdinaryRule? checkedRule data
  outcomes.head?.map fun outcome => outcome.2.verdict

private def firstFilledEntityVerdict? (data : DocumentData) : Option Verdict :=
  entityRuleVerdict? outerWithInnerFirstFilledRule? data

private def valueCountEntityVerdict? (data : DocumentData) : Option Verdict :=
  entityRuleVerdict? outerWithInnerValueCountRule? data

private def checkedOuterInnerAggregate? :
    Option (CheckedDocument ordinaryIterationModel ×
      CheckedNumberEntitySource ordinaryIterationModel) := do
  let prepared ←
    (prepareFlatStringContext defaultWorld builtinStringPatternCompiler
      ordinaryIterationModel).toOption
  let document ←
    (checkDocument prepared "en_US" outerInnerAggregateData).toOption
  let source ←
    (elaborateNumberEntitySource ordinaryIterationModel
      ["Order", "Sections"] {
        first := .star deeperInnerAmountStar
        rest := []
      }).toOption
  pure (document, source)

private def outerInnerAggregateConsumerSnapshot?
    (outer : Env) :
    Option (List CellAddr × List (Option String) × Bool) := do
  let (document, source) ← checkedOuterInnerAggregate?
  let resolved ←
    (source.first.resolveCheckedValidationOperand document outer).toOption
  pure (resolved.addressedCells.map (·.address),
    resolved.addressedCells.map (·.stored),
    resolved.hasUninstantiatedTail)

private def innerAggregateStructuralFailure? :
    Option CheckedAddressingError := do
  let (document, source) ← checkedOuterInnerAggregate?
  match source.evaluateCheckedDocumentValidationAggregate .sum document [] with
  | .ok _ => none
  | .error cause => some cause

private def checkedInnerEntitySource?
    (data : DocumentData) :
    Option (CheckedDocument ordinaryIterationModel ×
      CheckedNumberEntitySource ordinaryIterationModel) := do
  let prepared ←
    (prepareFlatStringContext defaultWorld builtinStringPatternCompiler
      ordinaryIterationModel).toOption
  let document ← (checkDocument prepared "en_US" data).toOption
  let source ← deeperInnerNumberSource?
  pure (document, source)

private def innerEntityConsumerSnapshot?
    (data : DocumentData) (outer : Env) :
    Option (List CellAddr × List (Option String) × Bool ×
      PartialValidationFirstFilledNumberResult × NumericOperand) := do
  let (document, source) ← checkedInnerEntitySource? data
  let resolved ←
    (source.first.resolveCheckedValidationOperand document outer).toOption
  let firstFilled ←
    (source.evaluateCheckedDocumentValidation document outer .full).toOption
  let valueCount ←
    (source.evaluateCheckedDocumentValueCountValidation
      4 document outer).toOption
  pure (resolved.addressedCells.map (·.address),
    resolved.addressedCells.map (·.stored),
    resolved.hasUninstantiatedTail, firstFilled, valueCount)

private def innerEntityStructuralFailures? :
    Option (CheckedAddressingError × CheckedAddressingError) := do
  let (document, source) ←
    checkedInnerEntitySource? openTailAfterValueEntityData
  let firstFilledFailure ←
    match source.evaluateCheckedDocumentValidation document [] .full with
    | .ok _ => none
    | .error cause => some cause
  let valueCountFailure ←
    match source.evaluateCheckedDocumentValueCountValidation 4 document [] with
    | .ok _ => none
    | .error cause => some cause
  pure (firstFilledFailure, valueCountFailure)

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

/- Both authored group-reference forms iterate the actual group rows in immutable document order. A created empty row is structural content, while zero rows produce no evaluation. -/
example :
    (groupRuleVerdicts? outerGroupPathRule? instantiatedEmptySectionsData ==
        some [
          ([(10, 2)], .fired .value),
          ([(10, 1)], .fired .value)]) = true ∧
    (groupRuleVerdicts? outerRuleGroupRule? instantiatedEmptySectionsData ==
        some [
          ([(10, 2)], .fired .value),
          ([(10, 1)], .fired .value)]) = true ∧
    (groupRuleVerdicts? outerGroupPathRule?
        { instantiatedRows := [], cells := [] } == some []) = true := by
  native_decide

/- A nonrepeatable descendant group inside the selected row is filled only by admitted descendant content: absence and malformed-only input remain non-firing, while the malformed cell remains independently visible as group error. -/
example :
    (groupRuleVerdicts? detailGroupPathRule?
        (oneSectionDetailData (some (.parsed (.num 7)))) ==
      some [([(10, 1)], .fired .value)]) = true ∧
    (groupRuleVerdicts? detailGroupPathRule?
        (oneSectionDetailData none) ==
      some [([(10, 1)], .notFired)]) = true ∧
    (groupRuleVerdicts? detailGroupPathRule?
        (oneSectionDetailData (some (.rejected .malformed))) ==
      some [([(10, 1)], .notFired)]) = true := by
  native_decide

/- Execute/Transform/Explain consumers recover the exact group and target addresses plus the uncollapsed admitted-content × error × relevance state from the same checked document used by rule execution. -/
example :
    addressedGroupConsumerSnapshot? instantiatedEmptySectionsData
        ["Order", "Sections"] [(10, 1)] outerAmount .fullyRelevant =
      some (
        ["Order", "Sections"],
        { field := outerAmount.id, path := [1] },
        { content := true, erroneous := false,
          relevance := .fullyRelevant }) ∧
    addressedGroupConsumerSnapshot?
        (oneSectionDetailData (some (.parsed (.num 7))))
        ["Order", "Sections", "Details"] [(10, 1)]
        sectionDetail .partlyRelevant =
      some (
        ["Order", "Sections", "Details"],
        { field := sectionDetail.id, path := [1] },
        { content := true, erroneous := false,
          relevance := .partlyRelevant }) ∧
    addressedGroupConsumerSnapshot?
        (oneSectionDetailData (some (.rejected .malformed)))
        ["Order", "Sections", "Details"] [(10, 1)]
        sectionDetail .fullyRelevant =
      some (
        ["Order", "Sections", "Details"],
        { field := sectionDetail.id, path := [1] },
        { content := false, erroneous := true,
          relevance := .fullyRelevant }) := by
  native_decide

/- A missing group binding is structural insufficient information, never semantic UNKNOWN. -/
example :
    detailGroupStructuralFailure? =
      some (.group (.missingBinding 10)) := by
  native_decide

private def ordinaryNumericData (stored : String) (raw : Option RawCell) : DocumentData :=
  { instantiatedRows := [{ group := 10, path := [1] }]
    cells := match raw with
      | none => []
      | some cell => [{
          address := { field := outerAmount.id, path := [1] }
          stored
          raw := cell
        }] }

private def evalOrdinaryNumeric? (stored : String) (raw : Option RawCell) :
    Option (Verdict × Option CellAddr) :=
  ordinaryRepeatableNumericRule?.bind fun rule =>
    (evalOrdinaryRule? rule (ordinaryNumericData stored raw)).bind fun outcomes =>
      (outcomes.map (fun entry =>
        (entry.2.verdict, entry.2.message?.map (·.errorAddress)))).head?

/- Addressed ordinary Number evaluation preserves the established nested arithmetic and direct-comparison empty polarity at the selected row: present zero is a value firing, absence is an omission firing, and malformed input stays semantic UNKNOWN. -/
example :
    evalOrdinaryNumeric? "2" (some (.parsed (.num 2))) =
        some (.fired .value,
          some { field := outerAmount.id, path := [1] }) ∧
      evalOrdinaryNumeric? "0" (some (.parsed (.num 0))) =
        some (.fired .value,
          some { field := outerAmount.id, path := [1] }) ∧
      evalOrdinaryNumeric? "" none =
        some (.fired .omission,
          some { field := outerAmount.id, path := [1] }) ∧
      evalOrdinaryNumeric? "bad" (some (.rejected .malformed)) =
        some (.unknown, none) := by
  native_decide

/- A nested direct Number keeps the complete outer/inner environment and emits at the exact two-level error address. -/
example :
    (nestedRepeatableNumericRule?.bind fun rule =>
      (evalOrdinaryRule? rule {
        instantiatedRows := [
          { group := 10, path := [1] },
          { group := 10, path := [2] },
          { group := 20, path := [2, 1] }]
        cells := [{
          address := { field := innerAmount.id, path := [2, 1] }
          stored := "3"
          raw := .parsed (.num 3)
        }]
      }).map fun outcomes => outcomes.map fun entry =>
        (entry.1, entry.2.verdict,
          entry.2.message?.map (·.errorAddress))) =
      some [(
        [(10, 2), (20, 1)],
        .fired .value,
        some { field := innerAmount.id, path := [2, 1] })] := by
  native_decide

/- One checked composite may read an ancestor and current-row Number through their declaration-owned scopes. Execute preserves the full target environment, while Transform/Explain recover both certified declarations from the same tree. -/
example :
    ((ancestorCurrentNumericRule?.bind fun rule =>
      (evalOrdinaryRule? rule {
        instantiatedRows := [
          { group := 10, path := [1] },
          { group := 20, path := [1, 1] }]
        cells := [
          classifiedCell outerAmount.id [1] "2" (.parsed (.num 2)),
          classifiedCell innerAmount.id [1, 1] "3" (.parsed (.num 3))]
      }).map fun outcomes =>
        (rule.condition.core.ordinaryRepeatableFields.map (·.id),
          outcomes.map fun entry =>
            (entry.1, entry.2.verdict,
              entry.2.message?.map (·.errorAddress)))) ==
      some (
        [outerAmount.id, innerAmount.id],
        [(
          [(10, 1), (20, 1)],
          .fired .value,
          some { field := innerAmount.id, path := [1, 1] })])) = true := by
  native_decide

/- The surrounding rule environment fixes only the outer row; the deeper aggregate reopens its checked suffix and therefore selects different inner instances even when both parents contain local coordinate 1. -/
example :
    (outerWithInnerAggregateRule?.bind
      (evalOrdinaryRule? · outerInnerAggregateData)).map
        (·.map fun outcome => (outcome.1, outcome.2.verdict)) =
      some [
        ([(10, 2)], .fired .value),
        ([(10, 1)], .notFired)] := by
  native_decide

/- The current-row Number keeps its established validation polarity inside the mixed expression: present input fires as VALUE, physical absence fires as OMISSION, and malformed input remains semantic UNKNOWN. -/
example :
    oneOuterAggregateVerdict? (some ("1", .parsed (.num 1))) =
        some (.fired .value) ∧
      oneOuterAggregateVerdict? none = some (.fired .omission) ∧
      oneOuterAggregateVerdict? (some ("bad", .rejected .malformed)) =
        some .unknown := by
  native_decide

/- `FirstFilledValue` retains its prefix stop through the whole-rule bridge, while value count drains the same selected cells and reaches the malformed suffix. -/
example :
    firstFilledEntityVerdict? prefixBeforeMalformedEntityData =
        some (.fired .value) ∧
      valueCountEntityVerdict? prefixBeforeMalformedEntityData =
        some .unknown := by
  native_decide

/- An earlier empty selected cell reaches the later value for both consumers and preserves the established fillable polarity. -/
example :
    firstFilledEntityVerdict? emptyBeforeValueEntityData =
        some (.fired .omission) ∧
      valueCountEntityVerdict? emptyBeforeValueEntityData =
        some (.fired .omission) := by
  native_decide

/- A present prefix makes the uninstantiated suffix irrelevant to `FirstFilledValue`; the draining count retains the same hierarchical tail as grow-only uncertainty. -/
example :
    firstFilledEntityVerdict? openTailAfterValueEntityData =
        some (.fired .value) ∧
      valueCountEntityVerdict? openTailAfterValueEntityData =
        some (.fired .omission) := by
  native_decide

/- A terminal value in an unfiltered slot hides the later filtered duplicate from `FirstFilledValue`; value count drains it, counts the second match, and retains matched-filter shrinkability. -/
example :
    entityRuleVerdict? outerWithFilteredInnerFirstFilledRule?
        openTailAfterValueEntityData =
        some (.fired .value) ∧
      entityRuleVerdict? outerWithFilteredInnerValueCountRule?
        openTailAfterValueEntityData =
        some (.fired .omission) := by
  native_decide

/- Execute/Transform/Explain consumers can recover complete addresses, exact stored payload, and hierarchical extent from the same checked source used by rule evaluation; a terminal coordinate never identifies a cell by itself. -/
example :
    outerInnerAggregateConsumerSnapshot? [(10, 2)] =
        some ([
            { field := innerAmount.id, path := [2, 1] },
            { field := innerAmount.id, path := [2, 2] }],
          [some "3", some "4"], false) ∧
      outerInnerAggregateConsumerSnapshot? [(10, 1)] =
        some ([{ field := innerAmount.id, path := [1, 1] }],
          [some "2"], true) := by
  native_decide

/- The same checked source exposes the exact selected address, stored payload, hierarchical tail, and each consumer-specific result without a second operand stream. -/
example :
    innerEntityConsumerSnapshot? openTailAfterValueEntityData [(10, 1)] =
      some ([
          { field := innerAmount.id, path := [1, 1] }],
        [some "4"], true,
        .evaluated (.value 4 false),
        .value 1 .growOnly) := by
  native_decide

/- A reached missing captured binding remains a structural addressing failure outside semantic UNKNOWN. -/
example :
    innerAggregateStructuralFailure? =
      some (.addressing (.missingBinding 10)) := by
  native_decide

/- Both newly admitted consumers preserve the same missing binding as a rich structural failure rather than projecting it to semantic UNKNOWN. -/
example :
    innerEntityStructuralFailures? =
      some (
        .addressing (.missingBinding 10),
        .addressing (.missingBinding 10)) := by
  native_decide

end A12Kernel.Conformance.ValidationRule
