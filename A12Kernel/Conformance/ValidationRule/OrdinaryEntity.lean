import A12Kernel.Elaboration.StringContext
import A12Kernel.Elaboration.CheckedStarDocument
import A12Kernel.Elaboration.ValidationRule
import A12Kernel.Conformance.ValidationRule.OrdinarySupport

/-! # Ordinary repeatable entity and group whole-rule locks -/

namespace A12Kernel.Conformance.ValidationRule.OrdinaryEntity

open A12Kernel
open A12Kernel.Conformance.ValidationRule.OrdinarySupport

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

end A12Kernel.Conformance.ValidationRule.OrdinaryEntity
