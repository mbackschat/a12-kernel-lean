import A12Kernel.Elaboration.NumericValidation.Resolution
import A12Kernel.Elaboration.NumericValidation.Expression
import A12Kernel.Elaboration.PartialGroupCount

/-! # Checked numeric-validation evaluation -/

namespace A12Kernel

/-- Lift the existing validation-phase Number read into the arithmetic outcome domain. -/
def FlatContext.resolveNumericArithmetic (context : FlatContext)
    (field : FlatNumberField) :
    Except NumericValidationUnavailable NumericArithmeticOutcome :=
  (context.resolveNumberComparisonOperand field).toValidationArithmetic

/-- Resolve the checked sub-day field/`Now` operand domain. An absent evaluation world or a forged broader temporal operand stays formally unavailable instead of acquiring a numeric default. -/
def FlatContext.resolveDateTimeDifferenceOperand
    (context : FlatContext) : FlatTemporalOperand → DateTimeDifferenceOperand
  | .fieldValue source =>
      .ofObservation (context.observeValidationAt source.id)
  | .nowValue =>
      match context.world with
      | some world => .value world.now
      | none => .unavailable .malformed
  | _ => .unavailable .malformed

def ValidationEvaluationContext.resolveNumericValidationAtom
    (context : ValidationEvaluationContext) :
    NumericValidationAtom →
      Except NumericValidationUnavailable NumericArithmeticOutcome
  | .field field => context.fields.resolveNumericArithmetic field
  | .baseYear year => .ok (.value year .fixed)
  | .fixedCurrentRepetition _ => .ok (.value 1 .fixed)
  | .boundCurrentRepetition _ => .error .groupState
  | .baseYearDatePart year source part =>
      .ok (.value (baseYearDateSourceNumericPart year source part) .fixed)
  | .temporalFieldPart field part =>
      (context.fields.resolveTemporalNumericOperand field part).toValidationArithmetic
  | .dateRangeBoundPart source bound part =>
      (context.fields.resolveDateRangeBoundNumericOperand source bound part).toValidationArithmetic
  | .stringLength field =>
      (context.fields.resolveStringLengthOperand field).toValidationArithmetic
  | .stringRange field start finish =>
      ((context.fields.observeValidationAt field.id).asStringRangeOperand start finish).toValidationArithmetic
  | .fieldValueAsNumber source =>
      (source.observeOperand (context.fields.observeValidationAt source.fieldId)).toValidationArithmetic
  | .dateDifference unit left right =>
      match DateDifferenceOperand.evaluate unit
          (left.validationOperand context.fields)
          (right.validationOperand context.fields) with
      | .ok operand => operand.toValidationArithmetic
      | .error _ => .error (.formal .malformed)
  | .dateTimeDifference unit left right =>
      (DateTimeDifferenceOperand.evaluate unit
        (context.fields.resolveDateTimeDifferenceOperand left)
        (context.fields.resolveDateTimeDifferenceOperand right))
        |>.toValidationArithmetic
  | .dayDifference profile left right =>
      match CalendarDayDifferenceOperand.evaluate profile
          (left.calendarDayValidationOperand profile context.fields)
          (right.calendarDayValidationOperand profile context.fields) with
      | .ok operand => operand.toValidationArithmetic
      | .error _ => .error (.formal .malformed)
  | .aggregate op source =>
      (source.evaluate op context.fields.observeValidationAt).toValidationArithmetic
  | .filledGroupCount groups =>
      -- The extent is the operand list, deliberately **not** the subtree slot capacity the field
      -- count uses. A listed group contributes at most one however many descendant rows it holds,
      -- and it counts as filled through a descendant row; both are measured
      -- ([checkpoint](../../../docs/SOURCES.md#src-group-count-list-extent)). Only a *starred*
      -- member can contribute per row, and this arm refuses one at elaboration.
      match context.groups.resolveAll groups with
      | none => .error .groupState
      | some states =>
          match (context.pass.countFilledGroups states).availableWithFillability?
              groups.length with
          | none => .error .groupState
          | some available => .ok (.value available.1 available.2)

/-- Preserve the established flat-only numeric entry point. A group-count atom evaluated without resolved group state becomes explicitly unavailable. -/
def FlatContext.resolveNumericValidationAtom (context : FlatContext)
    (atom : NumericValidationAtom) :
    Except NumericValidationUnavailable NumericArithmeticOutcome :=
  ({ fields := context, groups := GroupPresenceContext.unavailable } :
    ValidationEvaluationContext).resolveNumericValidationAtom atom

@[simp]
theorem ValidationEvaluationContext.resolveNumericValidationAtom_withoutGroups
    (fields : FlatContext) (atom : NumericValidationAtom) :
    ({ fields, groups := GroupPresenceContext.unavailable } :
      ValidationEvaluationContext).resolveNumericValidationAtom atom =
        fields.resolveNumericValidationAtom atom := by
  rfl

namespace OrderedNumericValidationAtom

/-- Resolve one nonempty direct Number field list in order, gating each reached source before its checked validation read. This proof-visible worker is used only by the relevance-aware numeric atom. -/
def resolveFirstFilledFields
    (context : ValidationEvaluationContext) (isRelevant : FlatRelevance) :
    List FlatNumberField → FirstFilledScanState →
      Except NumericValidationUnavailable NumericArithmeticOutcome
  | [], state => state.finish.asValidationOperand.toValidationArithmetic
  | field :: remaining, state =>
      if isRelevant field.id then
        match state.step (field.valueListCell context.fields) with
        | .continue next =>
            resolveFirstFilledFields context isRelevant remaining next
        | .done result =>
            result.asNumber.asValidationOperand.toValidationArithmetic
      else
        .error .nonRelevant

/-- Resolve one reached atom with its own relevance rule. Ordinary atoms preserve the previous all-fields gate; direct `FirstFilledValue` checks each source immediately before its declaration-owned read and hides the suffix after a terminal value or formal failure. -/
def resolve (atom : OrderedNumericValidationAtom model)
    (context : ValidationEvaluationContext) (isRelevant : FlatRelevance) :
    Except NumericValidationUnavailable NumericArithmeticOutcome :=
  match atom with
  | .ordinary source =>
      if source.allRelevant isRelevant then
        context.resolveNumericValidationAtom source
      else
        .error .nonRelevant
  | .temporalPart source =>
      if source.source.fieldIds.all isRelevant then
        (source.evalResult .validation context.fields).toOption.getD (.error .groupState)
      else .error .nonRelevant
  | .firstFilled source =>
      match source.directResolvedFields? with
      | some direct =>
          resolveFirstFilledFields context isRelevant direct.fields {}
      | none => .error .groupState
  | .valueCount expected source =>
      match source.directResolvedFields? with
      | some direct =>
          if direct.fields.all fun field => isRelevant field.id then
            match source.evaluateDirectValueCountAt? expected .validation
                context.fields with
            | some result => result.toValidationArithmetic
            | none => .error .groupState
          else
            .error .nonRelevant
      | none => .error .groupState
  | .tokenValueCount source =>
      match source.source.directFields? with
      | some direct =>
        if direct.all fun field => isRelevant field.operand.field.id then
          match source.evaluateDirectAt? .validation context.fields.read with
          | some result => result.toValidationArithmetic
          | none => .error .groupState
        else
          .error .nonRelevant
      | none => .error .groupState
  | .booleanValueCount source =>
      match source.directFields? with
      | some fields =>
          if fields.all fun field => isRelevant field.id then
            match source.evaluateDirectAt? .validation context.fields.read with
            | some result => result.toValidationArithmetic
            | none => .error .groupState
          else
            .error .nonRelevant
      | none => .error .groupState
  | .aggregate _ _ | .sumOfProducts _ => .error .groupState
  -- A starred member's contribution is an instantiated row count, which this scalar context
  -- carries no document to read. The addressed resolver owns the arm.
  | .filledGroupCountMixed _ | .filledFieldCount _ | .tokenDistinctCount _
  | .temporalDistinctCount _ => .error .groupState

/-- Keep temporal runtime effects outside numeric unavailability on the rule execution path. -/
def resolveResult (atom : OrderedNumericValidationAtom model)
    (context : ValidationEvaluationContext) (isRelevant : FlatRelevance) :
    Except ScalarTemporalEvaluationFault (Except NumericValidationUnavailable NumericArithmeticOutcome) :=
  match atom with
  | .temporalPart source =>
      if source.source.fieldIds.all isRelevant then source.evalResult .validation context.fields
      else pure (.error .nonRelevant)
  | _ => pure (atom.resolve context isRelevant)

private def temporalNumericFields (source : CheckedTemporalNumericExpression model)
    (context : AddressedValidationEvaluationContext model) : Except CheckedAddressingError FlatContext := do
  let cells ← source.source.fieldIds.mapM fun field => do
    pure (field, ← context.readCell context.outer field)
  let storedText ← match context.input with
    | .checked document | .partialView document _ => pure (document.storedTextIn context.outer)
    | .legacy _ _ => do
        if source.source.storedTextFields.any (fun field => (model.lookupUniqueId field).toOption.any
            (fun declaration => !declaration.repeatableScope.isEmpty)) then
          throw (.checkedDocumentRequired [])
        pure context.scalar.fields.storedText
  pure { context.scalar.fields with
    storedText
    read := fun field => ((cells.find? (·.1 == field)).map (·.2)).getD malformedCheckedCell }

/-- Full addressed validation makes every already-certified direct field relevant. Partial scopes use their separate evaluator and cannot inhabit this context. -/
def addressedDirectRelevant
    (_context : AddressedValidationEvaluationContext model) :
    FlatRelevance := fun _ => true

/-- Structural coordinate faults stay outside numeric unavailability. Field-backed atoms reuse
    their scalar evaluator over checked substitutions: full validation substitutes repeatable fields,
    while a partial view substitutes every referenced field to preserve call-local findings. -/
private def resolveAddressedOrdinary
    (source : NumericValidationAtom)
    (context : AddressedValidationEvaluationContext model) :
    Except CheckedAddressingError
      (Except NumericValidationUnavailable NumericArithmeticOutcome) := do
  if let .boundCurrentRepetition repetition := source then
    let coordinate ← repetition.coordinateAt context.outer |>.mapError .environment
    return .ok (.value coordinate .fixed)
  let rec readAddressed :
      List FieldId →
        Except CheckedAddressingError
          (Except NumericValidationUnavailable
            (List (FieldId × CheckedCell)))
    | [] => pure (.ok [])
    | field :: remaining =>
        match model.lookupUniqueId field with
        | .error _ => pure (.error (.formal .malformed))
        | .ok declaration =>
            let needsAddressedRead :=
              match context.input with
              | .partialView _ _ => true
              | .legacy _ _ | .checked _ =>
                  !declaration.repeatableScope.isEmpty
            if !needsAddressedRead then
              readAddressed remaining
            else do
              match ← context.readPartialCell context.outer field with
              | none => pure (.error .silentlyUnavailable)
              | some addressed =>
                  match ← readAddressed remaining with
                  | .error unavailable => pure (.error unavailable)
                  | .ok cells => pure (.ok ((field, addressed) :: cells))
  match ← readAddressed (addressedNumericValidationFieldIds source) with
  | .error unavailable => pure (.error unavailable)
  | .ok addressed =>
      let fields : FlatContext := {
        read := fun requested =>
          match addressed.find? fun entry => entry.1 == requested with
          | some entry => entry.2
          | none => context.scalar.fields.read requested
        world := context.scalar.fields.world }
      let scalar : ValidationEvaluationContext := {
        context.scalar with fields }
      pure (scalar.resolveNumericValidationAtom source)

/-- Read every operand of a mixed filled-group count in authored order. A fixed member needs its
    resolved presence state and answers `none` — semantic unavailability — when the checked-document
    boundary omitted one. A starred member reads its in-capacity instantiated row count, whose
    failure is structural and stays in the addressing domain rather than collapsing to UNKNOWN.

    A fixed terminal below a starred ancestor reads one fixed-member state per in-capacity
    environment, derived from the checked document as the group-list tally derives it. A legacy
    input and a partial view supply no such derivation, so both are refused as structural rather
    than guessed. -/
private def readValidationGroupCountOperands
    (context : AddressedValidationEvaluationContext model) (document : Document) :
    List (CheckedGroupCountOperand model) →
      Except CheckedAddressingError (Option (List ValidationGroupCountOperand))
  | [] => pure (some [])
  | operand :: rest => do
      let head : Option (List ValidationGroupCountOperand) ←
        match operand with
        | .fixed reference =>
            pure ((context.scalar.groups reference.path).map ([.fixed ·]))
        | .starred source =>
            let rows ← (source.inCapacityRowCount document context.outer).mapError
              CheckedAddressingError.addressing
            pure (some [.starredRows rows])
        | .starredPresence source =>
            match context.input with
            | .checked checked => do
                let environments ←
                  (source.inCapacityEnvironments document context.outer).mapError
                    CheckedAddressingError.addressing
                let states ← environments.mapM fun environment => do
                  let input ←
                    (checked.groupPresenceInput source.groupPath environment
                      .fullyRelevant false).mapError .group
                  pure (ValidationGroupCountOperand.fixed input.derive)
                pure (some states)
            | .legacy _ _ | .partialView _ _ =>
                .error (.checkedDocumentRequired source.groupPath)
      match head with
      | none => pure none
      | some readings =>
          match ← readValidationGroupCountOperands context document rest with
          | none => pure none
          | some tail => pure (some (readings ++ tail))

/-- Resolve one model-certified numeric source while preserving structural addressing failure outside semantic unavailability. -/
def resolveAddressed (atom : OrderedNumericValidationAtom model)
    (context : AddressedValidationEvaluationContext model) :
    Except CheckedAddressingError
      (Except NumericValidationUnavailable NumericArithmeticOutcome) := do
  match atom with
  | .temporalPart source => do
      let fields ← temporalNumericFields source context
      (source.evalResult .validation fields).mapError (fun _ => .temporalUnavailable)
  | .ordinary source =>
      if source.allRelevant (addressedDirectRelevant context) then
        match source, context.input with
        | .filledGroupCount groups, .checked document => do
            let states ← groups.mapM fun reference =>
              (document.groupPresenceInput reference.path context.outer
                .fullyRelevant false).mapError .group
            let resolvedGroups : GroupPresenceContext := fun path =>
              (groups.zip states).find? (fun entry => entry.1.path == path)
                |>.map (fun entry => entry.2.derive)
            pure ({ context.scalar with groups := resolvedGroups }
              |>.resolveNumericValidationAtom source)
        | _, _ => resolveAddressedOrdinary source context
      else
        pure (.error .nonRelevant)
  | .firstFilled source =>
      let result ← match context.input with
        | .legacy document read =>
            (source.evaluateValidationIn document context.outer
              .full context.scalar.fields read).mapError .addressing
        | .checked document =>
            source.evaluateCheckedDocumentValidation (world := context.scalar.fields.world)
              document context.outer .full true
        | .partialView document _ =>
            source.evaluateCheckedDocumentValidation (world := context.scalar.fields.world)
              document context.outer .full
      match result with
      | .nonRelevant => pure (.error .nonRelevant)
      | .evaluated result =>
          pure result.asValidationOperand.toValidationArithmetic
  | .valueCount expected source =>
      let result ← match context.input with
        | .legacy document read =>
            (source.evaluateValueCountValidationIn expected document
              context.outer context.scalar.fields read).mapError .addressing
        | .checked document | .partialView document _ =>
            source.evaluateCheckedDocumentValueCountValidation (world := context.scalar.fields.world)
              expected document context.outer
      pure result.toValidationArithmetic
  | .tokenValueCount source =>
      match context.input with
      | .legacy document read => do
          let result ←
            (source.evaluateValidation (world := context.scalar.fields.world) document context.outer
              context.scalar.fields.read read).mapError .addressing
          pure result.toValidationArithmetic
      | .checked document | .partialView document _ =>
          (source.evaluateCheckedDocumentValidation (world := context.scalar.fields.world)
            document context.outer).map NumericOperand.toValidationArithmetic
  | .booleanValueCount source =>
      match context.input with
      | .legacy document read => do
          let result ←
            (source.evaluateValidation (world := context.scalar.fields.world) document context.outer
              context.scalar.fields.read read).mapError .addressing
          pure result.toValidationArithmetic
      | .checked document | .partialView document _ =>
          (source.evaluateCheckedDocumentValidation (world := context.scalar.fields.world)
            document context.outer).map NumericOperand.toValidationArithmetic
  | .aggregate op source =>
      let result ← match context.input with
        | .legacy document read =>
            (source.evaluateValidationAggregateIn op document context.outer
              context.scalar.fields read).mapError .addressing
        | .checked document | .partialView document _ =>
            source.evaluateCheckedDocumentValidationAggregate
              op document context.outer context.scalar.fields.world
      pure result.toValidationArithmetic
  | .sumOfProducts source =>
      match context.input with
      | .legacy document read => do
          let result ←
            (source.evaluateAt .validation document context.outer read)
              |>.mapError .addressing
          pure result.toValidationArithmetic
      | .checked document | .partialView document _ =>
          (source.evaluateCheckedDocumentAt
            .validation document context.outer).map
              NumericOperand.toValidationArithmetic
  | .filledGroupCountMixed operands =>
      -- The extent is the sum of each member's own capacity, one per fixed group, the declared row
      -- maximum per star, and the product of the reopened levels' maxima per fixed group below a
      -- star, so a below-capacity count still types OMISSION
      -- ([checkpoint](../../../docs/SOURCES.md#src-group-count-list-extent)). An unretained maximum
      -- leaves no finite extent to reach and yields unavailability rather than an invented rule.
      match (operands.mapM CheckedGroupCountOperand.declaredExtent?).map List.sum with
      | none => pure (.error .groupState)
      | some extent =>
          let document := match context.input with
            | .legacy document _ => document
            | .checked document | .partialView document _ =>
                DocumentData.toDocument document.source
          match ← readValidationGroupCountOperands context document operands with
          | none => pure (.error .groupState)
          | some readings =>
              match (numberOfFilledGroupsForValidationOperands
                  readings).availableWithFillability? extent with
              | none => pure (.error .groupState)
              | some available =>
                  pure (.ok (.value available.1 available.2))
  -- A formally invalid operand leaves the count unavailable, and the group source reads the checked
  -- document's in-capacity extent, which neither the legacy nor the partial input carries.
  | .filledFieldCount source =>
      match context.input with
      | .checked document => do
          match ← source.evaluateCountOperand? (world := context.scalar.fields.world) document context.outer with
          | some operand => pure operand.toValidationArithmetic
          | none => pure (.error .groupState)
      | .legacy _ _ | .partialView _ _ => pure (.error .groupState)
  | .tokenDistinctCount source =>
      match context.input with
      | .legacy document read => do
          let result ←
            (source.evaluateDistinctValidation (world := context.scalar.fields.world) document context.outer
              context.scalar.fields.read read).mapError .addressing
          pure result.toValidationArithmetic
      | .checked document | .partialView document _ =>
          (source.evaluateCheckedDocumentDistinctValidation (world := context.scalar.fields.world)
            document context.outer).map NumericOperand.toValidationArithmetic
  -- The temporal fold reads the checked document's decoded cells, which the legacy input lacks.
  | .temporalDistinctCount run =>
      match context.input with
      | .checked document =>
          (run.evaluate (world := context.scalar.fields.world) document context.outer).map NumericOperand.toValidationArithmetic
      | .legacy _ _ | .partialView _ _ => pure (.error .groupState)

/-- Addressed temporal extraction keeps cell addressing and temporal execution as separate effects. -/
def resolveAddressedResult (atom : OrderedNumericValidationAtom model)
    (context : AddressedValidationEvaluationContext model) :
    Except (Sum CheckedAddressingError ScalarTemporalEvaluationFault)
      (Except NumericValidationUnavailable NumericArithmeticOutcome) := do
  match atom with
  | .temporalPart source =>
      let fields ← (temporalNumericFields source context).mapError Sum.inl
      (source.evalResult .validation fields).mapError Sum.inr
  | _ => (atom.resolveAddressed context).mapError Sum.inl

end OrderedNumericValidationAtom

/-- The direct-field relevance view induced by one addressed validation scope. -/
def AddressedValidationEvaluationContext.directRelevant
    (context : AddressedValidationEvaluationContext model) : FlatRelevance :=
  OrderedNumericValidationAtom.addressedDirectRelevant context

/-- Compatibility wrapper for the established ordinary numeric comparison. -/
def NumericComparison.evalWith
    (comparison : NumericComparison)
    (resolve :
      NumericValidationAtom →
        Except NumericValidationUnavailable NumericArithmeticOutcome) : Verdict :=
  NumericComparisonOf.evalWith comparison resolve

/-- Dot-notation compatibility for ordinary comparisons after extracting the atom-parameterized carrier. -/
def NumericComparisonOf.evalSelectedWithGroups
    (comparison : NumericComparisonOf NumericValidationAtom)
    (context : ValidationEvaluationContext) : Verdict :=
  comparison.evalWith context.resolveNumericValidationAtom

/-- Dot-notation compatibility for the established field-only entry point. -/
def NumericComparisonOf.evalSelected
    (comparison : NumericComparisonOf NumericValidationAtom)
    (context : FlatContext) : Verdict :=
  comparison.evalWith context.resolveNumericValidationAtom

/-- Evaluate against resolved field and group state. -/
def NumericComparison.evalSelectedWithGroups
    (comparison : NumericComparison)
    (context : ValidationEvaluationContext) : Verdict :=
  comparison.evalWith context.resolveNumericValidationAtom

/-- Preserve the established field-only entry point. Group-count sources require the explicit resolved-group variant and therefore evaluate as unavailable here. -/
def NumericComparison.evalSelected
    (comparison : NumericComparison) (context : FlatContext) : Verdict :=
  comparison.evalWith context.resolveNumericValidationAtom

/-- Evaluate one already row-selected checked comparison. -/
def CheckedNumericComparison.evalSelected
    (checked : CheckedNumericComparison model)
    (context : FlatContext) : Verdict :=
  checked.core.evalSelected context

/-- An admitted comparison never fires on an entirely blank full-validation row. -/
def CheckedNumericComparison.evalFull
    (checked : CheckedNumericComparison model)
    (context : FlatContext) (hasContent : Bool) : Verdict :=
  if hasContent then checked.evalSelected context else .notFired

/-- Evaluate a reached relevance-aware numeric comparison through the one generic arithmetic evaluator. -/
def OrderedNumericComparison.evalSelected
    (comparison : OrderedNumericComparison model)
    (context : ValidationEvaluationContext)
    (isRelevant : FlatRelevance) : Verdict :=
  comparison.evalWith fun atom => atom.resolve context isRelevant

/-- Resolve every atom in one reached numeric leaf against the addressed checked inputs, then delegate the complete arithmetic and comparison result to the sole generic evaluator. Structural addressing failure remains an outer error and cannot be confused with validation UNKNOWN. -/
def OrderedNumericComparison.evalAddressed
    (comparison : OrderedNumericComparison model)
    (context : AddressedValidationEvaluationContext model) :
    Except CheckedAddressingError Verdict := do
  let left ← comparison.left.mapM (·.resolveAddressed context)
  let right ← comparison.right.mapM (·.resolveAddressed context)
  let resolved : NumericComparisonOf
      (Except NumericValidationUnavailable NumericArithmeticOutcome) := {
    op := comparison.op
    left
    right
    suppressExactScaleWarning := comparison.suppressExactScaleWarning }
  pure (resolved.evalWith id)

/-- Numeric arithmetic consumes reached results only after temporal runtime effects have been
separated; the enclosing rule retains its existing abort and classification policy. -/
def OrderedNumericComparison.evalSelectedResult (comparison : OrderedNumericComparison model)
    (context : ValidationEvaluationContext) (isRelevant : FlatRelevance) :
    Except ScalarTemporalEvaluationFault Verdict := do
  let left ← comparison.left.mapM (·.resolveResult context isRelevant)
  let right ← comparison.right.mapM (·.resolveResult context isRelevant)
  let resolved : NumericComparisonOf (Except NumericValidationUnavailable NumericArithmeticOutcome) :=
    { comparison with left, right }
  pure (resolved.evalWith id)

def OrderedNumericComparison.evalAddressedResult (comparison : OrderedNumericComparison model)
    (context : AddressedValidationEvaluationContext model) :
    Except (Sum CheckedAddressingError ScalarTemporalEvaluationFault) Verdict := do
  let left ← comparison.left.mapM (·.resolveAddressedResult context)
  let right ← comparison.right.mapM (·.resolveAddressedResult context)
  let resolved : NumericComparisonOf (Except NumericValidationUnavailable NumericArithmeticOutcome) :=
    { comparison with left, right }
  pure (resolved.evalWith id)

/-- Resolve one atom after the public support check. Unsupported branches make recursion total but are unreachable through `evalAddressedPartial?`; they cannot become public semantic UNKNOWN. -/
private def OrderedNumericValidationAtom.resolveAddressedPartialUnchecked
    (atom : OrderedNumericValidationAtom model)
    (context : AddressedValidationEvaluationContext model)
    (scope : ValidationRelevanceScope)
    (isRelevant : FlatRelevance)
    (resolveGroup : PartialGroupResolver) :
    Except CheckedAddressingError
      (Except NumericValidationUnavailable NumericArithmeticOutcome) := do
  match atom with
  | .ordinary source =>
      if source.allRelevant isRelevant then
        resolveAddressedOrdinary source context
      else
        pure (.error .nonRelevant)
  | .aggregate op source =>
      match context.input with
      | .legacy _ _ =>
          throw (.checkedDocumentRequired [])
      | .checked document =>
          match ← source.evaluateCheckedDocumentPartialAggregate
              op document context.outer scope with
          | .skippedHaving => pure (.error .groupState)
          | .nonRelevant => pure (.error .nonRelevant)
          | .evaluated operand =>
              pure operand.toValidationArithmetic
      | .partialView document read =>
          match ← source.evaluatePartialViewAggregate
              op document context.outer scope read with
          | .silentlyUnavailable => pure (.error .silentlyUnavailable)
          | .result .skippedHaving => pure (.error .groupState)
          | .result .nonRelevant => pure (.error .nonRelevant)
          | .result (.evaluated operand) =>
              pure operand.toValidationArithmetic
  | .filledGroupCountMixed operands =>
      -- A decided count keeps the full arm's declared extent and fillability, as the partial
      -- aggregates keep theirs; only whether the count is decided is partial-specific.
      match (operands.mapM CheckedGroupCountOperand.declaredExtent?).map List.sum with
      | none => pure (.error .groupState)
      | some extent =>
          let document := match context.input with
            | .legacy document _ => document
            | .checked document | .partialView document _ =>
                DocumentData.toDocument document.source
          match ← CheckedGroupCountOperand.evaluatePartialWith operands scope resolveGroup
              document context.outer with
          | .nonRelevant => pure (.error .nonRelevant)
          | .evaluated count =>
              match count.availableWithFillability? extent with
              | none => pure (.error .groupState)
              | some available => pure (.ok (.value available.1 available.2))
  | .filledFieldCount source =>
      match context.input with
      | .legacy _ _ => throw (.checkedDocumentRequired [])
      | .checked document | .partialView document _ =>
          match ← source.evaluatePartialCount document context.outer scope context.readPartialCell with
          | some .nonRelevant => pure (.error .nonRelevant)
          | some .silentlyUnavailable => pure (.error .silentlyUnavailable)
          | some (.evaluated count) =>
              match source.countCapacity?.bind count.availableWithFillability? with
              | none => pure (.error .groupState)
              | some available => pure (.ok (.value available.1 available.2))
          | none | some .skippedHaving => pure (.error .groupState)
  | .firstFilled source =>
      match context.input with
      | .legacy _ _ => throw (.checkedDocumentRequired [])
      | .checked document | .partialView document _ =>
          match source.evaluateCheckedDocumentValidation document context.outer scope
              (read? := some context.readCell) with
          | .error (.partialUnavailable _ _) => pure (.error .silentlyUnavailable)
          | .error error => throw error
          | .ok .nonRelevant => pure (.error .nonRelevant)
          | .ok (.evaluated result) => pure result.asValidationOperand.toValidationArithmetic
  | .valueCount _ _ | .tokenValueCount _
  | .booleanValueCount _ | .sumOfProducts _
  | .temporalPart _ | .tokenDistinctCount _ | .temporalDistinctCount _ =>
      pure (.error .groupState)

/-- Evaluate a partial addressed numeric comparison. `none` means the atom family or filter shape is structurally unsupported; a reached relevance failure is numeric UNKNOWN. The caller must apply the rule-wide `Having` skip first. -/
def OrderedNumericComparison.evalAddressedPartial?
    (comparison : OrderedNumericComparison model)
    (context : AddressedValidationEvaluationContext model)
    (scope : ValidationRelevanceScope)
    (isRelevant : FlatRelevance)
    (resolveGroup : PartialGroupResolver) :
    Option (Except CheckedAddressingError Verdict) :=
  if comparison.supportsAddressedPartial then
    some do
      let left ← comparison.left.mapM fun atom =>
        atom.resolveAddressedPartialUnchecked context scope isRelevant resolveGroup
      let right ← comparison.right.mapM fun atom =>
        atom.resolveAddressedPartialUnchecked context scope isRelevant resolveGroup
      let resolved : NumericComparisonOf
          (Except NumericValidationUnavailable NumericArithmeticOutcome) := {
        op := comparison.op
        left
        right
        suppressExactScaleWarning := comparison.suppressExactScaleWarning
      }
      pure (resolved.evalWith id)
  else
    none

def CheckedOrderedNumericComparison.evalSelected
    (checked : CheckedOrderedNumericComparison model)
    (context : ValidationEvaluationContext)
    (isRelevant : FlatRelevance) : Verdict :=
  checked.core.evalSelected context isRelevant

def CheckedOrderedNumericComparison.evalAddressed
    (checked : CheckedOrderedNumericComparison model)
    (context : AddressedValidationEvaluationContext model) :
    Except CheckedAddressingError Verdict :=
  checked.core.evalAddressed context

/-- Full validation supplies universal relevance and the established unavailable group projection. -/
def CheckedOrderedNumericComparison.evalFull
    (checked : CheckedOrderedNumericComparison model)
    (context : FlatContext) (hasContent : Bool) : Verdict :=
  if hasContent then
    checked.evalSelected
      { fields := context, groups := GroupPresenceContext.unavailable }
      (fun _ => true)
  else
    .notFired

/-- Check a surface comparison and evaluate it against one model-indexed prepared String context under full validation. -/
def elaborateAndEvalNumericComparison
    (prepared : PreparedFlatStringContext model compilePattern)
    (locale : String) (rowGroup : GroupPath) (raw : RawFlatContext)
    (hasContent : Bool)
    (surface : SurfaceNumericComparison) :
    Except NumericValidationElabError Verdict := do
  let checked ← elaborateNumericComparison model rowGroup surface
  pure (checked.evalFull ((prepared.checkContext locale raw).withWorld prepared.world) hasContent)

end A12Kernel
