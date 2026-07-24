import A12Kernel.Elaboration.NumericValidation.Core

/-! # Checked numeric-validation evaluation -/

namespace A12Kernel

/-- Lift one already-classified validation numeric operand into the arithmetic outcome domain. Number and temporal component reads share this exact boundary. -/
def NumericOperand.toValidationArithmetic
    (operand : NumericOperand) :
    Except NumericValidationUnavailable NumericArithmeticOutcome :=
  match operand with
  | .value amount fillability => .ok (.value amount fillability)
  | .unknown cause => .error (.formal cause)

/-- Lift the existing validation-phase Number read into the arithmetic outcome domain. -/
def FlatContext.resolveNumericArithmetic (context : FlatContext)
    (field : FlatNumberField) :
    Except NumericValidationUnavailable NumericArithmeticOutcome :=
  (context.resolveNumberComparisonOperand field).toValidationArithmetic

def ValidationEvaluationContext.resolveNumericValidationAtom
    (context : ValidationEvaluationContext) :
    NumericValidationAtom →
      Except NumericValidationUnavailable NumericArithmeticOutcome
  | .field field => context.fields.resolveNumericArithmetic field
  | .baseYear year => .ok (.value year .fixed)
  | .baseYearDatePart year source part =>
      .ok (.value (baseYearDateSourceNumericPart year source part) .fixed)
  | .temporalFieldPart field part =>
      (context.fields.resolveTemporalNumericOperand field part).toValidationArithmetic
  | .stringLength field =>
      (context.fields.resolveStringLengthOperand field).toValidationArithmetic
  | .stringRange field start finish =>
      match context.fields.observeValidationAt field.id with
      | .empty => .ok (.value 0 .growOnly)
      | .value (.str value) =>
          .ok (.value (utf16RangeAsNatural value start finish) .fixed)
      | .value _ => .error (.formal .malformed)
      | .unknown cause | .poison cause => .error (.formal cause)
  | .fieldValueAsNumber source =>
      match context.fields.observeValidationAt source.fieldId with
      | .empty => .ok (.value 0 .both)
      | .value value =>
          match source.valueFor? value with
          | some amount => .ok (.value amount .fixed)
          | none => .error (.formal .malformed)
      | .unknown cause | .poison cause => .error (.formal cause)
  | .dateDifference unit left right =>
      match DateDifferenceOperand.evaluate unit
          (left.validationOperand context.fields)
          (right.validationOperand context.fields) with
      | .ok operand => operand.toValidationArithmetic
      | .error _ => .error (.formal .malformed)
  | .dateTimeDifference unit left right =>
      (DateTimeDifferenceOperand.evaluate unit
        (.ofObservation (context.fields.observeValidationAt left.id))
        (.ofObservation (context.fields.observeValidationAt right.id)))
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
      match context.groups.resolveAll groups with
      | none => .error .groupState
      | some states =>
          match numberOfFilledGroups states with
          | .unknown => .error .groupState
          | .value count =>
              .ok (.value count
                (if count < groups.length then .growOnly else .fixed))

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
  | .aggregate _ _ | .sumOfProducts _ => .error .groupState

/-- Full addressed validation makes every already-certified direct field relevant. Partial scopes use their separate evaluator and cannot inhabit this context. -/
def addressedDirectRelevant
    (_context : AddressedValidationEvaluationContext model) :
    FlatRelevance := fun _ => true

/-- Resolve every repeatable field of one ordinary atom in authored encounter order, then reuse its scalar evaluator over the checked substitutions. -/
private def resolveAddressedOrdinary
    (source : NumericValidationAtom)
    (context : AddressedValidationEvaluationContext model) :
    Except CheckedAddressingError
      (Except NumericValidationUnavailable NumericArithmeticOutcome) := do
  let rec readRepeatable :
      List FieldId →
        Except CheckedAddressingError
          (Option (List (FieldId × CheckedCell)))
    | [] => pure (some [])
    | field :: remaining =>
        match model.lookupUniqueId field with
        | .error _ => pure none
        | .ok declaration =>
            if declaration.repeatableScope.isEmpty then
              readRepeatable remaining
            else do
              let addressed ← context.readCell context.outer field
              match ← readRepeatable remaining with
              | none => pure none
              | some cells => pure (some ((field, addressed) :: cells))
  match ← readRepeatable (addressedNumericValidationFieldIds source) with
  | none => pure (.error (.formal .malformed))
  | some addressed =>
      let fields : FlatContext := {
        read := fun requested =>
          match addressed.find? fun entry => entry.1 == requested with
          | some entry => entry.2
          | none => context.scalar.fields.read requested }
      let scalar : ValidationEvaluationContext := {
        context.scalar with fields }
      pure (scalar.resolveNumericValidationAtom source)

/-- Resolve one model-certified numeric source while preserving structural addressing failure outside semantic unavailability. -/
def resolveAddressed (atom : OrderedNumericValidationAtom model)
    (context : AddressedValidationEvaluationContext model) :
    Except CheckedAddressingError
      (Except NumericValidationUnavailable NumericArithmeticOutcome) := do
  match atom with
  | .ordinary source =>
      if source.allRelevant (addressedDirectRelevant context) then
        resolveAddressedOrdinary source context
      else
        pure (.error .nonRelevant)
  | .firstFilled source =>
      let result ← match context.input with
        | .legacy document read =>
            (source.evaluateValidationIn document context.outer
              .full context.scalar.fields read).mapError .addressing
        | .checked document =>
            source.evaluateCheckedDocumentValidation
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
        | .checked document =>
            source.evaluateCheckedDocumentValueCountValidation
              expected document context.outer
      pure result.toValidationArithmetic
  | .tokenValueCount source =>
      match context.input with
      | .legacy document read => do
          let result ←
            (source.evaluateValidation document context.outer
              context.scalar.fields.read read).mapError .addressing
          pure result.toValidationArithmetic
      | .checked document =>
          (source.evaluateCheckedDocumentValidation
            document context.outer).map NumericOperand.toValidationArithmetic
  | .aggregate op source =>
      let result ← match context.input with
        | .legacy document read =>
            (source.evaluateValidationAggregateIn op document context.outer
              context.scalar.fields read).mapError .addressing
        | .checked document =>
            source.evaluateCheckedDocumentValidationAggregate
              op document context.outer
      pure result.toValidationArithmetic
  | .sumOfProducts source =>
      match context.input with
      | .legacy document read => do
          let result ←
            (source.evaluateAt .validation document context.outer read)
              |>.mapError .addressing
          pure result.toValidationArithmetic
      | .checked document =>
          (source.evaluateCheckedDocumentAt
            .validation document context.outer).map
              NumericOperand.toValidationArithmetic

end OrderedNumericValidationAtom

/-- The direct-field relevance view induced by one addressed validation scope. -/
def AddressedValidationEvaluationContext.directRelevant
    (context : AddressedValidationEvaluationContext model) : FlatRelevance :=
  OrderedNumericValidationAtom.addressedDirectRelevant context

def combineNumericValidationOutcomes
    (combine : NumericArithmeticOutcome → NumericArithmeticOutcome →
      NumericArithmeticOutcome)
    (left right : Except Error NumericArithmeticOutcome) :
    Except Error NumericArithmeticOutcome :=
  match left, right with
  | .error cause, _ => .error cause
  | _, .error cause => .error cause
  | .ok leftOutcome, .ok rightOutcome => .ok (combine leftOutcome rightOutcome)

def evalPlainBinary (op : NumericScaleBinaryOp)
    (left right : Except Error NumericArithmeticOutcome) :
    Except Error NumericArithmeticOutcome :=
  combineNumericValidationOutcomes
    (fun leftOutcome rightOutcome =>
      match op with
        | .add => NumericArithmeticOutcome.eval .add leftOutcome rightOutcome
        | .subtract => NumericArithmeticOutcome.eval .subtract leftOutcome rightOutcome
        | .multiply => NumericArithmeticOutcome.eval .multiply leftOutcome rightOutcome
        | .divide => NumericArithmeticOutcome.divide leftOutcome rightOutcome)
    left right

/-- Whether a lowered tree lies in the consumer's binary-arithmetic runtime subset. -/
def LoweredNumericExpr.isPlainArithmetic : LoweredNumericExpr Atom → Bool
  | .atom _ | .literal _ => true
  | .binary _ left right => left.isPlainArithmetic && right.isPlainArithmetic
  | .power base exponent =>
      base.isPlainArithmetic && exponent.isPlainArithmetic
  | .abs _ | .extremum _ _ _ | .extremumCall _ _ _ | .round _ _ _ => false

/-- Runtime-shape mirror of one authored extremum call, including its independent per-call constant budget. -/
def LoweredNumericExpr.extremumCallConstantUse?
    (expected : NumericExtremumOp) :
    LoweredNumericExpr Atom → Option Bool
  | .extremumCall actual constantUse _ =>
      if actual != expected then none else constantUse
  | _ => none

/-- Read the source-derived admission certificate retained across lowering. -/
def LoweredNumericExpr.isExtremumCall : LoweredNumericExpr Atom → Bool
  | .extremumCall _ constantUse _ => constantUse.isSome
  | _ => false

/-- Runtime-capable numeric-operation shape after grouping erasure. -/
def LoweredNumericExpr.isNumericOperation : LoweredNumericExpr Atom → Bool
  | .atom _ | .literal _ => true
  | .binary _ left right | .power left right =>
      left.isNumericOperation && right.isNumericOperation
  | .abs body | .round _ _ body => body.isNumericOperation
  | expression@(.extremumCall _ _ _) => expression.isExtremumCall
  | .extremum _ _ _ => false

def LoweredNumericExpr.isAdmittedValidation (expression : LoweredNumericExpr Atom) :
    Bool :=
  expression.isNumericOperation

/-- Preserve the first formal cause across exact extremum selection of two reached validation outcomes. -/
def NumericExtremumOp.selectValidationOutcome (op : NumericExtremumOp) :
    Except Error NumericArithmeticOutcome →
      Except Error NumericArithmeticOutcome →
        Except Error NumericArithmeticOutcome
  | left, right =>
      combineNumericValidationOutcomes op.selectOutcome left right

def LoweredNumericExpr.evalNumericOperationTree
    (read : Atom → Except Error NumericArithmeticOutcome) :
    LoweredNumericExpr Atom → Except Error NumericArithmeticOutcome
  | .atom sourceAtom => read sourceAtom
  | .literal amount => .ok (.value amount .fixed)
  | .binary op left right =>
      evalPlainBinary op
        (left.evalNumericOperationTree read)
        (right.evalNumericOperationTree read)
  | .power base exponent =>
      combineNumericValidationOutcomes NumericArithmeticOutcome.power
        (base.evalNumericOperationTree read)
        (exponent.evalNumericOperationTree read)
  | .abs body =>
      match body.evalNumericOperationTree read with
      | .ok outcome => .ok outcome.absolute
      | .error cause => .error cause
  | .extremum op left right =>
      op.selectValidationOutcome
        (left.evalNumericOperationTree read)
        (right.evalNumericOperationTree read)
  | .extremumCall _ _ body => body.evalNumericOperationTree read
  | .round mode places body =>
      match body.evalNumericOperationTree read with
      | .ok outcome => .ok (outcome.round mode places)
      | .error cause => .error cause

/-- Evaluate one complete numeric operation after checking its lowered admission certificate. -/
def LoweredNumericExpr.evalNumericOperation?
    (read : Atom → Except Error NumericArithmeticOutcome)
    (expression : LoweredNumericExpr Atom) :
      Option (Except Error NumericArithmeticOutcome) :=
  if expression.isNumericOperation then
    some (expression.evalNumericOperationTree read)
  else
    none

/-- Evaluate exactly the checked runtime fragment. Value functions compose recursively with arithmetic while formal invalidity and arithmetic domain failure remain distinct. -/
def LoweredNumericExpr.evalAdmittedValidation?
    (read : Atom → Except Error NumericArithmeticOutcome)
    (expression : LoweredNumericExpr Atom) :
      Option (Except Error NumericArithmeticOutcome) :=
  expression.evalNumericOperation? read

/-- Evaluate a raw core through one supplied numeric-source resolver. The unknown fallback fails closed for a forged unsupported operand and is unreachable through every checked specialization. -/
def NumericComparisonOf.evalWith
    (comparison : NumericComparisonOf Atom)
    (resolve :
      Atom →
        Except NumericValidationUnavailable NumericArithmeticOutcome) : Verdict :=
  match
      comparison.left.lowerForEvaluation.evalAdmittedValidation?
        resolve,
      comparison.right.lowerForEvaluation.evalAdmittedValidation?
        resolve with
  | some left, some right => comparison.op.evalArithmeticWith left right
  | _, _ => .unknown

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
  pure (checked.evalFull (prepared.checkContext locale raw) hasContent)

end A12Kernel
