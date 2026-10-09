import A12Kernel.Semantics.HavingFirstFilled
import A12Kernel.Semantics.HavingGroupCount
import A12Kernel.Semantics.HavingNumericProduct
import A12Kernel.Semantics.HavingCollectionCount
import A12Kernel.Semantics.HavingNumberAggregate
import A12Kernel.Semantics.ScalarTemporalDifference
import A12Kernel.Semantics.ConstructedDateInputs

namespace A12Kernel

/-- Clock and model constants carry no row origin, so arithmetic cannot make them satisfy a filter reference requirement (spec/07 §3). Field and repetition atoms retain their own origins. -/
inductive HavingNumericAtomOf (Temporal : Type) where
  | temporalDifference (unit : TemporalOperationUnit) (left right : Temporal)
  | firstFilled (slots : List (HavingFieldListSlot HavingNumberRef))
  | groupCount (operands : List HavingGroupCountOperand)
  | product (source : HavingNumericProduct)
  | collectionCount (source : HavingCollectionCount)
  | aggregate (op : NumericAggregateOp) (slots : List (HavingFieldListSlot HavingNumberRef))
  | dateDifference (unit : DateDifferenceUnit) (left right : ResolvedDateDifferenceOperand HavingTemporalRef)
  | dayDifference (profile : ModelZone.ConcreteProfile) (left right : ResolvedDateDifferenceOperand HavingTemporalRef)
  | dateTimeDifference (unit : DateTimeSubdayUnit) (left right : FlatTemporalOperand HavingTemporalRef)
  | baseYear (year : Int)
  | baseYearDatePart (year : Int) (source : BaseYearDateSource) (part : DateNumericPart)
  | clockPart (source : HavingClockSource) (profile : ModelZone.ConcreteProfile) (part : TemporalNumericPart)
  | fieldValueAsNumber (origin : HavingOrigin) (source : ResolvedFieldValueAsNumberSource)
  | field (reference : HavingNumberRef)
  | stringLength (origin : HavingOrigin) (field : FlatStringField)
  | stringRange (origin : HavingOrigin) (source : FlatStringField) (start finish : Nat)
  | dateRangeBoundPart (origin : HavingOrigin) (source : FlatDateRangeField) (bound : DateRangeBound) (part : DateNumericPart)
  | temporalExpressionPart (part : TemporalNumericPart) (source : Temporal)
  | temporalPart (origin : HavingOrigin) (source : FlatTemporalField) (part : TemporalNumericPart)
      (partialFormat : Option FullDateTargetFormat := none)
  | repetition (reference : HavingRepetitionRef)
  deriving Repr, DecidableEq

def HavingNumericAtomOf.mapTemporal (f : Temporal → Next) : HavingNumericAtomOf Temporal → HavingNumericAtomOf Next
  | .temporalDifference a0 a1 a2 => .temporalDifference a0 (f a1) (f a2)
  | .firstFilled a0 => .firstFilled a0
  | .groupCount a0 => .groupCount a0
  | .product a0 => .product a0
  | .collectionCount a0 => .collectionCount a0
  | .aggregate a0 a1 => .aggregate a0 a1
  | .dateDifference a0 a1 a2 => .dateDifference a0 a1 a2
  | .dayDifference a0 a1 a2 => .dayDifference a0 a1 a2
  | .dateTimeDifference a0 a1 a2 => .dateTimeDifference a0 a1 a2
  | .baseYear a0 => .baseYear a0
  | .baseYearDatePart a0 a1 a2 => .baseYearDatePart a0 a1 a2
  | .clockPart a0 a1 a2 => .clockPart a0 a1 a2
  | .fieldValueAsNumber a0 a1 => .fieldValueAsNumber a0 a1
  | .field a0 => .field a0
  | .stringLength a0 a1 => .stringLength a0 a1
  | .stringRange a0 a1 a2 a3 => .stringRange a0 a1 a2 a3
  | .dateRangeBoundPart a0 a1 a2 a3 => .dateRangeBoundPart a0 a1 a2 a3
  | .temporalExpressionPart a0 a1 => .temporalExpressionPart a0 (f a1)
  | .temporalPart a0 a1 a2 a3 => .temporalPart a0 a1 a2 a3
  | .repetition a0 => .repetition a0

def HavingNumericAtomOf.originsWith (origins : Temporal → List HavingOrigin) : HavingNumericAtomOf Temporal → List HavingOrigin
  | .temporalDifference _ left right => origins left ++ origins right
  | .groupCount operands => operands.map (·.origin)
  | .temporalExpressionPart _ source => origins source
  | .product source => [source.left.origin, source.right.origin]
  | .collectionCount source => (source.presenceSlots.flatMap (·.references)).map (·.origin)
  | .firstFilled slots | .aggregate _ slots => (slots.flatMap (·.references)).map (·.origin)
  | .dateDifference _ left right | .dayDifference _ left right => (left.fields ++ right.fields).map (·.origin)
  | .dateTimeDifference _ left right => (left.fieldValues ++ right.fieldValues).map (·.origin)
  | .baseYear _ | .baseYearDatePart _ _ _ | .clockPart _ _ _ => []
  | .field reference => [reference.origin]
  | .dateRangeBoundPart origin _ _ _ | .fieldValueAsNumber origin _ | .stringLength origin _
      | .stringRange origin _ _ _ | .temporalPart origin _ _ _ => [origin]
  | .repetition reference => [reference.origin]

/-- Preserve each read's own origin inside a multi-source numeric atom (spec/07 §3). -/
def HavingNumericAtomOf.fieldOriginsWith (fields : Temporal → List (HavingOrigin × FieldId)) : HavingNumericAtomOf Temporal → List (HavingOrigin × FieldId)
  | .temporalDifference _ left right => fields left ++ fields right
  | .groupCount operands => operands.flatMap fun operand => operand.source.members.map (operand.origin, ·)
  | .temporalExpressionPart _ source => fields source
  | .product source => [(source.left.origin, source.left.field.id), (source.right.origin, source.right.field.id)]
  | .collectionCount source => (source.presenceSlots.flatMap (·.references)).map (fun ref => (ref.origin, ref.field))
  | .firstFilled slots | .aggregate _ slots => (slots.flatMap (·.references)).map (fun reference => (reference.origin, reference.field.id))
  | .dateDifference _ left right | .dayDifference _ left right => (left.fields ++ right.fields).map (fun reference => (reference.origin, reference.field.id))
  | .dateTimeDifference _ left right => (left.fieldValues ++ right.fieldValues).map (fun reference => (reference.origin, reference.field.id))
  | .baseYear _ | .baseYearDatePart _ _ _ | .clockPart _ _ _ | .repetition _ => []
  | .dateRangeBoundPart origin source _ _ => [(origin, source.id)]
  | .fieldValueAsNumber origin source => [(origin, source.fieldId)]
  | .field reference => [(reference.origin, reference.field.id)]
  | .stringLength origin source | .stringRange origin source _ _ => [(origin, source.id)]
  | .temporalPart origin source _ _ => [(origin, source.id)]

def HavingNumericAtomOf.summary : HavingNumericAtomOf Temporal → NumericScaleSummary
  | .temporalDifference _ _ _ => .field 0
  | .product source => source.summary
  | .temporalExpressionPart _ _ => .field 0
  | .groupCount _ | .collectionCount _ | .aggregate .distinctCount _ => .field 0
  | .firstFilled slots | .aggregate _ slots => (slots.flatMap (·.references)).foldl (fun summary reference => summary.union (.field reference.field.info.scale)) (.field 0)
  | .dateDifference _ _ _ | .dayDifference _ _ _ | .dateTimeDifference _ _ _ => .field 0
  | .baseYear _ | .baseYearDatePart _ _ _ | .clockPart _ _ _ => .field 0
  | .fieldValueAsNumber _ source => .field source.scale
  | .field reference => .field reference.field.info.scale
  | .dateRangeBoundPart _ _ _ _ | .repetition _ | .stringLength _ _ | .stringRange _ _ _ _ | .temporalPart _ _ _ _ => .field 0

/-- Resolve one repetition reference through the structural addressed channel. -/
def CorrelationFrame.rowAtResolving (frame : CorrelationFrame)
    (context : ResolvingCorrelationContext Error)
    (reference : HavingRepetitionRef) : Except Error RowIndex :=
  match reference.source with
  | .repeatable level =>
      (frame.envAt reference.origin).bindingAt level |>.mapError context.bindingError
  | .fixed _ => .ok 1

private def readHavingSubdayDifference (phase : Phase)
    (read : Env → FieldId → Except Error CheckedCell) (frame : CorrelationFrame)
    (world : Option World) (unavailable : Error)
    (unit : DateTimeSubdayUnit) (left right : FlatTemporalOperand HavingTemporalRef) : Except Error NumericOperand := do
  let observe (reference : HavingTemporalRef) := observeCell phase <$> read (frame.envAt reference.origin) reference.field.id
  match ← readTemporalPair phase (fun source => source.readDateTimeDifferenceOperand observe world unavailable unavailable)
      (fun | .unavailable cause => some cause | _ => none) left right with
  | .error cause => pure (.unknown cause)
  | .ok (first, second) => pure (DateTimeDifferenceOperand.evaluate unit first second)

private def readHavingCalendarDifference (phase : Phase)
    (read : Env → FieldId → Except Error CheckedCell) (frame : CorrelationFrame)
    (readOperand : (HavingTemporalRef → Except Error CellObservation) →
      ResolvedDateDifferenceOperand HavingTemporalRef → Except Error Operand)
    (formalCause? : Operand → Option FormalCause)
    (evaluate : Operand → Operand → Except Unit NumericOperand)
    (left right : ResolvedDateDifferenceOperand HavingTemporalRef) : Except Error (Except Unit NumericOperand) := do
  let observe reference := observeCell phase <$> read (frame.envAt reference.origin) reference.field.id
  match ← readTemporalPair phase (readOperand observe) formalCause? left right with
  | .error cause => pure (.ok (.unknown cause))
  | .ok (first, second) => pure (evaluate first second)

private def readHavingToday (world : Option World) (unavailable : Error)
    (profile : ModelZone.ConcreteProfile) : Except Error DateParts :=
  match ResolvedDateDifferenceOperand.todayParts? profile world with
  | some parts => pure parts
  | none => throw unavailable

private def readHavingClockPart (world : Option World) (unavailable : Error)
    (source : HavingClockSource) (profile : ModelZone.ConcreteProfile) (part : TemporalNumericPart) : Except Error Rat :=
  match source.numericPart? profile world part with
  | some amount => pure amount
  | none => throw unavailable

private def readHavingDateOperand (world : Option World) (unavailable : Error)
    (read : HavingTemporalRef → Except Error CellObservation) :
    ResolvedDateDifferenceOperand HavingTemporalRef → Except Error DateDifferenceOperand :=
  ResolvedDateDifferenceOperand.readDateOperand read
    (fun profile => DateDifferenceOperand.value <$> readHavingToday world unavailable profile)

private def readHavingDayOperand (profile : ModelZone.ConcreteProfile)
    (world : Option World) (unavailable : Error) (read : HavingTemporalRef → Except Error CellObservation) :
    ResolvedDateDifferenceOperand HavingTemporalRef → Except Error CalendarDayDifferenceOperand :=
  ResolvedDateDifferenceOperand.readDayOperand profile read
    (fun sourceProfile => CalendarDayDifferenceOperand.ofParts sourceProfile <$> readHavingToday world unavailable sourceProfile)

/-- Numeric reads retain omission and formal identity until their consumer projects them.
The wider shift-amount controls separate these channels (docs/sources/temporal-runtime-fold-probes.md#src-temporal-numeric-amounts). -/
def HavingNumericAtomOf.readArithmetic [SizeOf Temporal] (phase : Phase)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame) (atom : HavingNumericAtomOf Temporal)
    (projection : TemporalNumericPart → (source : Temporal) → sizeOf source < sizeOf atom → Except Error (Except NumericValidationUnavailable NumericArithmeticOutcome))
    (difference : TemporalOperationUnit → (left right : Temporal) → sizeOf left < sizeOf atom → sizeOf right < sizeOf atom → Except Error (Except NumericValidationUnavailable NumericArithmeticOutcome))
    (unsupportedCalendar : Except Error (Except NumericValidationUnavailable NumericArithmeticOutcome) := .error context.unsupportedDateCalendar) :
    Except Error (Except NumericValidationUnavailable NumericArithmeticOutcome) :=
  match atom with
  | .temporalDifference unit left right => difference unit left right (by simp; omega) (by simp; omega)
  | .temporalExpressionPart part source => projection part source (by simp; omega)
  | .dateDifference unit left right => do
      let result ← readHavingCalendarDifference phase context.read frame
        (readHavingDateOperand context.world context.unsupportedDateCalendar)
        (fun | .unavailable cause => some cause | _ => none) (DateDifferenceOperand.evaluate unit) left right
      match result with
      | .ok operand => pure operand.toValidationArithmetic
      | .error _ => unsupportedCalendar
  | .dayDifference profile left right => do
      let result ← readHavingCalendarDifference phase context.read frame
        (readHavingDayOperand profile context.world context.unsupportedDateCalendar)
        (fun | .unavailable cause => some cause | _ => none) (CalendarDayDifferenceOperand.evaluate profile) left right
      match result with
      | .ok operand => pure operand.toValidationArithmetic
      | .error _ => unsupportedCalendar
  | .dateTimeDifference unit left right => do
      pure ((← readHavingSubdayDifference phase context.read frame context.world context.unsupportedDateCalendar unit left right).toValidationArithmetic)
  | .product source => do
      pure ((← source.evaluate phase context frame).toValidationArithmetic)
  | .groupCount operands => do
      pure ((← HavingGroupCount.evaluate phase context frame operands).map NumericOperand.toValidationArithmetic |>.getD (.error .groupState))
  | .collectionCount source => do
      pure ((← source.evaluate phase context frame).map NumericOperand.toValidationArithmetic |>.getD (.error .groupState))
  | .firstFilled slots => do
      pure ((← HavingFirstFilled.number phase context frame slots).toValidationArithmetic)
  | .aggregate op slots => do
      pure ((← HavingNumberAggregate.evaluate phase context frame op slots).toValidationArithmetic)
  | .baseYear year => pure (.ok (.value year .fixed))
  | .baseYearDatePart year source part => pure (.ok (.value (baseYearDateSourceNumericPart year source part) .fixed))
  | .clockPart source profile part => do
      pure (.ok (.value (← readHavingClockPart context.world context.unsupportedDateCalendar source profile part) .fixed))
  | .dateRangeBoundPart origin source bound part => do
      let cell ← context.read (frame.envAt origin) source.id
      pure ((observeCell phase cell).asDateRangeBoundNumericOperand bound part |>.toValidationArithmetic)
  | .fieldValueAsNumber origin source => do
      let cell ← context.read (frame.envAt origin) source.fieldId
      pure (source.observeOperand (observeCell phase cell) |>.toValidationArithmetic)
  | .stringLength origin source => do
      let cell ← context.read (frame.envAt origin) source.id
      pure ((observeCell phase cell).asStringLengthOperand.toValidationArithmetic)
  | .stringRange origin source start finish => do
      let cell ← context.read (frame.envAt origin) source.id
      pure ((observeCell phase cell).asStringRangeOperand start finish |>.toValidationArithmetic)
  | .temporalPart origin source part partialFormat => do
      let cell ← context.read (frame.envAt origin) source.id
      let observation := observeCell phase cell
      let operand := match part with
        | .date part =>
            -- Direct extraction and constructed-Date components read the same declared spelling
            -- (spec/05 §3); extraction does not complete an omitted component to an endpoint.
            match classifyConstructedDateExtractor source part observation partialFormat with
            | .ok (.value amount) => NumericOperand.value amount .fixed
            | .ok .empty => .value 0 .both
            | .ok (.unavailable cause) => .unknown cause
            | .error _ => .unknown .malformed
        | .time _ => observation.asTemporalNumericOperand source part.project?
      pure operand.toValidationArithmetic
  | .field reference => do
      let cell ← context.read (frame.envAt reference.origin) reference.field.id
      pure ((observeCell phase cell).asDirectNumericComparisonOperand reference.field.info |>.toValidationArithmetic)
  | .repetition reference => do
      pure (.ok (.value (← frame.rowAtResolving context reference) .fixed))

/-- Declared extent shape and ordered field identity survive numeric-to-temporal composition. -/
def HavingNumericAtomOf.presenceSlotsWith [SizeOf Temporal] (atom : HavingNumericAtomOf Temporal)
    (temporal : (source : Temporal) → sizeOf source < sizeOf atom → List (HavingFieldListSlot HavingPresenceRef)) :
    List (HavingFieldListSlot HavingPresenceRef) :=
  match atom with
  | .temporalDifference _ left right => temporal left (by simp; omega) ++ temporal right (by simp; omega)
  | .temporalExpressionPart _ source => temporal source (by simp; omega)
  | .groupCount operands => operands.map (·.presenceSlot)
  | .product source => source.presenceSlots
  | .collectionCount source => source.presenceSlots
  | .firstFilled slots | .aggregate _ slots => HavingNumberAggregate.presenceSlots slots
  | atom => (atom.fieldOriginsWith (fun _ => [])).map fun (origin, fieldId) => .direct { origin, field := fieldId }

namespace HavingNumericAtomOf

def formatWithSubterm [SizeOf Temporal] (atom : HavingNumericAtomOf Temporal)
    (format : (source : Temporal) → sizeOf source < sizeOf atom → Std.Format) : Std.Format :=
  match atom with
  | .temporalDifference a0 a1 a2 => "temporalDifference" ++ " " ++ (repr a0) ++ " " ++ (format a1 (by simp_all; omega)) ++ " " ++ (format a2 (by simp_all; omega))
  | .firstFilled a0 => "firstFilled" ++ " " ++ (repr a0)
  | .groupCount a0 => "groupCount" ++ " " ++ (repr a0)
  | .product a0 => "product" ++ " " ++ (repr a0)
  | .collectionCount a0 => "collectionCount" ++ " " ++ (repr a0)
  | .aggregate a0 a1 => "aggregate" ++ " " ++ (repr a0) ++ " " ++ (repr a1)
  | .dateDifference a0 a1 a2 => "dateDifference" ++ " " ++ (repr a0) ++ " " ++ (repr a1) ++ " " ++ (repr a2)
  | .dayDifference a0 a1 a2 => "dayDifference" ++ " " ++ (repr a0) ++ " " ++ (repr a1) ++ " " ++ (repr a2)
  | .dateTimeDifference a0 a1 a2 => "dateTimeDifference" ++ " " ++ (repr a0) ++ " " ++ (repr a1) ++ " " ++ (repr a2)
  | .baseYear a0 => "baseYear" ++ " " ++ (repr a0)
  | .baseYearDatePart a0 a1 a2 => "baseYearDatePart" ++ " " ++ (repr a0) ++ " " ++ (repr a1) ++ " " ++ (repr a2)
  | .clockPart a0 a1 a2 => "clockPart" ++ " " ++ (repr a0) ++ " " ++ (repr a1) ++ " " ++ (repr a2)
  | .fieldValueAsNumber a0 a1 => "fieldValueAsNumber" ++ " " ++ (repr a0) ++ " " ++ (repr a1)
  | .field a0 => "field" ++ " " ++ (repr a0)
  | .stringLength a0 a1 => "stringLength" ++ " " ++ (repr a0) ++ " " ++ (repr a1)
  | .stringRange a0 a1 a2 a3 => "stringRange" ++ " " ++ (repr a0) ++ " " ++ (repr a1) ++ " " ++ (repr a2) ++ " " ++ (repr a3)
  | .dateRangeBoundPart a0 a1 a2 a3 => "dateRangeBoundPart" ++ " " ++ (repr a0) ++ " " ++ (repr a1) ++ " " ++ (repr a2) ++ " " ++ (repr a3)
  | .temporalExpressionPart a0 a1 => "temporalExpressionPart" ++ " " ++ (repr a0) ++ " " ++ (format a1 (by simp_all; omega))
  | .temporalPart a0 a1 a2 a3 => "temporalPart" ++ " " ++ (repr a0) ++ " " ++ (repr a1) ++ " " ++ (repr a2) ++ " " ++ (repr a3)
  | .repetition a0 => "repetition" ++ " " ++ (repr a0)

def decideEqWithSubterm [SizeOf Temporal] (left right : HavingNumericAtomOf Temporal)
    (equal : (a b : Temporal) → sizeOf a < sizeOf left → sizeOf b < sizeOf right → Decidable (a = b)) :
    Decidable (left = right) := by
  cases left <;> cases right
  all_goals first | (apply isFalse; intro h; cases h; done) | skip
  case temporalDifference.temporalDifference a0 a1 a2 b0 b1 b2 =>
    letI := equal a1 b1 (by simp; omega) (by simp; omega)
    letI := equal a2 b2 (by simp; omega) (by simp; omega)
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) (by simp)
  case firstFilled.firstFilled a0 b0 =>
    exact decidable_of_iff (a0 = b0) (by simp)
  case groupCount.groupCount a0 b0 =>
    exact decidable_of_iff (a0 = b0) (by simp)
  case product.product a0 b0 =>
    exact decidable_of_iff (a0 = b0) (by simp)
  case collectionCount.collectionCount a0 b0 =>
    exact decidable_of_iff (a0 = b0) (by simp)
  case aggregate.aggregate a0 a1 b0 b1 =>
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp)
  case dateDifference.dateDifference a0 a1 a2 b0 b1 b2 =>
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) (by simp)
  case dayDifference.dayDifference a0 a1 a2 b0 b1 b2 =>
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) (by simp)
  case dateTimeDifference.dateTimeDifference a0 a1 a2 b0 b1 b2 =>
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) (by simp)
  case baseYear.baseYear a0 b0 =>
    exact decidable_of_iff (a0 = b0) (by simp)
  case baseYearDatePart.baseYearDatePart a0 a1 a2 b0 b1 b2 =>
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) (by simp)
  case clockPart.clockPart a0 a1 a2 b0 b1 b2 =>
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) (by simp)
  case fieldValueAsNumber.fieldValueAsNumber a0 a1 b0 b1 =>
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp)
  case field.field a0 b0 =>
    exact decidable_of_iff (a0 = b0) (by simp)
  case stringLength.stringLength a0 a1 b0 b1 =>
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp)
  case stringRange.stringRange a0 a1 a2 a3 b0 b1 b2 b3 =>
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3) (by simp)
  case dateRangeBoundPart.dateRangeBoundPart a0 a1 a2 a3 b0 b1 b2 b3 =>
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3) (by simp)
  case temporalExpressionPart.temporalExpressionPart a0 a1 b0 b1 =>
    letI := equal a1 b1 (by simp; omega) (by simp; omega)
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp)
  case temporalPart.temporalPart a0 a1 a2 a3 b0 b1 b2 b3 =>
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3) (by simp)
  case repetition.repetition a0 b0 =>
    exact decidable_of_iff (a0 = b0) (by simp)

def flatMapTemporalSubterm [SizeOf Temporal] (atom : HavingNumericAtomOf Temporal)
    (visit : (source : Temporal) → sizeOf source < sizeOf atom → List Result) : List Result :=
  match atom with
  | .temporalDifference _ left right => visit left (by simp; omega) ++ visit right (by simp; omega)
  | .temporalExpressionPart _ source => visit source (by simp; omega)
  | _ => []

end HavingNumericAtomOf

end A12Kernel
