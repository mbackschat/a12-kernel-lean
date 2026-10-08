import A12Kernel.Semantics.TimeConstruction
import A12Kernel.Semantics.TimeNumeric
import A12Kernel.Semantics.FlatValidation
import A12Kernel.Semantics.String

namespace A12Kernel

/-- The declaration gate selected by a field's authored `Time(...)` position. -/
inductive TimeComponentPosition where
  | hour
  | minute
  | second
  deriving Repr, DecidableEq

namespace TimeComponentPosition

/-- Inclusive natural-number bound for a quoted constant at this position. -/
def maximumNat : TimeComponentPosition → Nat
  | .hour => 23
  | .minute | .second => 59

/-- Inclusive maximum accepted as the position-specific alternative to stored length 2. -/
def maximum : TimeComponentPosition → Rat
  | position => position.maximumNat

/-- Decode one already-unescaped quoted constant under the pinned Java 21 decimal-digit profile and position bound. -/
def decodeConstant? (position : TimeComponentPosition)
    (source : String) : Option Int := do
  let value ← parseJava21BmpNatural? source
  if value ≤ position.maximumNat then
    some value
  else
    none

/-- The only extractor token admitted at this constructor position. -/
def extractor : TimeComponentPosition → TimeNumericPart
  | .hour => .hour
  | .minute => .minute
  | .second => .second

end TimeComponentPosition

/-- The zero-to-three-component prefix shared by surface and checked carriers. Omitted trailing components are fixed zeroes and cannot be read. -/
inductive TimeComponentPrefix (Component : Type) where
  | empty
  | hour (hour : Component)
  | minute (hour minute : Component)
  | second (hour minute second : Component)
  deriving Repr, DecidableEq

namespace TimeComponentPrefix

/-- Whether any supplied component satisfies its carrier-specific field-reference predicate; omitted suffixes contribute no reference. -/
def referencesFieldWith (checked : TimeComponentPrefix Component)
    (referencesField : Component → FieldId → Bool)
    (field : FieldId) : Bool :=
  match checked with
  | .empty => false
  | .hour hourComponent => referencesField hourComponent field
  | .minute hourComponent minuteComponent =>
      referencesField hourComponent field ||
        referencesField minuteComponent field
  | .second hourComponent minuteComponent secondComponent =>
      referencesField hourComponent field ||
        referencesField minuteComponent field ||
        referencesField secondComponent field

/-- Evaluate one supplied prefix through its carrier-specific reader. Computation stops on formal poison; validation still evaluates later arguments
    before projecting formal state (spec/05 §3). Omitted trailing slots remain fixed zeroes. -/
@[simp]
def evaluateWithSubterm [SizeOf Component] (checked : TimeComponentPrefix Component)
    (read : (component : Component) → sizeOf component < sizeOf checked → Except Error TimeConstructionComponent)
    (phase : Phase := .computation) :
    Except Error TimeConstructionResult :=
  match checked with
  | .empty =>
      pure (TimeConstructionArity.zero.evaluate .empty .empty .empty)
  | .hour hourField => do
      let hourValue ← read hourField (by simp +arith)
      pure (TimeConstructionArity.hour.evaluate hourValue .empty .empty)
  | .minute hourField minuteField => do
      let hourValue ← read hourField (by simp +arith)
      match hourValue with
      | .unavailable cause =>
          if phase == .validation then (read minuteField (by simp +arith)).map (fun _ => .unavailable cause)
          else pure (.unavailable cause)
      | hourValue =>
          let minuteValue ← read minuteField (by simp +arith)
          pure (TimeConstructionArity.minute.evaluate hourValue minuteValue .empty)
  | .second hourField minuteField secondField => do
      let hourValue ← read hourField (by simp +arith)
      match hourValue with
      | .unavailable cause =>
          if phase == .validation then do
            let _ ← read minuteField (by simp +arith)
            let _ ← read secondField (by simp +arith)
            pure (.unavailable cause)
          else pure (.unavailable cause)
      | hourValue =>
          let minuteValue ← read minuteField (by simp +arith)
          match minuteValue with
          | .unavailable cause =>
              if phase == .validation then (read secondField (by simp +arith)).map (fun _ => .unavailable cause)
              else pure (.unavailable cause)
          | minuteValue =>
              let secondValue ← read secondField (by simp +arith)
              pure (TimeConstructionArity.second.evaluate
                hourValue minuteValue secondValue)

/-- The ordinary reader specializes the same ordered prefix evaluation. -/
def evaluateWith (checked : TimeComponentPrefix Component)
    (read : Component → Except Error TimeConstructionComponent)
    (phase : Phase := .computation) :
    Except Error TimeConstructionResult :=
  checked.evaluateWithSubterm (fun component _ => read component) phase

end TimeComponentPrefix

/-- Host conversion faults remain distinct from missing values and formal poison (spec/05 §3). -/
inductive TimeConstructionInputFault where
  | payloadKind (field : FieldId)
  | stringNotConvertible (field : FieldId) (value : String)
  | nonIntegralPayload (field : FieldId) (value : Rat)
  deriving Repr, DecidableEq


/-- Project one checked Number cell to the constructor component domain without applying arithmetic truncation or accepting a mismatched runtime payload. The classifier is placement-neutral; scalar and addressed readers supply the exact field identity. -/
def classifyTimeNumberComponent (field : FieldId)
    (observation : CellObservation Value) :
    Except TimeConstructionInputFault TimeConstructionComponent :=
  match observation with
  | .empty => pure .empty
  | .unknown cause | .poison cause => pure (.unavailable cause)
  | .value (.num value) =>
      if value.den = 1 then
        pure (.value value.num)
      else
        throw (.nonIntegralPayload field value)
  | .value _ => throw (.payloadKind field)


/-- Convert one already checked digit String through the bounded host-decimal conversion. Pattern and maximum-length checking happened when the document was constructed. The classifier is placement-neutral; scalar and addressed readers supply the exact field identity. -/
def classifyTimeStringComponent (field : FieldId)
    (observation : CellObservation Value) :
    Except TimeConstructionInputFault TimeConstructionComponent :=
  match observation with
  | .empty => pure .empty
  | .unknown cause | .poison cause => pure (.unavailable cause)
  | .value (.str value) =>
      match parseTemporalComponentInt32? value with
      | some amount => pure (.value amount)
      | none => throw (.stringNotConvertible field value)
  | .value _ => throw (.payloadKind field)


/-- Project a clock from whichever temporal payload carries one.

    **The declared kind is deliberately not consulted.** A cell's value family is its declared
    format's, so a DATE-declared field formatted `HH:mm:ss` holds a clock and the Kernel reads it:
    `Time(HoursFromTime(…), …)` over such a field is admitted and computes `08:30:45` from a stored
    `08:30:45`, on both codegen strategies
    ([checkpoint](../../docs/sources/computation-placement-and-constant-probes.md#src-temporal-difference-gates-read-the-format)).
    Earlier guards here required the kind to match the payload, which turned that admitted source
    into a `payloadKind` fault. `.value _` still fails, so a payload carrying no clock at all
    remains a real refusal. -/
private def clockObservation? :
    CellObservation Value → Option (CellObservation TimeOfDay)
  | .empty => some .empty
  | .unknown cause => some (.unknown cause)
  | .poison cause => some (.poison cause)
  | .value (.temporal (.time _ clock)) => some (.value clock)
  | .value (.temporal (.dateTime _ _ clock _)) => some (.value clock)
  | .value _ => none

private def componentOfNumericOperand (field : FieldId) :
    NumericOperand → Except TimeConstructionInputFault TimeConstructionComponent
  | .value amount fillability =>
      if fillability.canGrow || fillability.canShrink then
        pure .empty
      else if amount.den = 1 then
          pure (.value amount.num)
        else
          throw (.nonIntegralPayload field amount)
  | .unknown cause => pure (.unavailable cause)

/-- Project a selected clock component without imposing placement. Empty temporal input follows the extractor's symmetric numeric-zero rule; formal unavailability retains its exact cause. -/
def classifyTimeExtractorComponent (field : FieldId)
    (part : TimeNumericPart)
    (observation : CellObservation Value) :
    Except TimeConstructionInputFault TimeConstructionComponent :=
  match clockObservation? observation with
  | some projected =>
      componentOfNumericOperand field (part.fromTimeObservation projected)
  | none => throw (.payloadKind field)

inductive ResolvedTimeConstructionSource where
  | number (field : FlatNumberField)
  | string (field : FlatStringField)
  | constant (value : Int)
  | extractor (field : FlatTemporalField) (part : TimeNumericPart)
  | nowExtractor (part : TimeNumericPart)
  deriving Repr, DecidableEq

namespace TimeComponentPrefix

def sources (source : TimeComponentPrefix α) : List α :=
  match source with
  | .empty => []
  | .hour h => [h]
  | .minute h m => [h, m]
  | .second h m s => [h, m, s]

def mapM [Monad m] (f : TimeComponentPosition → α → m β) : TimeComponentPrefix α → m (TimeComponentPrefix β)
  | .empty => pure .empty
  | .hour h => return .hour (← f .hour h)
  | .minute h m => return .minute (← f .hour h) (← f .minute m)
  | .second h m s => return .second (← f .hour h) (← f .minute m) (← f .second s)

def allWithPosition (f : TimeComponentPosition → α → Bool) : TimeComponentPrefix α → Bool
  | .empty => true
  | .hour h => f .hour h
  | .minute h m => f .hour h && f .minute m
  | .second h m s => f .hour h && f .minute m && f .second s

end TimeComponentPrefix
end A12Kernel
