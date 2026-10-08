import A12Kernel.Semantics.FullDateInputFormat
import A12Kernel.Semantics.LegacyCalendarExpression
import A12Kernel.Semantics.BaseYearDateSource
import A12Kernel.Semantics.ConstructedDateDay
import A12Kernel.Semantics.DateTimeComparison
import A12Kernel.Semantics.FlatValidation
import A12Kernel.Semantics.String

namespace A12Kernel

/-- The two dynamic point-in-time values admitted beneath Date-component extraction. -/
inductive ConstructedDatePointInTime where
  | today
  | now
  deriving Repr, DecidableEq

/-- Conversion failure or incoherent host input, kept outside Date value and formal-state semantics. A reached `stringNotConvertible` is a runtime failure under spec/05 §3. -/
inductive ConstructedDateComponentFault where
  | payloadKind (field : FieldId)
  | stringNotConvertible (field : FieldId) (value : String)
  | dateYearStoredMissing (field : FieldId)
  | dateYearNotConvertible (field : FieldId) (value : String)
  | nonIntegralPayload (field : FieldId) (value : Rat)
  | todayWorldRequired
  | todayUnavailable (zoneId : String)
  | nowWorldRequired
  | nowUnavailable (zoneId : String)
  | profileDateUnsupported (zoneId : String) (parts : DateParts)
  deriving Repr, DecidableEq

/-- A checked component before cause-free construction classification. -/
inductive CheckedConstructedDateComponent where
  | value (amount : Int)
  | empty
  | unavailable (cause : FormalCause)
  deriving Repr, DecidableEq

def classifyConstructedDateNumber (source : FlatNumberField)
    (observation : CellObservation Value) :
    Except ConstructedDateComponentFault CheckedConstructedDateComponent :=
  match observation with
  | .empty => pure .empty
  | .unknown cause | .poison cause => pure (.unavailable cause)
  | .value (.num value) =>
      if value.den = 1 then
        pure (.value value.num)
      else
        throw (.nonIntegralPayload source.id value)
  | .value _ => throw (.payloadKind source.id)

def classifyConstructedDateString (source : FlatStringField)
    (observation : CellObservation Value) :
    Except ConstructedDateComponentFault CheckedConstructedDateComponent :=
  match observation with
  | .empty => pure .empty
  | .unknown cause | .poison cause => pure (.unavailable cause)
  | .value (.str value) =>
      match parseTemporalComponentInt32? value with
      | some amount => pure (.value amount)
      | none => throw (.stringNotConvertible source.id value)
  | .value _ => throw (.payloadKind source.id)

def classifyConstructedDateYear (source : FlatTemporalField)
    (observation : CellObservation Value) (stored : Option String) :
    Except ConstructedDateComponentFault CheckedConstructedDateComponent :=
  match observation with
  | .empty => pure .empty
  | .unknown cause | .poison cause => pure (.unavailable cause)
  | .value (.temporal value) =>
      -- The formal check's own format-family test, not the declared kind (LF203).
      if !source.holdsValue value then
        throw (.payloadKind source.id)
      else
        match stored with
        | none => throw (.dateYearStoredMissing source.id)
        | some text =>
            match parseAsciiNatural? text with
            | some amount => pure (.value amount)
            | none => throw (.dateYearNotConvertible source.id text)
  | .value _ => throw (.payloadKind source.id)

def classifyConstructedDateExtractor (source : FlatTemporalField) (part : DateNumericPart)
    (observation : CellObservation Value) (partialFormat : Option FullDateTargetFormat := none) :
    Except ConstructedDateComponentFault CheckedConstructedDateComponent :=
  match observation with
  | .empty => pure .empty
  | .unknown cause | .poison cause => pure (.unavailable cause)
  | .value (.temporal value) =>
      if !source.holdsValue value then
        throw (.payloadKind source.id)
      else
        match value.dateParts? with
        | none => throw (.payloadKind source.id)
        | some parts =>
            let amount := part.extract parts
            if amount.den = 1 then
              pure (.value amount.num)
            else
              throw (.nonIntegralPayload source.id amount)
  | .value (.partialDate text) =>
      match partialFormat.bind (·.parseComponents? text) with
      | some parts => pure (.value (part.extract parts).num)
      | none => throw (.payloadKind source.id)
  | .value _ => throw (.payloadKind source.id)
/-- A cause-preserving checked observation around the existing four-way construction result. -/
inductive ConstructedDateObservation where
  | resolved (result : DateConstructionResult)
  | unavailable (cause : FormalCause)
  deriving Repr, DecidableEq

/-- A checked constructed-Date value after its selected profile has resolved a real
    local label exactly once. Fresh construction and every calendar shift share this
    result boundary so exact instant identity cannot be lost between consumers. -/
inductive ConstructedDateValue where
  | noValue (notGiven : Bool)
  | value (instant : Instant) (parts : DateParts) (notGiven : Bool)
  | unavailable (cause : FormalCause)
  deriving Repr, DecidableEq

namespace ConstructedDateValue

/-- Project a fresh or shifted Date value into the shared exact-instant comparison
    domain without reconstructing its selected instant from calendar parts. -/
def comparisonOperand :
    ConstructedDateValue → SimpleComparisonOperand Instant
  | .noValue _ => .notEvaluated
  | .value instant _ notGiven => .value instant (!notGiven)
  | .unavailable cause => .unknown cause

end ConstructedDateValue

/-- The two projections of a constructed Date retain different failure polarities. -/
inductive ConstructedDateValidityOp where
  | valid
  | invalid
  deriving Repr, DecidableEq

namespace ConstructedDateObservation

/-- Resolve three cause-free checked components. `none` means empty; formal unavailability is intercepted before this seam, so this constructor cannot produce `.resolved .unknown`. -/
def ofAvailableComponents (day month year : Option Int) :
    ConstructedDateObservation :=
  let availability : Option Int → DateComponentAvailability
    | some _ => .present
    | none => .empty
  let reality := match day, month, year with
    | some day, some month, some year =>
        let parts : DateParts := {
          year
          month := Int.toNat month
          day := Int.toNat day }
        if DateParts.LegacyHybrid.isReal parts then
          .real parts
        else
          .unreal
    | _, _, _ => .unreal
  .resolved (classifyDateConstruction3
    (availability day) (availability month) (availability year) reality)

/-- Project checked `Valid(Date(...))` without discarding a reached formal cause. -/
def validVerdict : ConstructedDateObservation → Except FormalCause Verdict
  | .resolved result => .ok result.validVerdict
  | .unavailable cause => .error cause

/-- Project checked `Invalid(Date(...))` without discarding a reached formal cause. -/
def invalidVerdict : ConstructedDateObservation → Except FormalCause Verdict
  | .resolved result => .ok result.invalidVerdict
  | .unavailable cause => .error cause

/-- Select the existing validity projection without changing its exact formal-cause channel. -/
def validityVerdict (operation : ConstructedDateValidityOp) :
    ConstructedDateObservation → Except FormalCause Verdict :=
  match operation with
  | .valid => validVerdict
  | .invalid => invalidVerdict

/-- Preserve cause-free UNKNOWN when projecting an observation. The direct component evaluator
excludes that branch; recursive validity may produce it for a non-relevant component (spec/05 §3). -/
def numericPart (observation : ConstructedDateObservation)
    (part : DateNumericPart) :
    Except FormalCause ConstructedDateNumericResult :=
  match observation with
  | .resolved result => .ok (result.numericPart part)
  | .unavailable cause => .error cause

/-- Shift a resolved observation by default-cutover calendar days without losing a formal cause. -/
def addLegacyDays? : ConstructedDateObservation → Int →
    Option ConstructedDateObservation
  | .resolved result, offset => (result.addLegacyDays? offset).map .resolved
  | .unavailable cause, _ => some (.unavailable cause)

/-- Shift a resolved observation by default-cutover calendar months without losing a formal cause. -/
def addLegacyMonths? : ConstructedDateObservation → Int →
    Option ConstructedDateObservation
  | .resolved result, offset => (result.addLegacyMonths? offset).map .resolved
  | .unavailable cause, _ => some (.unavailable cause)

/-- Shift a resolved observation by default-cutover calendar years without losing a formal cause. -/
def addLegacyYears? : ConstructedDateObservation → Int →
    Option ConstructedDateObservation
  | .resolved result, offset => (result.addLegacyYears? offset).map .resolved
  | .unavailable cause, _ => some (.unavailable cause)

end ConstructedDateObservation

inductive ResolvedConstructedDateSource where
  | numberField (source : FlatNumberField)
  | stringField (source : FlatStringField)
  | dateYearField (source : FlatTemporalField)
  | constant (value : Int)
  | extractor (source : FlatTemporalField) (part : DateNumericPart) (partialFormat : Option FullDateTargetFormat := none)
  | baseYearExtractor (year : Int) (source : BaseYearDateSource) (part : DateNumericPart)
  | pointInTimeExtractor (point : ConstructedDatePointInTime) (part : DateNumericPart)
      (zone : String) (profile : ModelZone.ConcreteProfile)
  deriving Repr, DecidableEq

def ResolvedConstructedDateSource.fieldId? : ResolvedConstructedDateSource → Option FieldId
  | .numberField source => some source.id
  | .stringField source => some source.id
  | .dateYearField source | .extractor source _ _ => some source.id
  | _ => none

/-- Clock acquisition and profile decoding remain separate capabilities, as in spec/05 §7. -/
def projectConstructedDateClock (profile : ModelZone.ConcreteProfile) (part : DateNumericPart)
    (instant : Instant) (unavailable : ConstructedDateComponentFault) :
    Except ConstructedDateComponentFault CheckedConstructedDateComponent :=
  match profile.localDate? instant with
  | none => throw unavailable
  | some date => pure (.value (part.extract date.civil.parts).num)

def readConstructedDateClock (point : ConstructedDatePointInTime) (part : DateNumericPart)
    (zone : String) (profile : ModelZone.ConcreteProfile) (world : Option World) :
    Except ConstructedDateComponentFault CheckedConstructedDateComponent := do
  let some world := world | throw (match point with | .today => .todayWorldRequired | .now => .nowWorldRequired)
  let unavailable := match point with | .today => ConstructedDateComponentFault.todayUnavailable zone | .now => .nowUnavailable zone
  let instant ← match point with
    | .today => match world.today? zone with | some instant => pure instant | none => throw unavailable
    | .now => pure world.now
  projectConstructedDateClock profile part instant unavailable

def ResolvedConstructedDateSource.readWith [Monad m] (source : ResolvedConstructedDateSource)
    (phase : Phase) (readCell : FieldId → m CheckedCell) (storedText : FieldId → Option String)
    (world : Option World) (liftFault : Except ConstructedDateComponentFault CheckedConstructedDateComponent → m CheckedConstructedDateComponent) :
    m CheckedConstructedDateComponent := do
  match source with
  | .numberField field => liftFault (classifyConstructedDateNumber field (observeCell phase (← readCell field.id)))
  | .stringField field => liftFault (classifyConstructedDateString field (observeCell phase (← readCell field.id)))
  | .dateYearField field => liftFault (classifyConstructedDateYear field (observeCell phase (← readCell field.id)) (storedText field.id))
  | .extractor field part partialFormat => liftFault (classifyConstructedDateExtractor field part (observeCell phase (← readCell field.id)) partialFormat)
  | .constant value => pure (.value value)
  | .baseYearExtractor year source part => pure (.value (baseYearDateSourceNumericPart year source part).num)
  | .pointInTimeExtractor point part zone profile =>
      liftFault (readConstructedDateClock point part zone profile world)

inductive ResolvedConstructedDateYear (Source : Type) where
  | complete (source : Source)
  | baseYear (year : Int)
  | centuryAndShortYear (century shortYear : Source)
  deriving Repr, DecidableEq

structure ResolvedConstructedDateComponents (Source : Type) where
  day : Source
  month : Source
  year : ResolvedConstructedDateYear Source
  profile : ModelZone.ConcreteProfile
  deriving Repr, DecidableEq

/-- Expose decreasing component subterms without changing authored evaluation order. -/
def ResolvedConstructedDateComponents.attach [SizeOf Source]
    (checked : ResolvedConstructedDateComponents Source) :
    ResolvedConstructedDateComponents { source : Source // sizeOf source < sizeOf checked } :=
  match checked with
  | ⟨day, month, .complete year, profile⟩ =>
      { day := ⟨day, by simp +arith⟩, month := ⟨month, by simp +arith⟩
        year := .complete ⟨year, by simp +arith⟩, profile }
  | ⟨day, month, .baseYear year, profile⟩ =>
      { day := ⟨day, by simp +arith⟩, month := ⟨month, by simp +arith⟩
        year := .baseYear year, profile }
  | ⟨day, month, .centuryAndShortYear century shortYear, profile⟩ =>
      { day := ⟨day, by simp +arith⟩, month := ⟨month, by simp +arith⟩
        year := .centuryAndShortYear ⟨century, by simp +arith⟩ ⟨shortYear, by simp +arith⟩, profile }

def ResolvedConstructedDateComponents.sources (source : ResolvedConstructedDateComponents Source) : List Source :=
  [source.day, source.month] ++ match source.year with
    | .complete year => [year]
    | .baseYear _ => []
    | .centuryAndShortYear century shortYear => [century, shortYear]

def ResolvedConstructedDateYear.readWith [Monad m] (checked : ResolvedConstructedDateYear Source)
    (readSource : Source → m CheckedConstructedDateComponent)
    (phase : Phase := .computation) :
    m CheckedConstructedDateComponent :=
  match checked with
  | .complete source => readSource source
  | .baseYear year => pure (.value year)
  | .centuryAndShortYear century shortYear => do
      match ← readSource century with
      | .unavailable cause =>
          if phase == .validation then discard (readSource shortYear)
          pure (.unavailable cause)
      | centuryPart =>
          match ← readSource shortYear with
          | .unavailable cause => pure (.unavailable cause)
          | shortYearPart =>
              match centuryPart, shortYearPart with
              | .value century, .value shortYear =>
                  -- The four-part constructor rejects a present zero Century (spec/05 §3).
                  pure (.value (if century == 0 then 0 else century * 100 + shortYear))
              | _, _ => pure .empty

private def availableAmount? : CheckedConstructedDateComponent → Option Int
  | .value amount => some amount
  | .empty | .unavailable _ => none

/-- Read Day, Month, and Year in generated argument order before applying a profile
    consumer. Computation stops on formal poison; validation evaluates later arguments, whose
    conversion may still throw, before retaining the first formal cause (spec/05 §3). -/
def ResolvedConstructedDateComponents.evaluateComponentsWith [Monad m] (checked : ResolvedConstructedDateComponents Source)
    (readSource : Source → m CheckedConstructedDateComponent)
    (phase : Phase := .computation) :
    m ConstructedDateObservation := do
  match ← readSource checked.day with
  | .unavailable cause =>
      if phase == .validation then
        discard (readSource checked.month)
        discard (checked.year.readWith readSource phase)
      pure (.unavailable cause)
  | day =>
      match ← readSource checked.month with
      | .unavailable cause =>
          if phase == .validation then discard (checked.year.readWith readSource phase)
          pure (.unavailable cause)
      | month =>
          match ← checked.year.readWith readSource phase with
          | .unavailable cause => pure (.unavailable cause)
          | year =>
              pure (ConstructedDateObservation.ofAvailableComponents
                (availableAmount? day) (availableAmount? month)
                (availableAmount? year))

def ResolvedConstructedDateComponents.resolveFreshInstant (checked : ResolvedConstructedDateComponents Source)
    (parts : DateParts) : Option Instant :=
  (checked.profile.resolveCalendarLabel? {
    parts, time := { hour := 0, minute := 0, second := 0, valid := by decide } }).filter fun instant =>
      decide (-9223372036854775808 ≤ instant.epochMillis ∧ instant.epochMillis ≤ 9223372036854775807)

def ResolvedConstructedDateComponents.applyProfileReality (checked : ResolvedConstructedDateComponents Source) :
    ConstructedDateObservation → ConstructedDateObservation
  | .resolved (.real parts) => if (checked.resolveFreshInstant parts).isSome then .resolved (.real parts) else .resolved .unreal
  | observation => observation

/-- Preserve incomplete versus unreal provenance when turning a constructed label into a Date
value; the selected instant is resolved once for all consumers (spec/05 §3). -/
def ResolvedConstructedDateComponents.finishValue (checked : ResolvedConstructedDateComponents Source) :
    ConstructedDateObservation → ConstructedDateValue
  | .unavailable cause => .unavailable cause
  | .resolved (.real parts) => match checked.resolveFreshInstant parts with
      | some instant => .value instant parts false
      | none => .noValue false
  | .resolved .incomplete => .noValue true
  | .resolved .unreal => .noValue false
  | .resolved .unknown => .unavailable .malformed

end A12Kernel
