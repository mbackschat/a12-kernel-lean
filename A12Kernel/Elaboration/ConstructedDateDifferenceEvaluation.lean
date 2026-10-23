import A12Kernel.Semantics.ScalarTemporalDifference
import A12Kernel.Elaboration.ConstructedDateShiftEvaluation
import A12Kernel.Semantics.DateTimeDayDifference

/-! # Checked constructed-Date differences

This capsule evaluates checked constructed-Date day, month, and year differences under
UTC/GMT and the pinned Berlin profile. Direct `Date(...)` operands resolve their wall
labels freshly. The bounded mixed form accepts one already-evaluated checked shift in
either authored operand position and feeds its exact instant directly into the existing
calendar-difference mechanism.

The mixed form is not a general temporal expression tree. DateTime operands, arbitrary
recursive lowering, other model zones, repeatable placement, and target storage remain
outside.
-/

namespace A12Kernel

/-- Structural failure outside the reason-bearing result of a checked constructed-Date difference. -/
inductive ConstructedDateDifferenceFault where
  | source (error : ConstructedDateEvaluationFault)
  | operationUnavailable
      (unit : DateShiftUnit)
      (first second : DateConstructionResult)
  deriving Repr, DecidableEq

namespace ModelZone.ConcreteProfile

/-- Static constructed-Date difference support for one selected profile and unit. Both implemented profiles now own all three independently closed mechanisms. -/
def admitsConstructedDateDifference :
    ConcreteProfile → DateShiftUnit → Bool
  | .utc, _ => true
  | .europeBerlin, .days => true
  | .europeBerlin, .months => true
  | .europeBerlin, .years => true

end ModelZone.ConcreteProfile

/-- Two checked constructed-Date sources and one profile-admitted day/month/year difference unit. -/
structure CheckedConstructedDateDifference (model : FlatModel) where
  first : CheckedConstructedDateComponents model
  second : CheckedConstructedDateComponents model
  unit : DateShiftUnit
  unitAdmitted :
    first.profile.admitsConstructedDateDifference unit = true

namespace CheckedConstructedDateDifference

/-- Resolve one constructed-Date label at its hybrid-calendar midnight under the pinned Berlin profile. -/
private def resolveBerlin? (parts : DateParts) :
    Option (LegacyCalendarLabel × Instant) := do
  let label := LegacyCalendarLabel.midnight parts
  pure (label, ← ModelZone.ConcreteProfile.europeBerlin.resolveCalendarLabel? label)

/-- Apply one Berlin difference to two already resolved values. -/
private def differenceBerlinResolved?
    (unit : DateShiftUnit)
    (firstLocal : LegacyCalendarLabel) (firstInstant : Instant)
    (secondLocal : LegacyCalendarLabel) (secondInstant : Instant) : Option Int :=
  match unit with
  | .days =>
      EuropeBerlinLegacyProfile.differenceResolvedInDays?
        firstLocal firstInstant secondLocal secondInstant
  | .months =>
      EuropeBerlinLegacyProfile.differenceResolvedInMonths?
        firstLocal firstInstant secondLocal secondInstant
  | .years =>
      EuropeBerlinLegacyProfile.differenceResolvedInYears?
        firstLocal firstInstant secondLocal secondInstant

/-- Apply one independently closed Berlin difference to two freshly constructed labels. -/
private def differenceBerlin?
    (unit : DateShiftUnit) (first second : DateParts) : Option Int := do
  let (firstLocal, firstInstant) ← resolveBerlin? first
  let (secondLocal, secondInstant) ← resolveBerlin? second
  differenceBerlinResolved?
    unit firstLocal firstInstant secondLocal secondInstant

/-- Delegate one resolved pair to the profile- and unit-specific completed-calendar owner. -/
def differenceResolved? (profile : ModelZone.ConcreteProfile)
    (unit : DateShiftUnit)
    (first second : DateConstructionResult) :
    Option ConstructedDateNumericResult :=
  match profile, unit with
  | .utc, .days => first.differenceLegacyDays? second
  | .utc, .months => first.differenceLegacy? .months second
  | .utc, .years => first.differenceLegacy? .years second
  | .europeBerlin, unit =>
      DateConstructionResult.differenceWith?
        (differenceBerlin? unit) first second

/-- Evaluate the first constructed Date before the second with one explicit optional world, preserve the first reached formal cause, and reuse the established reason-bearing numeric result. -/
def evaluate (checked : CheckedConstructedDateDifference model)
    (phase : Phase) (input : CheckedDocument model)
    (world : Option World) :
    Except ConstructedDateDifferenceFault
      (Except FormalCause ConstructedDateNumericResult) :=
  do
    let pair ← (readTemporalPair phase (fun (source : CheckedConstructedDateComponents model) => source.evaluate phase input world)
      (fun | .unavailable cause => some cause | _ => none) checked.first checked.second).mapError ConstructedDateDifferenceFault.source
    match pair with
    | .error cause => pure (.error cause)
    | .ok (.unavailable cause, _) | .ok (_, .unavailable cause) => pure (.error cause)
    | .ok (.resolved first, .resolved second) =>
        match differenceResolved? checked.first.profile checked.unit first second with
        | some result => pure (.ok result)
        | none => throw (.operationUnavailable checked.unit first second)

end CheckedConstructedDateDifference

/-- Compatibility name for the shared authored shift position. -/
abbrev ConstructedDateShiftDifferencePosition :=
  ShiftDifferencePosition

/-- Structural failure while evaluating the bounded shift/constructed-Date difference form. -/
inductive ConstructedDateShiftDifferenceFault where
  | constructedSource (error : ConstructedDateEvaluationFault)
  | shiftSource (error : ConstructedDateShiftFault)
  | operationUnavailable
      (unit : DateShiftUnit)
      (position : ConstructedDateShiftDifferencePosition)
  deriving Repr, DecidableEq

namespace CheckedConstructedDateShift

private inductive DifferenceOperand where
  | unavailable (cause : FormalCause)
  | noValue (notGiven : Bool)
  | exact (instant : Instant) (parts : DateParts) (notGiven : Bool)

namespace DifferenceOperand

def ofValue : ConstructedDateValue → DifferenceOperand
  | .unavailable cause => .unavailable cause
  | .noValue notGiven => .noValue notGiven
  | .value instant parts notGiven => .exact instant parts notGiven

def notGiven : DifferenceOperand → Bool
  | .noValue notGiven | .exact _ _ notGiven => notGiven
  | .unavailable _ => false

def parts? : DifferenceOperand → Option DateParts
  | .exact _ parts _ => some parts
  | .unavailable _ | .noValue _ => none

def berlinResolved? : DifferenceOperand → Option (LegacyCalendarLabel × Instant)
  | .exact instant _ _ =>
      (ModelZone.ConcreteProfile.europeBerlin.calendarLabel? instant).map
        (·, instant)
  | .unavailable _ | .noValue _ => none

end DifferenceOperand

private def differenceValueOperands?
    (profile : ModelZone.ConcreteProfile) (unit : DateShiftUnit)
    (first second : DifferenceOperand) : Option Int :=
  match profile with
  | .utc => do
      let firstParts ← first.parts?
      let secondParts ← second.parts?
      match unit with
      | .days =>
          DateParts.LegacyHybrid.differenceInDays?
            firstParts secondParts
      | .months =>
          DateDifferenceUnit.betweenLegacy?
            .months firstParts secondParts
      | .years =>
          DateDifferenceUnit.betweenLegacy?
            .years firstParts secondParts
  | .europeBerlin => do
      let (firstLocal, firstInstant) ← first.berlinResolved?
      let (secondLocal, secondInstant) ← second.berlinResolved?
      CheckedConstructedDateDifference.differenceBerlinResolved?
        unit firstLocal firstInstant secondLocal secondInstant

private def differenceOperands?
    (profile : ModelZone.ConcreteProfile) (unit : DateShiftUnit)
    (first second : DifferenceOperand) :
    Option (Except FormalCause ConstructedDateNumericResult) :=
  match first, second with
  | .unavailable cause, _ => some (.error cause)
  | _, .unavailable cause => some (.error cause)
  | .noValue _, _ | _, .noValue _ =>
      some (.ok (.value 0 (first.notGiven || second.notGiven)))
  | first, second =>
      (differenceValueOperands? profile unit first second).map fun amount =>
        .ok (.value amount (first.notGiven || second.notGiven))

/-- Combine one exact checked shift with one exact direct constructed Date in
    authored operand order. Both operands retain their selected instants and missing
    provenance through the shared value boundary. -/
def differenceWithConstruction?
    (profile : ModelZone.ConcreteProfile) (unit : DateShiftUnit)
    (position : ConstructedDateShiftDifferencePosition)
    (shiftResult : ConstructedDateShiftResult)
    (construction : ConstructedDateValue) :
    Option (Except FormalCause ConstructedDateNumericResult) :=
  match position with
  | .first =>
      differenceOperands? profile unit
        (.ofValue shiftResult) (.ofValue construction)
  | .second =>
      differenceOperands? profile unit
        (.ofValue construction) (.ofValue shiftResult)

private def finishDifference
    (checked : CheckedConstructedDateShift model)
    (position : ConstructedDateShiftDifferencePosition)
    (unit : DateShiftUnit)
    (shiftResult : ConstructedDateShiftResult)
    (construction : ConstructedDateValue) :
    Except ConstructedDateShiftDifferenceFault
      (Except FormalCause ConstructedDateNumericResult) :=
  match differenceWithConstruction?
      checked.source.profile unit position shiftResult construction with
  | some result => .ok result
  | none => .error (.operationUnavailable unit position)

/-- Evaluate one checked shift and one direct constructed Date in authored operand
    order. The shifted operand retains its exact instant and missing provenance; the
    direct operand retains the instant selected by its one fresh resolution under
    the same checked model profile. -/
def evaluateDifferenceWith
    (checked : CheckedConstructedDateShift model)
    (other : CheckedConstructedDateComponents model)
    (position : ConstructedDateShiftDifferencePosition)
    (unit : DateShiftUnit)
    (_unitAdmitted :
      checked.source.profile.admitsConstructedDateDifference unit = true)
    (phase : Phase) (input : CheckedDocument model)
    (world : Option World) :
    Except ConstructedDateShiftDifferenceFault
      (Except FormalCause ConstructedDateNumericResult) :=
  do
    let readShift (_ : Unit) := (checked.evaluate phase input world).mapError ConstructedDateShiftDifferenceFault.shiftSource
    let readOther (_ : Unit) := (other.evaluateValue phase input world).mapError ConstructedDateShiftDifferenceFault.constructedSource
    let formalCause? : ConstructedDateValue → Option FormalCause := fun
      | .unavailable cause => some cause
      | _ => none
    let pair ← match position with
      | .first => readTemporalPair phase (fun action => action ()) formalCause? readShift readOther
      | .second => readTemporalPair phase (fun action => action ()) formalCause? readOther readShift
    match pair with
    | .error cause => pure (.error cause)
    | .ok (first, second) =>
        match position with
        | .first => checked.finishDifference position unit first second
        | .second => checked.finishDifference position unit second first

end CheckedConstructedDateShift

end A12Kernel
