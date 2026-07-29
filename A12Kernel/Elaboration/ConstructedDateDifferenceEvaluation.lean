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

/-- Resolve one post-floor constructed-Date label at local midnight under the pinned Berlin profile. -/
private def resolveBerlin? (parts : DateParts) :
    Option (LocalDateTime × Instant) := do
  let localLabel ←
    LocalDateTime.ofYmdHms? parts.year parts.month parts.day 0 0 0
  let instant ← EuropeBerlinLegacyProfile.resolveLocal? localLabel
  pure (localLabel, instant)

/-- Apply one Berlin difference to two already resolved values. -/
private def differenceBerlinResolved?
    (unit : DateShiftUnit)
    (firstLocal : LocalDateTime) (firstInstant : Instant)
    (secondLocal : LocalDateTime) (secondInstant : Instant) : Option Int :=
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
  match checked.first.evaluate phase input world with
  | .error error => .error (.source error)
  | .ok (.unavailable cause) => .ok (.error cause)
  | .ok (.resolved first) =>
      match checked.second.evaluate phase input world with
      | .error error => .error (.source error)
      | .ok (.unavailable cause) => .ok (.error cause)
      | .ok (.resolved second) =>
          match differenceResolved?
              checked.first.profile checked.unit first second with
          | some result => .ok (.ok result)
          | none =>
              .error (.operationUnavailable checked.unit first second)

end CheckedConstructedDateDifference

/-- Authored position of the checked shift in the bounded mixed difference form. -/
inductive ConstructedDateShiftDifferencePosition where
  | first
  | second
  deriving Repr, DecidableEq

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
  | unknown
  | noValue (notGiven : Bool)
  | fresh (parts : DateParts)
  | exact (instant : Instant) (parts : DateParts) (notGiven : Bool)

namespace DifferenceOperand

def ofConstruction : ConstructedDateObservation → DifferenceOperand
  | .unavailable cause => .unavailable cause
  | .resolved .unknown => .unknown
  | .resolved .incomplete => .noValue true
  | .resolved .unreal => .noValue false
  | .resolved (.real parts) => .fresh parts

def ofShift : ConstructedDateShiftResult → DifferenceOperand
  | .unavailable cause => .unavailable cause
  | .noValue notGiven => .noValue notGiven
  | .value instant parts notGiven => .exact instant parts notGiven

def notGiven : DifferenceOperand → Bool
  | .noValue notGiven | .exact _ _ notGiven => notGiven
  | .unavailable _ | .unknown | .fresh _ => false

def parts? : DifferenceOperand → Option DateParts
  | .fresh parts | .exact _ parts _ => some parts
  | .unavailable _ | .unknown | .noValue _ => none

def berlinResolved? : DifferenceOperand → Option (LocalDateTime × Instant)
  | .fresh parts =>
      CheckedConstructedDateDifference.resolveBerlin? parts
  | .exact instant _ _ =>
      (ModelZone.ConcreteProfile.europeBerlin.localDateTime? instant).map
        (·, instant)
  | .unavailable _ | .unknown | .noValue _ => none

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
  | .unknown, _ | _, .unknown => some (.ok .unavailable)
  | .noValue _, _ | _, .noValue _ =>
      some (.ok (.value 0 (first.notGiven || second.notGiven)))
  | first, second =>
      (differenceValueOperands? profile unit first second).map fun amount =>
        .ok (.value amount (first.notGiven || second.notGiven))

/-- Combine one exact checked shift result with one direct constructed-Date
    observation in authored operand order. The shifted value's exact instant and
    missing provenance remain observable to the difference. -/
def differenceWithConstruction?
    (profile : ModelZone.ConcreteProfile) (unit : DateShiftUnit)
    (position : ConstructedDateShiftDifferencePosition)
    (shiftResult : ConstructedDateShiftResult)
    (construction : ConstructedDateObservation) :
    Option (Except FormalCause ConstructedDateNumericResult) :=
  match position with
  | .first =>
      differenceOperands? profile unit
        (.ofShift shiftResult) (.ofConstruction construction)
  | .second =>
      differenceOperands? profile unit
        (.ofConstruction construction) (.ofShift shiftResult)

private def finishDifference
    (checked : CheckedConstructedDateShift model)
    (position : ConstructedDateShiftDifferencePosition)
    (unit : DateShiftUnit)
    (shiftResult : ConstructedDateShiftResult)
    (construction : ConstructedDateObservation) :
    Except ConstructedDateShiftDifferenceFault
      (Except FormalCause ConstructedDateNumericResult) :=
  match differenceWithConstruction?
      checked.source.profile unit position shiftResult construction with
  | some result => .ok result
  | none => .error (.operationUnavailable unit position)

/-- Evaluate one checked shift and one direct constructed Date in authored operand
    order. The shifted operand retains its exact instant and missing provenance; the
    direct operand is resolved freshly under the same checked model profile. -/
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
  match position with
  | .first =>
      match checked.evaluate phase input world with
      | .error error => .error (.shiftSource error)
      | .ok (.unavailable cause) => .ok (.error cause)
      | .ok shiftResult =>
          match other.evaluate phase input world with
          | .error error => .error (.constructedSource error)
          | .ok (.unavailable cause) => .ok (.error cause)
          | .ok otherResult =>
              checked.finishDifference position unit
                shiftResult otherResult
  | .second =>
      match other.evaluate phase input world with
      | .error error => .error (.constructedSource error)
      | .ok (.unavailable cause) => .ok (.error cause)
      | .ok otherResult =>
          match checked.evaluate phase input world with
          | .error error => .error (.shiftSource error)
          | .ok (.unavailable cause) => .ok (.error cause)
          | .ok shiftResult =>
              checked.finishDifference position unit
                shiftResult otherResult

end CheckedConstructedDateShift

end A12Kernel
