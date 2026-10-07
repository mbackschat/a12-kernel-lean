import A12Kernel.Semantics.FirstFilledValue

namespace A12Kernel.Conformance.HavingCalendarDifference
open A12Kernel

local instance [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .ok a, .ok b => decidable_of_iff (a = b) (by simp)
  | .error a, .error b => decidable_of_iff (a = b) (by simp)
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

private def reference (origin : HavingOrigin) (id : FieldId) : HavingTemporalRef := {
  origin, field := { id, kind := .date, components := { year := true, month := true, day := true, hour := false, minute := false, second := false } } }
private def atoms : List HavingNumericAtom :=
  [.dateDifference .months (.field (reference .inner 1)) (.field (reference .outer 2)),
   .dateDifference .years (.field (reference .inner 1)) (.field (reference .outer 2)),
   .dayDifference .utc (.field (reference .inner 1)) (.field (reference .outer 2))]
private def dateCell (basis : DateCalendarBasis) : CheckedCell := {
  rawPresent := true, findings := [], parsed := some (.temporal (.date {
    instant := { epochMillis := 0 }, parts := { year := 1970, month := 1, day := 1 }, basis })) }
private def emptyCell : CheckedCell := { rawPresent := false, parsed := none, findings := [] }
private def invalid : CheckedCell := { rawPresent := true, parsed := none, findings := [.malformed] }
private def frame : CorrelationFrame := { innerEnv := [(10, 1)], outerEnv := [(10, 2)] }
private def pair (first second : CheckedCell) : CorrelationContext := {
  read := fun _ id => if id == 1 then first else second }
private def resolving (context : CorrelationContext) : ResolvingCorrelationContext String := {
  world := context.world
  read := fun env id => .ok (context.read env id)
  bindingError := fun _ => "binding", unsupportedDateCalendar := "calendar", temporalValueFailure := "value failure"
  worldUnavailable := "world unavailable"
  typeValidityValueFailure := "type validity value failure", groupUnavailable := fun _ => "group unavailable" }

example : atoms.all (fun atom =>
    atom.readComputation (pair (dateCell .legacyHybrid) (dateCell .storedGregorian)) frame == .error () &&
    atom.readComputationResolving (resolving (pair (dateCell .legacyHybrid) (dateCell .storedGregorian))) frame == .error "calendar" &&
    atom.readValidation (pair (dateCell .legacyHybrid) (dateCell .storedGregorian)) frame == .error () &&
    atom.readComputation (pair (dateCell .legacyHybrid) emptyCell) frame == .ok (.value 0) &&
    atom.readComputation (pair emptyCell (dateCell .legacyHybrid)) frame == .ok (.value 0) &&
    atom.readComputation (pair invalid (dateCell .legacyHybrid)) frame == .ok (.poison .malformed)) = true := by native_decide

example : atoms.all (fun atom => atom.readComputationResolving {
    read := fun _ id => if id == 1 then .ok invalid else .error "captured read"
    bindingError := fun _ => "binding", unsupportedDateCalendar := "calendar", temporalValueFailure := "value failure"
    worldUnavailable := "world unavailable"
    typeValidityValueFailure := "type validity value failure", groupUnavailable := fun _ => "group unavailable" } frame == .error "captured read") = true := by native_decide

private def condition (atom : HavingNumericAtom) : CorrelatedHaving := .leaf (.numeric {
  op := .ordinary .equal, left := .atom atom, right := .literal { value := 0, authoredScale := 0 } })
private def holds : CorrelatedHaving := .presence .filled { origin := .inner, field := 3 }
private def fails : CorrelatedHaving := .presence .notFilled { origin := .inner, field := 3 }
private def faulty : CorrelationContext := pair (dateCell .legacyHybrid) (dateCell .storedGregorian)

example : atoms.all (fun atom =>
    CorrelatedHaving.evalComputationIn (.or holds (condition atom)) faulty frame == .ok .holds &&
    CorrelatedHaving.evalComputationIn (.and fails (condition atom)) faulty frame == .ok .notTrue &&
    CorrelatedHaving.evalComputationIn (.and holds (condition atom)) faulty frame == .error .calendarUnavailable &&
    CorrelatedHaving.evalComputationIn (.or fails (condition atom)) faulty frame == .error .calendarUnavailable) = true := by native_decide

private def scanContext : CorrelationContext := {
  read := fun env id => dateCell (if id == 1 && env == [(10, 2)] then .legacyHybrid else .storedGregorian) }

example : atoms.all (fun atom =>
    (condition atom).scanComputation scanContext [] (fun (_ : Unit) _ => Sum.inr true)
      [[(10, 1)], [(10, 2)]] () == .error .calendarUnavailable &&
    (condition atom).scanComputation scanContext [] (fun (_ : Unit) _ => Sum.inr true)
      [[(10, 1)], [(10, 3)], [(10, 2)]] () == .ok (.terminated true) &&
    (match scanFilteredComputationFirstFilled (condition atom) scanContext [] (fun _ => ValueListCell.present (kind := .number) 1)
      [[(10, 1)], [(10, 2)]] false {} with | .error .calendarUnavailable => true | _ => false)) = true := by native_decide

example : atoms.all (fun atom => CorrelatedHaving.fieldIds (condition atom) == [1, 2] &&
    CorrelatedHaving.markedFieldIds (condition atom) == [2]) = true := by native_decide


private def staticAtoms : List HavingNumericAtom :=
  let literal : ResolvedDateDifferenceOperand HavingTemporalRef := .literal { year := some 1970, month := 1, day := 1 } 2023
  [.dateDifference .months literal (.field (reference .outer 2)),
   .dateDifference .years (.field (reference .outer 2)) (.baseYear 1970 .direct),
   .dayDifference .utc literal (.field (reference .outer 2))]

example : staticAtoms.all (fun atom => atom.origins == [.outer] &&
    CorrelatedHaving.fieldIds (condition atom) == [2] &&
    CorrelatedHaving.markedFieldIds (condition atom) == [2] &&
    atom.readComputationResolving {
      read := fun env id => if env == frame.outerEnv && id == 2 then .ok (dateCell .storedGregorian) else .error "unexpected read"
      bindingError := fun _ => "binding", unsupportedDateCalendar := "calendar", temporalValueFailure := "value failure"
      worldUnavailable := "world unavailable"
      typeValidityValueFailure := "type validity value failure", groupUnavailable := fun _ => "group unavailable" } frame == .ok (.value 0) &&
    atom.readComputation (pair emptyCell invalid) frame == .ok (.poison .malformed) &&
    atom.readComputation (pair invalid emptyCell) frame == .ok (.value 0)) = true := by native_decide


example : (HavingNumericAtom.dayDifference .utc (.baseYear 2024 .direct)
    (.literal { year := none, month := 3, day := 1 } 2024)).readComputationResolving {
      read := fun _ _ => .error "unexpected read", bindingError := fun _ => "binding"
      unsupportedDateCalendar := "calendar", temporalValueFailure := "value failure"
      worldUnavailable := "world unavailable"
      typeValidityValueFailure := "type validity value failure", groupUnavailable := fun _ => "group unavailable" } frame = .ok (.value 60) := by native_decide

private def clockAtoms : List HavingNumericAtom :=
  [.dateDifference .months (.field (reference .inner 1)) (.today .utc),
   .dateDifference .years (.today .utc) (.field (reference .inner 1)),
   .dayDifference .utc (.field (reference .inner 1)) (.today .utc)]

example : clockAtoms.all (fun atom =>
    let noClock := pair (dateCell .storedGregorian) (dateCell .storedGregorian)
    let clock := { noClock with world := some { now := { epochMillis := 0 } } }
    atom.readComputation noClock frame == .error () &&
    atom.readValidationResolving (resolving noClock) frame == .error "calendar" &&
    atom.readComputation clock frame == .ok (.value 0) &&
    atom.readValidationResolving (resolving clock) frame == .ok (.ok (.value 0 .fixed)) &&
    atom.origins == [.inner] && CorrelatedHaving.fieldIds (condition atom) == [1] &&
    CorrelatedHaving.markedFieldIds (condition atom) == [] &&
    CorrelatedHaving.evalComputationIn (.or holds (condition atom)) noClock frame == .ok .holds &&
    CorrelatedHaving.evalComputationIn (.and fails (condition atom)) noClock frame == .ok .notTrue &&
    CorrelatedHaving.evalComputationIn (.and holds (condition atom)) noClock frame == .error .calendarUnavailable) = true := by native_decide

example : clockAtoms.all (fun atom =>
    [emptyCell, invalid].all (fun cell =>
      atom.readComputation (pair cell (dateCell .storedGregorian)) frame == .error ()) &&
    atom.readComputation { (pair emptyCell (dateCell .storedGregorian)) with
      world := some { now := { epochMillis := 0 } } } frame == .ok (.value 0) &&
    atom.readComputation { (pair invalid (dateCell .storedGregorian)) with
      world := some { now := { epochMillis := 0 } } } frame == .ok (.poison .malformed)) = true := by native_decide

private def subdayClock (unit : DateTimeSubdayUnit) (origin : HavingOrigin := .inner)
    (reverse : Bool := false) : HavingNumericAtom :=
  let field := FlatTemporalOperand.fieldValue {
    origin, field := { id := 1, kind := .dateTime, components := TemporalComponents.now } : HavingTemporalRef }
  if reverse then .dateTimeDifference unit .nowValue field else .dateTimeDifference unit field .nowValue

private def instantCell : CheckedCell := {
  rawPresent := true, findings := [], parsed := some (.temporal (.dateTime
    { epochMillis := 1000 } { year := 1970, month := 1, day := 1 } { hour := 0, minute := 0, second := 1, valid := by decide } .storedGregorian)) }

example : [DateTimeSubdayUnit.hours, .minutes, .seconds].all (fun unit =>
    let atom := subdayClock unit
    let noClock := pair instantCell instantCell
    let clock := { noClock with world := some { now := { epochMillis := 1000 } } }
    atom.readValidation noClock frame == .error () &&
    atom.readComputation noClock frame == .error () &&
    atom.readValidationResolving (resolving noClock) frame == .error "calendar" &&
    atom.readComputationResolving (resolving noClock) frame == .error "calendar" &&
    atom.readComputation clock frame == .ok (.value 0) &&
    atom.readValidationResolving (resolving clock) frame == .ok (.ok (.value 0 .fixed)) &&
    atom.origins == [.inner] && CorrelatedHaving.fieldIds (condition atom) == [1] &&
    CorrelatedHaving.markedFieldIds (condition atom) == [] &&
    CorrelatedHaving.evalComputationIn (.or holds (condition atom)) noClock frame == .ok .holds &&
    CorrelatedHaving.evalComputationIn (.and fails (condition atom)) noClock frame == .ok .notTrue &&
    CorrelatedHaving.evalComputationIn (.and holds (condition atom)) noClock frame == .error .calendarUnavailable &&
    [emptyCell, invalid].all (fun cell => atom.readComputation (pair cell instantCell) frame == .error ()) &&
    atom.readComputation { clock with read := fun _ _ => emptyCell } frame == .ok (.value 0) &&
    atom.readComputation { clock with read := fun _ _ => invalid } frame == .ok (.poison .malformed)) = true := by native_decide

example : [DateTimeSubdayUnit.hours, .minutes, .seconds].all (fun unit =>
    [false, true].all (fun reverse =>
      let atom := subdayClock unit .outer reverse
      atom.origins == [.outer] && atom.fieldOrigins == [(.outer, 1)] &&
      CorrelatedHaving.markedFieldIds (condition atom) == [1] &&
      atom.readComputationResolving {
        world := some { now := { epochMillis := 1000 } },
        read := fun env id => if env == frame.outerEnv && id == 1 then .ok instantCell else .error "wrong origin"
        bindingError := fun _ => "binding", unsupportedDateCalendar := "calendar", temporalValueFailure := "value failure"
        worldUnavailable := "world unavailable"
        typeValidityValueFailure := "type validity value failure", groupUnavailable := fun _ => "group unavailable" } frame == .ok (.value 0))) = true := by native_decide

example :
    let noClock : ResolvingCorrelationContext String := {
      read := fun _ _ => .error "field", bindingError := fun _ => "binding", unsupportedDateCalendar := "calendar", temporalValueFailure := "value failure"
      worldUnavailable := "world unavailable"
      typeValidityValueFailure := "type validity value failure", groupUnavailable := fun _ => "group unavailable" }
    (subdayClock .seconds).readComputationResolving noClock frame = .error "field" ∧
    (subdayClock .seconds .inner true).readComputationResolving noClock frame = .error "calendar" ∧
    (subdayClock .seconds).readValidationResolving noClock frame = .error "field" ∧
    (subdayClock .seconds .inner true).readValidationResolving noClock frame = .error "calendar" := by native_decide

example : [false, true].all (fun reverse =>
    (subdayClock .seconds .inner reverse).readComputation {
      (pair instantCell instantCell) with world := some { now := { epochMillis := 999 } }
    } frame == .ok (.value 0)) = true := by native_decide

end A12Kernel.Conformance.HavingCalendarDifference
