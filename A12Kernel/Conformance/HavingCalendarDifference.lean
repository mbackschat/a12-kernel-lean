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
  [.dateDifference .months (reference .inner 1) (reference .outer 2),
   .dateDifference .years (reference .inner 1) (reference .outer 2),
   .dayDifference .utc (reference .inner 1) (reference .outer 2)]
private def dateCell (basis : DateCalendarBasis) : CheckedCell := {
  rawPresent := true, findings := [], parsed := some (.temporal (.date {
    instant := { epochMillis := 0 }, parts := { year := 1970, month := 1, day := 1 }, basis })) }
private def emptyCell : CheckedCell := { rawPresent := false, parsed := none, findings := [] }
private def invalid : CheckedCell := { rawPresent := true, parsed := none, findings := [.malformed] }
private def frame : CorrelationFrame := { innerEnv := [(10, 1)], outerEnv := [(10, 2)] }
private def pair (first second : CheckedCell) : CorrelationContext := {
  read := fun _ id => if id == 1 then first else second }
private def resolving (context : CorrelationContext) : ResolvingCorrelationContext String := {
  read := fun env id => .ok (context.read env id)
  bindingError := fun _ => "binding", unsupportedDateCalendar := "calendar" }

example : atoms.all (fun atom =>
    atom.readComputation (pair (dateCell .legacyHybrid) (dateCell .storedGregorian)) frame == .error () &&
    atom.readComputationResolving (resolving (pair (dateCell .legacyHybrid) (dateCell .storedGregorian))) frame == .error "calendar" &&
    atom.readValidation (pair (dateCell .legacyHybrid) (dateCell .storedGregorian)) frame == .error () &&
    atom.readComputation (pair (dateCell .legacyHybrid) emptyCell) frame == .ok (.value 0) &&
    atom.readComputation (pair emptyCell (dateCell .legacyHybrid)) frame == .ok (.value 0) &&
    atom.readComputation (pair invalid (dateCell .legacyHybrid)) frame == .ok (.poison .malformed)) = true := by native_decide

example : atoms.all (fun atom => atom.readComputationResolving {
    read := fun _ id => if id == 1 then .ok invalid else .error "captured read"
    bindingError := fun _ => "binding", unsupportedDateCalendar := "calendar" } frame == .error "captured read") = true := by native_decide

private def condition (atom : HavingNumericAtom) : CorrelatedHaving := .leaf (.numeric {
  op := .ordinary .equal, left := .atom atom, right := .literal { value := 0, authoredScale := 0 } })
private def holds : CorrelatedHaving := .presence .filled { origin := .inner, field := 3 }
private def fails : CorrelatedHaving := .presence .notFilled { origin := .inner, field := 3 }
private def faulty : CorrelationContext := pair (dateCell .legacyHybrid) (dateCell .storedGregorian)

example : atoms.all (fun atom =>
    CorrelatedHaving.evalComputationIn (.or holds (condition atom)) faulty frame == .ok .holds &&
    CorrelatedHaving.evalComputationIn (.and fails (condition atom)) faulty frame == .ok .notTrue &&
    CorrelatedHaving.evalComputationIn (.and holds (condition atom)) faulty frame == .error () &&
    CorrelatedHaving.evalComputationIn (.or fails (condition atom)) faulty frame == .error ()) = true := by native_decide

private def scanContext : CorrelationContext := {
  read := fun env id => dateCell (if id == 1 && env == [(10, 2)] then .legacyHybrid else .storedGregorian) }

example : atoms.all (fun atom =>
    (condition atom).scanComputation scanContext [] (fun (_ : Unit) _ => Sum.inr true)
      [[(10, 1)], [(10, 2)]] () == .error () &&
    (condition atom).scanComputation scanContext [] (fun (_ : Unit) _ => Sum.inr true)
      [[(10, 1)], [(10, 3)], [(10, 2)]] () == .ok (.terminated true) &&
    (match scanFilteredComputationFirstFilled (condition atom) scanContext [] (fun _ => ValueListCell.present (kind := .number) 1)
      [[(10, 1)], [(10, 2)]] false {} with | .error () => true | .ok _ => false)) = true := by native_decide

example : atoms.all (fun atom => CorrelatedHaving.fieldIds (condition atom) == [1, 2] &&
    CorrelatedHaving.markedFieldIds (condition atom) == [2]) = true := by native_decide

end A12Kernel.Conformance.HavingCalendarDifference
