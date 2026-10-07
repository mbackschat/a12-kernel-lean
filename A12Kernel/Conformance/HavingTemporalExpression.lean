import A12Kernel.Elaboration.CorrelationWellFormed

namespace A12Kernel.Conformance.HavingTemporalExpression
open A12Kernel

local instance [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .ok a, .ok b => decidable_of_iff (a = b) (by simp)
  | .error a, .error b => decidable_of_iff (a = b) (by simp)
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

private def frame : CorrelationFrame := { innerEnv := [(10, 1)], outerEnv := [(10, 2)] }
private def empty : CheckedCell := { rawPresent := false, parsed := none, findings := [] }
private def invalid : CheckedCell := { rawPresent := true, parsed := none, findings := [.malformed] }
private def required : CheckedCell := { empty with findings := [.required] }
private def stamp (millis : Int) : CheckedCell := {
  rawPresent := true, findings := [], parsed := some
    (.temporal (.dateTime { epochMillis := millis } { year := 1970, month := 1, day := 1 }
    { hour := 0, minute := 0, second := 0, valid := by decide } .legacyHybrid)) }
private def ref (id : FieldId := 1) (origin : HavingOrigin := .inner) : HavingTemporalRef :=
  { origin, field := { id, kind := .dateTime, components := TemporalComponents.now } }
private def source (core : TemporalExpressionOf HavingTemporalAtom ScalarTemporalConstructorOp) :
    A12Kernel.HavingTemporalExpression := { core, profile := .utc, baseYear := none }
private def fieldSource := source (.atom (.field (ref)))
private def date := source (.apply .dateFromDateTime fieldSource.core [])
private def time := source (.apply .timeFromDateTime fieldSource.core [])
private def joined := source (.apply .dateTime date.core
  [.apply .timeFromDateTime (.atom (.field (ref 1 .outer))) []])
private def base : ResolvingCorrelationContext CorrelationRuntimeFault :=
  ({ read := fun env _ => stamp (if env == frame.innerEnv then 0 else 3600000) } : CorrelationContext).asResolving

example : joined.references = [{ origin := .inner, source := .inl ref.field },
      { origin := .outer, source := .inl (ref 1 .outer).field }] ∧
    joined.evaluate .validation base frame = .ok (.value (.instant { epochMillis := 3600000 }) true) ∧
    joined.evaluate .computation base frame = .ok (.value (.instant { epochMillis := 3600000 }) true) ∧
    (HavingNumericAtom.temporalExpressionPart (.time .hour) joined).fieldOrigins = [(.inner, 1), (.outer, 1)] := by native_decide

private def laterFault : ResolvingCorrelationContext CorrelationRuntimeFault := { base with
  read := fun env id => if env == frame.innerEnv then pure invalid else .error (.storedTextUnavailable id) }
example : joined.evaluate .validation laterFault frame = .error (.storedTextUnavailable 1) ∧
    joined.evaluate .computation laterFault frame = .ok (.unknown .malformed) ∧
    joined.evaluate .computation { laterFault with read := fun _ id => .error (.storedTextUnavailable id) } frame =
      .error (.storedTextUnavailable 1) ∧
    joined.evaluate .computation { laterFault with read := fun env id => if env == frame.innerEnv then pure empty else .error (.storedTextUnavailable id) } frame =
      .error (.storedTextUnavailable 1) := by native_decide

private def clockJoined := source (.apply .dateTime date.core [.apply .timeFromDateTime (.atom .now) []])
example : clockJoined.evaluate .validation { base with read := fun _ _ => pure invalid } frame = .error .worldUnavailable ∧
    clockJoined.evaluate .computation { base with read := fun _ _ => pure invalid } frame = .ok (.unknown .malformed) ∧
    clockJoined.evaluate .computation { base with read := fun _ _ => pure empty } frame = .error .worldUnavailable := by native_decide

private def hour : HavingNumericAtom := .temporalExpressionPart (.time .hour) time
example : hour.readValidationResolving { base with read := fun _ _ => pure required } frame = .ok (.error ()) ∧
    hour.readComputationResolving { base with read := fun _ _ => pure required } frame = .ok (.value 0) ∧
    hour.readValidationResolving { base with read := fun _ _ => pure empty } frame = .ok (.ok (.value 0 .both)) ∧
    hour.readComputationResolving laterFault frame = .ok (.poison .malformed) := by native_decide

private def comparison : HavingTemporalComparison := { operator := .equal, left := date, right := source (.atom .today) }
example : comparison.evalValidationRead { base with read := fun _ _ => pure invalid } frame = .error .worldUnavailable ∧
    comparison.evalComputationRead { base with read := fun _ _ => pure invalid } frame = .ok (.poison .malformed) ∧
    comparison.evalComputationRead { base with read := fun _ _ => pure empty } frame = .error .worldUnavailable := by native_decide

private def retainedDate := source (.atom (.field { origin := .inner, field := { id := 2, kind := .date, components := TemporalComponents.fullDate } }))
private def mixed : HavingTemporalComparison := { operator := .after, left := retainedDate, right := source (.atom .now) }
private def dated : ResolvingCorrelationContext CorrelationRuntimeFault := { base with
  world := some { now := { epochMillis := 0 } }
  read := fun _ _ => pure { rawPresent := true, findings := [], parsed := some (.temporal (.date {
    instant := { epochMillis := 3600000 }, parts := { year := 1970, month := 1, day := 1 }, basis := .legacyHybrid })) } }
example : mixed.evalValidationRead dated frame = .ok (.fired .value) ∧
    mixed.evalComputationRead dated frame = .ok .holds := by native_decide

private def model : FlatModel := {
  fields := [{
    id := 1, name := "Stamp", groupPath := ["Rows"], repeatableScope := [10]
    policy := { kind := .temporal .dateTime TemporalComponents.now }
    temporalTargetPolicy := some { format := "yyyy-MM-dd'T'HH:mm:ss" } }]
  repeatableGroups := [{ level := 10, path := ["Rows"], repeatability := some 2 }] }
example : joined.wellFormed model [10] [10] = true ∧
    joined.wellFormed model [10] [] = false ∧
    joined.wellFormed model [] [10] = false ∧
    ({ joined with profile := .europeBerlin }).wellFormed model [10] [10] = false ∧
    ({ joined with baseYear := some 2024 }).wellFormed model [10] [10] = false ∧
    (source (.apply .dateTime date.core [])).wellFormed model [10] [10] = false ∧
    (source (.apply .dateTime time.core [date.core])).wellFormed model [10] [10] = false ∧
    (source (.atom (.field { (ref) with field := { id := 1, kind := .dateTime, components := TemporalComponents.time } }))).wellFormed model [10] [10] = false := by native_decide

private def yearlessModel : FlatModel := { model with baseYear := some 2024, fields := model.fields.map fun field => { field with
  policy := { kind := .temporal .date { TemporalComponents.fullDate with year := false } }
  temporalTargetPolicy := some { format := "MM-dd" } } }
private def yearless := source (.atom (.field { origin := .inner, field := {
  id := 1, kind := .date, components := { TemporalComponents.fullDate with year := false } } }))
private def completed := { yearless with baseYear := some 2024 }
private def storedDate : CheckedCell := { rawPresent := true, findings := [], parsed := some (.temporal (.date {
  instant := { epochMillis := 0 }, parts := { year := 1970, month := 1, day := 1 }, basis := .legacyHybrid })) }
example : completed.wellFormed yearlessModel [10] [] = true ∧
    yearless.wellFormed yearlessModel [10] [] = false ∧
    (HavingNumericAtom.temporalExpressionPart (.date .year) completed).readComputationResolving
      { base with read := fun _ _ => pure storedDate } frame = .ok (.value 2024) ∧
    yearless.components? = some { TemporalComponents.fullDate with year := false } := by native_decide

private def rangeSource (origin : HavingOrigin := .inner) (bound : DateRangeBound := .start)
    (components : TemporalComponents := TemporalComponents.fullDate) :=
  source (.atom (.rangeBound origin { id := 1 } components bound))
private def rangeCell (origin : HavingOrigin) : CheckedCell := {
  rawPresent := true, findings := [], parsed := some (.dateRange (.exact {
    start := {
      instant := { epochMillis := if origin == .inner then 0 else 3600000 }
      parts := { year := 1970, month := 1, day := 1 }, basis := .legacyHybrid }
    finish := {
      instant := { epochMillis := if origin == .inner then 86400000 else 90000000 }
      parts := { year := 1970, month := 1, day := 2 }, basis := .legacyHybrid } })) }
private def rangeContext : ResolvingCorrelationContext CorrelationRuntimeFault := { base with
  read := fun env _ => pure (rangeCell (if env == frame.innerEnv then .inner else .outer)) }
private def rangeJoined := source (.apply .dateTime (rangeSource).core [.apply .timeFromDateTime (.atom .now) []])

example : [Phase.validation, .computation].all (fun phase =>
    [HavingOrigin.inner, .outer].all fun origin => [DateRangeBound.start, .finish].all fun bound =>
      let millis := (if origin == .inner then 0 else 3600000) + (if bound == .start then 0 else 86400000)
      (rangeSource origin bound).evaluate phase rangeContext frame == .ok (.value (.date {
        instant := { epochMillis := millis }, parts := { year := 1970, month := 1, day := if bound == .start then 1 else 2 }
        basis := .legacyHybrid }) true)) = true ∧
    ((rangeSource .outer).references.map fun reference => (reference.origin, reference.fieldId)) = [(.outer, 1)] := by native_decide

example : rangeJoined.evaluate .validation { base with read := fun _ _ => pure invalid } frame = .error .worldUnavailable ∧
    rangeJoined.evaluate .computation { base with read := fun _ _ => pure invalid } frame = .ok (.unknown .malformed) ∧
    rangeJoined.evaluate .computation { base with read := fun _ _ => pure empty } frame = .error .worldUnavailable ∧
    (rangeSource).evaluate .validation { base with read := fun _ _ => pure required } frame = .ok (.unknown .required) ∧
    (rangeSource).evaluate .computation { base with read := fun _ _ => pure required } frame = .ok .notEvaluated ∧
    (rangeSource).evaluate .validation base frame = .error .calendarUnavailable := by native_decide

private def rangeModel : FlatModel := { model with fields := model.fields.map fun field => { field with
  policy := { kind := .dateRange }, temporalTargetPolicy := none
  dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" } } }
example : (rangeSource).wellFormed rangeModel [10] [] = true ∧
    (rangeSource .outer).wellFormed rangeModel [] [10] = true ∧
    (rangeSource).wellFormed rangeModel [] [10] = false ∧
    (rangeSource .outer).wellFormed rangeModel [10] [] = false ∧
    (rangeSource .inner .start TemporalComponents.time).wellFormed rangeModel [10] [] = false ∧
    (rangeSource).wellFormed model [10] [] = false ∧
    ({ rangeSource with baseYear := some 2024 }).wellFormed rangeModel [10] [] = false := by native_decide

private def fragment : CheckedCell := {
  rawPresent := true, findings := [],
  parsed := some (.dateRange (.yearlessMonth 2 2)) }
private def monthComponents : TemporalComponents := { year := false, month := true, day := false, hour := false, minute := false, second := false }
example : (rangeSource).evaluate .validation { base with read := fun _ _ => pure fragment } frame = .error .calendarUnavailable ∧
    (rangeSource .inner .finish monthComponents).evaluate .computation rangeContext frame = .error .calendarUnavailable ∧
    (rangeSource .inner .finish monthComponents).components? = some monthComponents ∧
    (({ rangeSource .inner .finish monthComponents with baseYear := some 2024 }).components?) =
      some { monthComponents with year := true } := by native_decide

end A12Kernel.Conformance.HavingTemporalExpression
