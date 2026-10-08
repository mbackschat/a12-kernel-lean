import A12Kernel.Elaboration.TemporalNumericExpression
import A12Kernel.Elaboration.GeneratedComputationValidation

namespace A12Kernel.Conformance.TemporalNumericExpression

private def model : FlatModel := {
  timeZoneId := "Europe/Berlin"
  fields := [
    { id := 0, groupPath := ["Form"], name := "Stamp",
      policy := { kind := .temporal .dateTime TemporalComponents.now },
      temporalTargetPolicy := some { format := "yyyy-MM-dd'T'HH:mm:ss" } }] }

private def stamp : SurfaceScalarTemporalExpression :=
  .field { base := .absolute, groups := ["Form"], field := "Stamp" }

private def extract (phase : Phase) (source : SurfaceScalarTemporalExpression)
    (part : TimeNumericPart) (cell : CheckedCell := checkAdmittedRawCell .presentEmpty) := do
  let checked ← (elaborateTemporalNumericExpression model ["Form"] source (.time part)).toOption
  let result ← (checked.evalResult phase {
    read := fun _ => cell, world := some { now := { epochMillis := 1704112496000 } } }).toOption
  pure (match result with | .ok value => Sum.inr value | .error cause => Sum.inl cause)

example : [.hour, .minute, .second].map (extract .validation .now ·) =
    [some (.inr (.value 13 .fixed)), some (.inr (.value 34 .fixed)), some (.inr (.value 56 .fixed))] := by
  native_decide

example : [.validation, .computation].all (fun phase =>
    extract phase (.subdayShift .seconds .now (.literal { value := 61, authoredScale := 0 })) .second ==
      some (.inr (.value 57 .fixed)) &&
    extract phase (.timeFromDateTime (.subdayShift .minutes .now (.literal { value := 30, authoredScale := 0 }))) .hour ==
      some (.inr (.value 14 .fixed))) = true := by native_decide

example : [.validation, .computation].all (fun phase =>
    extract phase stamp .hour == some (.inr (.value 0 .both)) &&
    extract phase (.timeFromDateTime stamp) .minute == some (.inr (.value 0 .both)) &&
    extract phase stamp .hour (checkAdmittedRawCell (.rejected .malformed)) ==
      some (.inl (.formal .malformed))) = true := by native_decide

example : (elaborateTemporalNumericExpression model ["Form"]
    (.timeLiteral { hour := 1, minute := 2, second := 3, valid := by decide }) (.time .hour)).isOk = false ∧
    (elaborateTemporalNumericExpression model ["Form"] .today (.time .hour)).isOk = false ∧
    (elaborateTemporalNumericExpression model ["Form"] (.group .now) (.time .hour)).isOk = false := by
  native_decide

private def generated (source : SurfaceScalarTemporalExpression) (target : Rat)
    (cell : RawCell := .empty) : Option (Option Polarity) := do
  let model := { model with fields := model.fields ++ [{
    id := 1, groupPath := ["Form"], name := "Target",
    policy := { kind := .number { scale := 0, signed := true } } }] }
  let numeric : SurfaceNumericComputationAtom :=
    .temporalExpression (.projection (.time .hour) (.timeConstruction (.hour (.inr (.hour, source)))))
  let operation ← (elaborateCompleteNumericComputationOperation model ["Form"] 1 (.atom numeric)).toOption
  let rule ← (assembleGeneratedNumericOperationRule model operation "GeneratedClock" none
    { parts := [.text "Clock mismatch"] }).toOption
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 1704112496000 } }
    builtinStringPatternCompiler model).toOption
  let result ← (rule.evalFull prepared "en_US" {
    read := fun field => if field == 1 then .parsed (.num target) else cell }
    GroupPresenceContext.unavailable true).toOption
  pure (match result with
    | .fired message => some message.messageType
    | .notFired | .unknown => none)

example : generated .now 13 = some none ∧
    generated .now 12 = some (some .value) ∧
    generated (.timeFromDateTime stamp) 1 = some (some .omission) ∧
    generated (.timeFromDateTime stamp) 1 (.rejected .malformed) = some none := by
  native_decide

private def differenceStops (phase : Phase) (unit : TemporalOperationUnit)
    (source : SurfaceScalarTemporalExpression) (cell : CheckedCell) : Bool :=
  let project (source : SurfaceScalarTemporalExpression) :=
    if unit == .months || unit == .years then .dateFromDateTime source else source
  match elaborateTemporalNumericOperation model ["Form"] (.difference unit (project source)
      (project (.dateTimeLiteral ((LocalDateTime.ofYmdHms? 2024 3 31 2 30 0).get (by decide))))) with
  | .error _ => false
  | .ok checked =>
      match checked.evalResult phase { read := fun _ => cell } with
      | .ok (.error (.formal .malformed)) => phase == .computation
      | .error .dateTimeLabelUnresolved => phase == .validation
      | _ => false

example : [TemporalOperationUnit.days, .months, .years, .hours, .minutes, .seconds].all (fun unit =>
    [Phase.validation, .computation].all fun phase =>
      differenceStops phase unit stamp (checkAdmittedRawCell (.rejected .malformed)) &&
      differenceStops phase unit (.subdayShift .seconds stamp (.literal { value := 1, authoredScale := 0 }))
        (checkAdmittedRawCell (.rejected .malformed))) = true := by native_decide

end A12Kernel.Conformance.TemporalNumericExpression
