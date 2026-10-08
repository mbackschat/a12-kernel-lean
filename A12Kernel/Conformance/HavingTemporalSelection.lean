import A12Kernel.Elaboration.Correlation

namespace A12Kernel.Conformance.HavingTemporalSelection
open A12Kernel

private def time : TimeOfDay := { hour := 12, minute := 30, second := 0, valid := by decide }
private def filled : CheckedCell := { rawPresent := true, parsed := some (.temporal (.time { epochMillis := 45000000 } time)), findings := [] }
private def empty : CheckedCell := { rawPresent := false, parsed := none, findings := [] }
private def malformed : CheckedCell := { empty with rawPresent := true, findings := [.malformed] }
private def reference (id : FieldId) (origin : HavingOrigin := .inner) : HavingTemporalSelectionRef := {
  origin, field := { id, kind := .time, components := TemporalComponents.time } }
private def slots : List (HavingFieldListSlot HavingTemporalSelectionRef) := [
  .direct (reference 1), .direct (reference 2 .outer)]
private def frame : CorrelationFrame := { innerEnv := [(10, 1)], outerEnv := [(10, 2)] }
private def context (first : CheckedCell) : ResolvingCorrelationContext CorrelationRuntimeFault := {
  ({ read := fun _ _ => empty } : CorrelationContext).asResolving with
  read := fun environment field => if field == 1 && environment == frame.innerEnv then pure first
    else .error .valueFailure }
private def run (kind : HavingTemporalSelection) (phase : Phase)
    (context : ResolvingCorrelationContext CorrelationRuntimeFault)
    (operands : List (HavingFieldListSlot HavingTemporalSelectionRef) := slots) :
    Sum CorrelationRuntimeFault (SimpleComparisonOperand ScalarTemporalValue) :=
  match kind.evaluate none .utc phase context frame operands with
  | .ok value => .inr value
  | .error error => .inl error

example : [Phase.validation, .computation].all (fun phase =>
    run .firstFilled phase (context filled) == .inr (.value (.time time) true) &&
    run .firstFilled phase (context malformed) == .inr (.unknown .malformed) &&
    run .firstFilled phase (context empty) == .inl .valueFailure &&
    run (.extremum .minimum) phase (context filled) == .inl .valueFailure) = true ∧
    run (.extremum .maximum) .validation (context malformed) = .inl .valueFailure ∧
    run (.extremum .maximum) .computation (context malformed) = .inr (.unknown .malformed) := by native_decide

private def extent : HavingEntityExtent := .starField ["Form", "Rows"] {
  axes := [{ level := 10, repeatability := some 3 }], firstStar := 0 }
private def extentContext : ResolvingCorrelationContext CorrelationRuntimeFault := { context filled with
  groups := some {
    validation := fun _ _ => .error .valueFailure
    computation := fun _ _ => .error .valueFailure
    fieldExtent := fun _ env _ field => if field == 1 then pure ([env, frame.outerEnv], true)
      else .error .valueFailure } }
example : run .firstFilled .validation extentContext [.extent extent [reference 1, reference 2]] =
      .inr (.value (.time time) true) ∧
    run (.extremum .maximum) .computation extentContext [.extent extent [reference 1, reference 2]] =
      .inl .valueFailure := by native_decide

private def omitted : ResolvingCorrelationContext CorrelationRuntimeFault := { extentContext with
  read := fun _ _ => pure filled
  groups := some {
    validation := fun _ _ => .error .valueFailure
    computation := fun _ _ => .error .valueFailure
    fieldExtent := fun _ env _ _ => pure ([env], true) } }
example : run .firstFilled .validation omitted [.extent extent [reference 1]] =
      .inr (.value (.time time) true) ∧
    run (.extremum .minimum) .validation omitted [.extent extent [reference 1]] =
      .inr (.value (.time time) false) := by native_decide

private def model : FlatModel := {
  fields := [
    { id := 1, groupPath := ["Form", "Rows"], name := "Time", repeatableScope := [10]
      policy := { kind := .temporal .time TemporalComponents.time }
      temporalTargetPolicy := some { format := "HH:mm:ss" } },
    { id := 2, groupPath := ["Form"], name := "Expected"
      policy := { kind := .temporal .time TemporalComponents.time }
      temporalTargetPolicy := some { format := "HH:mm:ss" } }]
  repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 3 }] }
private def expression (operands : List (HavingFieldListSlot HavingTemporalSelectionRef)) : HavingTemporalExpression := {
  core := .atom (.selection .firstFilled operands), profile := .utc, baseYear := none }
private def forgedExtent : HavingEntityExtent := .starField ["Form", "Rows"] {
  axes := [{ level := 10, repeatability := some 4 }], firstStar := 0 }
example : (expression slots).wellFormed model [10] [] = true ∧
    (expression slots).wellFormed model [] [] = false ∧
    (expression [.extent extent [reference 1], .direct (reference 2 .outer)]).wellFormed model [] [] = true ∧
    (expression [.extent forgedExtent [reference 1], .direct (reference 2 .outer)]).wellFormed model [] [] = false ∧
    (expression [.extent extent [reference 1, reference 2]]).wellFormed model [] [] = false := by native_decide

private def partialReference : HavingTemporalSelectionRef := {
  origin := .inner
  field := { id := 1, kind := .date, components := TemporalComponents.fullDate }
  partialFormat := some .yearMonthDayDashes }
private def partialCell (text : String) : CheckedCell := {
  rawPresent := true, parsed := some (.partialDate text), findings := [] }
private def partialModel : FlatModel := {
  fields := [
    { id := 1, name := "Candidate", groupPath := ["Form"]
      policy := { kind := .temporal .date TemporalComponents.fullDate }
      temporalTargetPolicy := some { format := "yyyy-MM-dd", partialMode := .yearOptional } },
    { id := 2, name := "Fallback", groupPath := ["Form"]
      policy := { kind := .temporal .date TemporalComponents.fullDate }
      temporalTargetPolicy := some { format := "yyyy-MM-dd" } }] }
private def partialSlots : List (HavingFieldListSlot HavingTemporalSelectionRef) := [
  .direct partialReference, .direct { partialReference with field := { partialReference.field with id := 2 }, partialFormat := none }]
example : HavingTemporalSelection.firstFilled.wellFormed partialModel [] [] partialSlots = true ∧
    (HavingTemporalSelection.extremum .minimum).wellFormed partialModel [] [] partialSlots = false ∧
    HavingTemporalSelection.firstFilled.wellFormed partialModel [] []
      [.direct { partialReference with partialFormat := none }, .direct { partialReference with field := { partialReference.field with id := 2 }, partialFormat := none }] = false ∧
    HavingTemporalSelection.firstFilled.wellFormed partialModel [] []
      [.direct { partialReference with partialFormat := some .dayMonthYearDots }, .direct { partialReference with field := { partialReference.field with id := 2 }, partialFormat := none }] = false := by native_decide
example : [Phase.validation, .computation].all (fun phase =>
    run .firstFilled phase (context (partialCell "0000-00-00")) partialSlots ==
      .inr (.value .nonRelevant true) &&
    (match run .firstFilled phase (context (partialCell "2024-06-00")) partialSlots with
      | .inr (.value (.date value) true) => value.parts == { year := 2024, month := 6, day := 1 }
      | _ => false)) = true := by native_decide

private def selectedStamp : HavingTemporalExpression := {
  core := .apply (.constructor .dateTime) (.atom .today) [.atom (.selection .firstFilled slots)]
  profile := .utc, baseYear := none }
private def surfaceSelection : SurfaceHavingTemporalExpression := .selection .firstFilled {
  first := .group .inner (.ruleGroup false), rest := [] }
private def admitted (source : SurfaceHavingTemporalExpression) : Bool :=
  (HavingTemporalExpression.elaborate model (fun _ => .error .numericExpressionUnsupported) source
    (fun _ _ => pure slots)).isOk
example : selectedStamp.components? = none ∧
    selectedStamp.wellFormed model [10] [] = false ∧
    admitted (.dateTime .today surfaceSelection) = false ∧
    admitted (.dateTime .today (.grouped (.timeLiteral time))) = false ∧
    admitted (.dateTime .today (.timeLiteral time)) = true := by native_decide

private def numericSelection : CorrelatedHavingLeaf := .numeric {
  op := .ordinary .equal
  left := .atom (.temporalExpressionPart (.time .hour) (expression slots))
  right := .atom (.temporalExpressionPart (.time .hour) (expression slots)) }
example : numericSelection.wellFormedForEnvironments model [10] [] = false := by native_decide

private def checkedNumericSelection : Except CorrelationElabError CorrelatedHaving := do
  let star ← (elaborateStarFieldPath model ["Form"] {
    base := .absolute, groups := [{ name := "Form" }, { name := "Rows", starred := true }]
    field := "Time" }).mapError fun _ => .incoherentCore
  let source : SurfaceHavingTemporalExpression := .selection .firstFilled {
    first := .entity { origin := .inner, field := { base := .absolute, groups := ["Form", "Rows"], field := "Time" } }
    rest := [.entity { origin := .outer, field := { base := .absolute, groups := ["Form"], field := "Expected" } }] }
  pure (← elaborateStarHavingCore model ["Form"] star (.numeric .equal
    (.atom (.temporalExpressionPart (.time .hour) source))
    (.atom (.temporalExpressionPart (.time .hour) source)))).condition
example : checkedNumericSelection.isOk = false := by native_decide

end A12Kernel.Conformance.HavingTemporalSelection
