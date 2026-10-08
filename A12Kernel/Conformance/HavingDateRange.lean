import A12Kernel.Elaboration.HavingDateRange

namespace A12Kernel.Conformance.HavingDateRange

private def empty : CheckedCell := { rawPresent := false, parsed := none, findings := [] }
private def bad : CheckedCell := { rawPresent := true, parsed := none, findings := [.malformed] }
private def range (start finish : Nat) : CheckedCell := {
  rawPresent := true, parsed := some (.dateRange (.yearlessMonth start finish)), findings := [] }

private def context (cells : List (FieldId × CheckedCell)) : ResolvingCorrelationContext String := {
  read := fun _ field => match cells.lookup field with
    | some cell => .ok cell
    | none => .error "unread field reached"
  bindingError := fun _ => "binding"
  stringExpressionUnavailable := "String expression unavailable"
  unsupportedDateCalendar := "calendar"
  temporalValueFailure := "value"
  worldUnavailable := "world"
  typeValidityValueFailure := "type"
  groupUnavailable := fun _ => "unread extent reached"
  storedTextUnavailable := fun _ => "stored text" }

private def ref (field : FieldId) : HavingPresenceRef := { origin := .inner, field }
private def frame : CorrelationFrame := { innerEnv := [], outerEnv := [] }
private def direct (field : FieldId) := HavingFieldListSlot.direct (ref field)

private def result (scalar : Option HavingPresenceRef) (slots : List (HavingFieldListSlot HavingPresenceRef))
    (phase : Phase) (context : ResolvingCorrelationContext String) : String ⊕ ComputationConditionResult :=
  match HavingDateRangePredicate.evalOverlap scalar slots phase context frame with
  | .ok value => .inr value
  | .error error => .inl error

example : result (some (ref 1)) [direct 2]
    .computation (context [(1, empty)]) = .inr .notTrue ∧
    result none [direct 1, direct 2]
      .computation (context [(1, empty)]) = .inl "unread field reached" := by native_decide

example : result none [direct 1, direct 2, direct 3]
    .computation (context [(1, range 1 3), (2, range 3 4)]) = .inr .holds ∧
    result none [direct 3, direct 1, direct 2]
      .computation (context [(1, range 1 3), (2, range 3 4)]) = .inl "unread field reached" := by native_decide

example : result (some (ref 1)) [direct 2, direct 3]
    .computation (context [(1, range 8 9), (2, range 1 3), (3, range 2 4)]) = .inr .notTrue ∧
    result none [direct 1, direct 2, direct 3]
      .computation (context [(1, range 8 9), (2, range 1 3), (3, range 2 4)]) = .inr .holds := by native_decide

example : result none [direct 1, direct 2, direct 3]
    .validation (context [(1, bad), (2, range 1 3), (3, range 2 4)]) = .inr .holds ∧
    result none [direct 1, direct 2, direct 3]
      .computation (context [(1, bad), (2, range 1 3), (3, range 2 4)]) = .inr (.poison .malformed) := by native_decide

private def group : HavingFieldListSlot HavingPresenceRef :=
  .extent (.group { path := ["Form", "Ranges"], origin := .path }) [ref 3, ref 4]
private def emptyExtentContext : ResolvingCorrelationContext String := {
  context [(1, range 1 3), (2, range 3 4)] with groups := some {
    validation := fun _ _ => .error "unused validation group"
    computation := fun _ _ => .error "unused computation group"
    fieldExtent := fun _ _ _ _ => .ok ([], true) } }

example : [Phase.validation, .computation].all (fun phase =>
    result (some (ref 1)) [group] phase emptyExtentContext == .inr .notTrue &&
    result none [direct 1, group, direct 2] phase emptyExtentContext == .inr .holds &&
    result (some (ref 1)) [group] phase (context [(1, empty)]) == .inr .notTrue) = true := by native_decide

private def model : FlatModel := {
  fields := [
    { id := 1, name := "Start", groupPath := ["Form"], policy := { kind := .temporal .date .fullDate },
      temporalTargetPolicy := some { format := "yyyy-MM-dd" } },
    { id := 2, name := "Finish", groupPath := ["Form"], policy := { kind := .temporal .date .fullDate },
      temporalTargetPolicy := some { format := "yyyy-MM-dd" } },
    { id := 3, name := "Range", groupPath := ["Form"], policy := { kind := .dateRange },
      dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" } }] }
private def endpoint (field : FieldId) : HavingDateRangeEndpoint := {
  reference := ref field, format := .full .yearMonthDayDashes, profile := .utc }
private def compare (start finish : HavingDateRangeEndpoint) : HavingDateRangePredicate :=
  .compare .equal (.constructed start finish) (.stored (ref 3))

example : (compare (endpoint 1) (endpoint 2)).wellFormedForEnvironments model [] [] = true ∧
    (compare { endpoint 1 with format := .yearlessMonthDay } (endpoint 2)).wellFormedForEnvironments model [] [] = false ∧
    (compare { endpoint 1 with profile := .europeBerlin } (endpoint 2)).wellFormedForEnvironments model [] [] = false ∧
    (HavingDateRangePredicate.overlap none [direct 3, direct 3]).wellFormedForEnvironments model [] [] = false ∧
    (HavingDateRangePredicate.overlap none [direct 1, direct 3]).wellFormedForEnvironments model [] [] = false := by native_decide

private def mixedSpellingModel : FlatModel := { model with fields := model.fields ++ [
  { id := 4, name := "A", groupPath := ["Form", "Ranges"], policy := { kind := .dateRange },
    dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" } },
  { id := 5, name := "B", groupPath := ["Form", "Ranges"], policy := { kind := .dateRange },
    dateRangePolicy := some { format := "dd.MM.yyyy", separator := "-" } }] }
private def mixedGroup : HavingFieldListSlot HavingPresenceRef :=
  .extent (.group { path := ["Form", "Ranges"], origin := .path }) [ref 4, ref 5]

example : (HavingDateRangePredicate.overlap (some (ref 3)) [mixedGroup]).wellFormedForEnvironments
    mixedSpellingModel [] [] = false ∧
    (HavingDateRangePredicate.overlap (some (ref 3)) [direct 4, direct 5]).wellFormedForEnvironments
      mixedSpellingModel [] [] = true ∧
    (HavingDateRangePredicate.overlap (some (ref 3)) [mixedGroup]).wellFormedForEnvironments
      { mixedSpellingModel with baseYear := some 2024 } [] [] = true := by native_decide

end A12Kernel.Conformance.HavingDateRange
