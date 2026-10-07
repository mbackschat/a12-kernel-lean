import A12Kernel.Elaboration.CheckedStarDocument

namespace A12Kernel.Conformance.HavingUniquenessExtent
open A12Kernel

private def frame : CorrelationFrame := { innerEnv := [(10, 1)], outerEnv := [(10, 2)] }
private def number (value : Rat) : CheckedCell := { rawPresent := true, parsed := some (.num value), findings := [] }
private def invalid : CheckedCell := { rawPresent := true, parsed := none, findings := [.malformed] }
private def ref (field : FieldId) (origin : HavingOrigin := .inner) : HavingNumberRef :=
  { origin, field := { id := field, info := { scale := 0, signed := true } } }
private def extent : HavingEntityExtent := .starredGroup ["Form", "Rows"] {
  axes := [{ level := 10, repeatability := some 3 }], firstStar := 0 }
private def groupExtent : HavingEntityExtent := .group {
  path := ["Form", "Rows"], origin := .path, boundRepeatableScope := [10] }
private def base : ResolvingCorrelationContext CorrelationRuntimeFault :=
  ({ read := fun _ _ => number 5 } : CorrelationContext).asResolving
private def context (read : Env → FieldId → Except CorrelationRuntimeFault CheckedCell)
    (environments : Env → Nat → FieldId → Except CorrelationRuntimeFault (List Env)) :
    ResolvingCorrelationContext CorrelationRuntimeFault :=
  { base with read, groups := some {
      validation := fun _ source => .error (.groupUnavailable source.path)
      computation := fun _ source => .error (.groupUnavailable source.reference.path)
      fieldEnvironments := fun _ => environments } }
private def result (source : A12Kernel.HavingUniqueness) (phase : Phase)
    (context : ResolvingCorrelationContext CorrelationRuntimeFault) :
    Sum CorrelationRuntimeFault ComputationConditionResult :=
  match source.evalRead phase context frame with
  | .ok value => .inr value
  | .error error => .inl error

private def mixed : A12Kernel.HavingUniqueness := .number [
  .extent extent [ref 1], .direct (ref 2)]
private def rows : List Env := [[(10, 1)], [(10, 2)]]
private def noRows : Document := { instantiatedRows := [], rawCells := fun _ => none }
private def mixedContext : ResolvingCorrelationContext CorrelationRuntimeFault :=
  context (fun env field => pure (number (if field == 2 || env == rows[1]! then 7 else 5)))
    (fun _ depth _ => if depth == 0 then pure rows else .error .valueFailure)

example : [Phase.validation, .computation].all (fun phase => decide (
    result mixed phase mixedContext = .inr .holds ∧
    result (.number [.extent extent [ref 1]]) phase mixedContext = .inr .notTrue)) = true := by
  native_decide

private def deciding : A12Kernel.HavingUniqueness := .number [
  .extent extent [ref 1, ref 2], .extent groupExtent [ref 3]]
private def decidingContext (duplicate : Bool) : ResolvingCorrelationContext CorrelationRuntimeFault :=
  context (fun env field => if field != 1 then .error (.storedTextUnavailable field)
      else pure (number (if duplicate || env == rows[0]! then 5 else 7)))
    (fun _ _ field => if field == 1 then pure rows else .error (.storedTextUnavailable field))

example : result deciding .computation (decidingContext true) = .inr .holds ∧
    result deciding .computation (decidingContext false) = .inl (.storedTextUnavailable 2) ∧
    result (.number [.extent extent [ref 1], .extent groupExtent [ref 3]])
      .computation (decidingContext false) = .inl (.storedTextUnavailable 3) ∧
    result (.number [.extent extent [ref 1], .extent groupExtent [ref 3]])
      .computation (decidingContext true) = .inr .holds := by native_decide

private def phaseContext : ResolvingCorrelationContext CorrelationRuntimeFault :=
  context (fun env field => pure (if field == 1 && env == rows[0]! then invalid else number 5))
    (fun _ _ _ => pure rows)

example : result mixed .validation phaseContext = .inr .holds ∧
    result mixed .computation phaseContext = .inr (.poison .malformed) ∧
    result mixed .validation base = .inl (.groupUnavailable ["Form", "Rows"]) := by native_decide

example : result mixed .computation (context (fun _ _ => pure invalid)
      (fun _ _ field => if field == 1 then pure rows else .error (.storedTextUnavailable field))) =
      .inr (.poison .malformed) ∧
    result mixed .computation (phaseContext.withComputationGroups noRows) = .inr (.poison .malformed) ∧
    result mixed .validation (base.withComputationGroups noRows) =
      .inl (.groupUnavailable ["Form", "Rows"]) := by native_decide

private def originSource (origin : HavingOrigin) : A12Kernel.HavingUniqueness := .number [
  .extent groupExtent [ref 1 origin], .direct (ref 2)]
private def originContext : ResolvingCorrelationContext CorrelationRuntimeFault :=
  context (fun env field => pure (number (if field == 2 || env == frame.outerEnv then 5 else 7)))
    (fun env depth _ => if depth == 1 then pure [env] else .error .valueFailure)

example : result (originSource .inner) .computation originContext = .inr .notTrue ∧
    result (originSource .outer) .computation originContext = .inr .holds ∧
    (originSource .outer).references = [{ origin := .outer, field := 1 }, { origin := .inner, field := 2 }] := by
  native_decide

private def temporalRef (field : FieldId) : HavingTemporalRef :=
  { origin := .inner, field := { id := field, kind := .date, components := .fullDate } }
private def temporalSource : A12Kernel.HavingUniqueness := .temporal [
  .extent extent [temporalRef 1], .direct (temporalRef 2)]
private def temporalContext (duplicate : Bool) : ResolvingCorrelationContext CorrelationRuntimeFault :=
  { (context (fun _ _ => pure { rawPresent := true, findings := [], parsed := some (.temporal (.date {
      instant := { epochMillis := 0 }, parts := { year := 1970, month := 1, day := 1 }, basis := .storedGregorian })) })
      (fun _ _ _ => pure rows)) with
    storedText := fun env field => if field == 2 then none
      else some (if duplicate || env == rows[0]! then "spelling A" else "spelling B") }

-- Synthetic spellings isolate exact storage identity; no Kernel ingress claim follows.
example : [Phase.validation, .computation].all (fun phase => decide (
    result temporalSource phase (temporalContext true) = .inr .holds ∧
    result temporalSource phase (temporalContext false) = .inl (.storedTextUnavailable 2))) = true := by
  native_decide

private def checkedModel : FlatModel := {
  fields := [
    { id := 1, groupPath := ["Form", "Rows"], name := "N", repeatableScope := [10],
      policy := { kind := .number { scale := 0, signed := true } } },
    { id := 2, groupPath := ["Form"], name := "Outside", policy := { kind := .number { scale := 0, signed := true } } }]
  repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 2 }] }
private def checkedResult? : Option (ComputationConditionResult × List Env × List Env) := do
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler checkedModel).toOption
  let checked ← (checkDocument prepared "en_US" {
    instantiatedRows := [3, 2, 1].map fun row => { group := 10, path := [row] }
    cells := [
      { address := { field := 1, path := [1] }, stored := "5", raw := .parsed (.num 5) },
      { address := { field := 1, path := [2] }, stored := "7", raw := .parsed (.num 7) },
      { address := { field := 1, path := [3] }, stored := "5", raw := .parsed (.num 5) },
      { address := { field := 2, path := [] }, stored := "7", raw := .parsed (.num 7) }] }).toOption
  let groups := checkedModel.correlationGroupsWithRead checked.source.toDocument
    (fun _ field => .error (.field field (.unknownFieldId field)))
  let environments ← (groups.fieldEnvironments extent.groupPath [] 0 1).toOption
  let bound ← (groups.fieldEnvironments groupExtent.groupPath [(10, 2)] 1 1).toOption
  let value ← (mixed.evalRead .computation checked.resolvingCorrelationContext frame).toOption
  pure (value, environments, bound)

example : checkedResult?.any (fun (value, environments, bound) => decide (
    value = .holds ∧ environments = rows ∧ bound = [frame.outerEnv])) = true := by
  native_decide

end A12Kernel.Conformance.HavingUniquenessExtent
