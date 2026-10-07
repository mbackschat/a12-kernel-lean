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
    (environments : Env → Nat → FieldId → Except CorrelationRuntimeFault (List Env))
    (tail : Bool := false) :
    ResolvingCorrelationContext CorrelationRuntimeFault :=
  { base with read, groups := some {
      validation := fun _ source => .error (.groupUnavailable source.path)
      computation := fun _ source => .error (.groupUnavailable source.reference.path)
      fieldExtent := fun _ env depth field => (fun rows => (rows, tail)) <$> environments env depth field } }
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
private def mixedContext (tail : Bool := false) : ResolvingCorrelationContext CorrelationRuntimeFault :=
  context (fun env field => pure (number (if field == 2 || env == rows[1]! then 7 else 5)))
    (fun _ depth _ => if depth == 0 then pure rows else .error .valueFailure) tail

example : [Phase.validation, .computation].all (fun phase => decide (
    result mixed phase mixedContext = .inr .holds ∧
    result (.number [.extent extent [ref 1]]) phase mixedContext = .inr .notTrue)) = true := by
  native_decide

example : [Phase.validation, .computation].all (fun phase => decide (
    result mixed phase (mixedContext true) = .inr .holds ∧
    result (.number [.extent extent [ref 1]]) phase (mixedContext true) = .inr .notTrue)) = true := by
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
  let (environments, _) ← (groups.fieldExtent extent.groupPath [] 0 1).toOption
  let (bound, _) ← (groups.fieldExtent groupExtent.groupPath [(10, 2)] 1 1).toOption
  let value ← (mixed.evalRead .computation checked.resolvingCorrelationContext frame).toOption
  pure (value, environments, bound)

example : checkedResult?.any (fun (value, environments, bound) => decide (
    value = .holds ∧ environments = rows ∧ bound = [frame.outerEnv])) = true := by
  native_decide

private abbrev StreamTrace := List (FieldId × Env)
private def streamSlots : List (HavingFieldListSlot HavingNumberRef) := [
  .extent extent [ref 1, ref 2], .direct (ref 3)]
private def streamContext (tail : Bool := true) (failLater : Bool := false) :
    ResolvingCorrelationContext CorrelationRuntimeFault :=
  { base with
    read := fun _ field => if failLater && field != 1 then .error (.storedTextUnavailable field)
      else pure (number 5)
    groups := some {
      validation := fun _ source => .error (.groupUnavailable source.path)
      computation := fun _ source => .error (.groupUnavailable source.reference.path)
      fieldExtent := fun _ _ _ field =>
        if failLater && field != 1 then .error (.storedTextUnavailable field)
        else pure (rows, tail) } }
private def streamResult (context : ResolvingCorrelationContext CorrelationRuntimeFault)
    (slots : List (HavingFieldListSlot HavingNumberRef))
    (onOmitted : StreamTrace → Except CorrelationRuntimeFault (Sum StreamTrace StreamTrace))
    (decideAtRow : Bool := false) :
    Sum CorrelationRuntimeFault (Sum StreamTrace StreamTrace) :=
  match HavingFieldListSlot.foldRead (·.origin) (·.field.id) context frame
      (fun trace reference environment => do
        let _ ← context.read environment reference.field.id
        let next := trace ++ [(reference.field.id, environment)]
        pure (if decideAtRow then .inr next else .inl next)) [] slots onOmitted with
  | .ok trace => .inr trace
  | .error error => .inl error

example : (streamResult streamContext streamSlots (fun trace => pure (.inl (trace ++ [(0, [])]))) ==
    .inr (.inl [(1, rows[0]!), (1, rows[1]!), (0, []),
      (2, rows[0]!), (2, rows[1]!), (0, []), (3, frame.innerEnv)])) = true := by
  native_decide

example : [streamSlots,
    [.extent extent [ref 1], .direct (ref 3)],
    [.extent extent [ref 1], .extent groupExtent [ref 3]]].all (fun slots =>
      streamResult (streamContext (failLater := true)) slots
        (fun trace => pure (.inr (trace ++ [(0, [])]))) ==
      .inr (.inr [(1, rows[0]!), (1, rows[1]!), (0, [])])) = true := by
  native_decide

example : (streamResult (streamContext (failLater := true)) streamSlots
      (fun _ => .error .valueFailure) true == .inr (.inr [(1, rows[0]!)])) = true ∧
    (streamResult (streamContext false) streamSlots (fun _ => .error .valueFailure) ==
      .inr (.inl [(1, rows[0]!), (1, rows[1]!), (2, rows[0]!), (2, rows[1]!), (3, frame.innerEnv)])) = true := by
  native_decide

private def pureStreamContext : CorrelationContext := {
  read := fun _ _ => number 5
  groups := streamContext.groups }

example : [
    (streamContext (failLater := true)).withComputationGroups noRows,
    (pureStreamContext.withComputationGroups noRows).asResolving].all (fun context =>
      streamResult context streamSlots (fun trace => pure (.inr (trace ++ [(0, [])]))) ==
        .inr (.inr [(1, rows[0]!), (1, rows[1]!), (0, [])])) = true ∧
    [base, base.withComputationGroups noRows,
      (({ read := fun _ _ => number 5 } : CorrelationContext).withComputationGroups noRows).asResolving].all
      (fun context => streamResult context streamSlots (fun trace => pure (.inr trace)) ==
        .inl (.groupUnavailable extent.groupPath)) = true := by
  native_decide

private def modelExtents? : Option (List (List Env × Bool)) := do
  let document : Document := { noRows with instantiatedRows := [{ group := 10, path := [1] }] }
  let resolving := base.withModelComputationGroups checkedModel document
  let pureContext := ({ read := fun _ _ => number 5 } : CorrelationContext).withModelComputationGroups checkedModel document
  let resolvingGroups ← resolving.groups
  let pureGroups ← pureContext.groups
  ([resolvingGroups.fieldExtent extent.groupPath [] 0 1,
    pureGroups.fieldExtent extent.groupPath [] 0 1,
    resolvingGroups.fieldExtent [] [] 0 2,
    pureGroups.fieldExtent [] [] 0 2]).mapM Except.toOption

example : modelExtents? = some [([rows[0]!], true), ([rows[0]!], true), ([[]], false), ([[]], false)] := by
  native_decide

private def nestedModel : FlatModel := {
  fields := [
    { id := 1, groupPath := ["Form", "Rows", "Lines"], name := "N", repeatableScope := [10, 20],
      policy := { kind := .number { scale := 0, signed := true } } }]
  repeatableGroups := [
    { level := 10, path := ["Form", "Rows"], repeatability := some 2 },
    { level := 20, path := ["Form", "Rows", "Lines"], repeatability := some 2 }] }
private def nestedExtents? : Option (List (List Env × Bool)) := do
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler nestedModel).toOption
  let checked ← (checkDocument prepared "en_US" {
    instantiatedRows := [{ group := 10, path := [3] }, { group := 10, path := [2] },
      { group := 10, path := [1] }, { group := 20, path := [2, 1] },
      { group := 20, path := [1, 3] }, { group := 20, path := [1, 2] }, { group := 20, path := [1, 1] }]
    cells := [] }).toOption
  let empty ← (checkDocument prepared "en_US" { instantiatedRows := [], cells := [] }).toOption
  let groups := checked.correlationGroupsWithRead (fun _ => .error (.incoherentRepeatableScope []))
  let emptyGroups := empty.correlationGroupsWithRead (fun _ => .error (.incoherentRepeatableScope []))
  let path := ["Form", "Rows", "Lines"]
  ([groups.fieldExtent path [] 0 1,
    groups.fieldExtent path [(10, 1), (20, 2)] 2 1,
    groups.fieldExtent path [(10, 2), (20, 2)] 2 1,
    groups.fieldExtent path [(10, 1), (20, 3)] 2 1,
    emptyGroups.fieldExtent path [] 0 1,
    emptyGroups.fieldExtent path [(10, 1), (20, 1)] 2 1,
    emptyGroups.fieldExtent path [(10, 3)] 1 1,
    emptyGroups.fieldExtent path [(10, 3), (20, 1)] 2 1]).mapM Except.toOption

example : nestedExtents? = some [
    ([[(10, 1), (20, 1)], [(10, 1), (20, 2)], [(10, 2), (20, 1)]], true),
    ([[(10, 1), (20, 2)]], false), ([], true), ([], false), ([], true), ([], true), ([], false), ([], false)] := by
  native_decide

end A12Kernel.Conformance.HavingUniquenessExtent
