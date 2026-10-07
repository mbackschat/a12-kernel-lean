import A12Kernel.Semantics.Correlation

namespace A12Kernel.Conformance.HavingGroupPresence
open A12Kernel

local instance [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .ok a, .ok b => decidable_of_iff (a = b) (by simp)
  | .error a, .error b => decidable_of_iff (a = b) (by simp)
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

private def source : ComputationGroupOperand := {
  reference := { path := ["Form", "Info"], origin := .path }
  content := { scope := [10], fields := [1], rowLevels := [] }
  members := [1, 3] }

private def other : ComputationGroupOperand := {
  reference := { path := ["Form", "Other"], origin := .path }
  content := { scope := [10], fields := [2], rowLevels := [] }
  members := [2] }

private def frame : CorrelationFrame := { innerEnv := [(10, 1)], outerEnv := [(10, 2)] }
private def empty : CheckedCell := { rawPresent := false, parsed := none, findings := [] }
private def value : CheckedCell := { rawPresent := true, parsed := some (.num 3), findings := [] }
private def malformed : CheckedCell := { rawPresent := true, parsed := none, findings := [.malformed] }
private def dependency : CheckedCell := { rawPresent := true, parsed := none, findings := [.computedDependency] }

private def groupContext (cell : CheckedCell) (rows : Bool := false) (otherCell : CheckedCell := empty) : CorrelationContext := {
  read := fun _ field => if field == 1 then cell else otherCell
  groups := some {
    validation := fun _ reference => pure (({
      descendantCells := [if reference.path == source.reference.path then cell else otherCell]
      hasInstantiatedRow := rows, structuralError := false, relevance := .fullyRelevant } :
      ResolvedGroupPresenceInput).derive)
    computation := fun _ source => pure (
      source.content.fields.map (fun field => observeCell .computation (if field == 1 then cell else otherCell)), rows) } }

private def leaves : List CorrelatedHavingLeaf :=
  let first := HavingGroupOperand.group .inner { source with dependencyKind := .ordinaryList }
  let rest := [HavingGroupOperand.group .inner { other with dependencyKind := .ordinaryList }]
  [.groupPresence .filled .inner source, .groupPresence .notFilled .inner source] ++
    [GroupFillQuantifier.allGroupsFilled, .noGroupFilled, .atLeastOneGroupFilled,
      .notAllGroupsFilled, .groupsNotCollectivelyFilled].map (fun operator => .groupFill operator first rest)

example : [
    (value, value, [K.tru, .fls, .tru, .unknown, .tru, .unknown, .unknown],
      [ComputationConditionResult.holds, .notTrue, .holds, .notTrue, .holds, .notTrue, .notTrue]),
    (value, empty, [K.tru, .fls, .unknown, .unknown, .tru, .tru, .tru],
      [ComputationConditionResult.holds, .notTrue, .notTrue, .notTrue, .holds, .holds, .holds]),
    (empty, empty, [K.fls, .tru, .unknown, .tru, .unknown, .tru, .unknown],
      [ComputationConditionResult.notTrue, .holds, .notTrue, .holds, .notTrue, .holds, .notTrue]),
    (malformed, empty, [K.fls, .unknown, .unknown, .unknown, .unknown, .tru, .unknown],
      [ComputationConditionResult.holds, .notTrue, .notTrue, .notTrue, .holds, .holds, .holds]),
    (dependency, empty, [K.fls, .unknown, .unknown, .unknown, .unknown, .tru, .unknown],
      [ComputationConditionResult.notTrue, .holds, .notTrue, .holds, .notTrue, .holds, .notTrue])].all
    (fun (cell, otherCell, validation, computation) =>
      leaves.map (·.evalTruthIn (groupContext cell (otherCell := otherCell)) frame) == validation &&
      decide (leaves.mapM (·.evalComputationIn (groupContext cell (otherCell := otherCell)) frame) = .ok computation) &&
      decide (leaves.mapM (·.evalTruthInResolving (groupContext cell (otherCell := otherCell)).asResolving frame) = .ok validation) &&
      decide (leaves.mapM (·.evalComputationInResolving (groupContext cell (otherCell := otherCell)).asResolving frame) = .ok computation)) = true := by
  native_decide

example : (CorrelatedHavingLeaf.groupPresence .filled .inner source).evalTruthIn
      (groupContext empty true) frame = .tru ∧
    (CorrelatedHavingLeaf.groupPresence .notFilled .inner source).evalTruthIn
      (groupContext malformed true) frame = .fls ∧
    (CorrelatedHavingLeaf.groupPresence .filled .inner source).evalComputationIn
      (groupContext dependency true) frame = .ok .holds := by native_decide

private def originContext : CorrelationContext := {
  read := fun env _ => if env == frame.innerEnv then value else empty
  groups := some {
    validation := fun env _ => pure {
      content := env == frame.innerEnv
      erroneous := false
      relevance := .fullyRelevant }
    computation := fun env _ => pure ([observeCell .computation
      (if env == frame.innerEnv then value else empty)], false) } }

example : (CorrelatedHavingLeaf.groupPresence .filled .inner source).evalTruthIn originContext frame = .tru ∧
    (CorrelatedHavingLeaf.groupPresence .filled .outer source).evalTruthIn originContext frame = .fls ∧
    (CorrelatedHavingLeaf.groupPresence .filled .inner source).evalComputationIn originContext frame = .ok .holds ∧
    (CorrelatedHavingLeaf.groupPresence .filled .outer source).evalComputationIn originContext frame = .ok .notTrue ∧
    (CorrelatedHavingLeaf.groupFill .groupsNotCollectivelyFilled (.group .inner source)
      [.group .outer source]).evalTruthIn originContext frame = .tru ∧
    (CorrelatedHavingLeaf.groupFill .groupsNotCollectivelyFilled (.group .inner source)
      [.group .outer source]).evalComputationIn originContext frame = .ok .holds := by native_decide

private def unavailable : CorrelationContext := { read := fun _ _ => empty }
private def field (id : FieldId) : HavingGroupOperand := .field { origin := .inner, field := id }

example : leaves.all (fun leaf =>
    leaf.evalTruthIn unavailable frame == .unknown &&
    decide (leaf.evalComputationIn unavailable frame = .error (.groupUnavailable source.reference.path)) &&
    decide (leaf.evalTruthInResolving unavailable.asResolving frame = .error (.groupUnavailable source.reference.path))) = true := by
  native_decide

private def failing : ResolvingCorrelationContext String := {
  read := fun _ id => if id == 1 then .ok value else .error "field unavailable"
  bindingError := fun _ => "binding unavailable"
  unsupportedDateCalendar := "calendar unavailable"
  temporalValueFailure := "value failure"
  worldUnavailable := "world unavailable"
  storedTextUnavailable := fun _ => "stored text unavailable"
  typeValidityValueFailure := "type validity value failure"
  groupUnavailable := fun _ => "group unavailable"
  groups := some {
    validation := fun _ reference =>
      if reference.path == source.reference.path then
        .ok { content := true, erroneous := false, relevance := .fullyRelevant }
      else .error "group read unavailable"
    computation := fun _ source =>
      if source.content.fields == [1] then .ok ([.value (.num 3)], false)
      else .error "group read unavailable" } }

example : (CorrelatedHavingLeaf.groupFill .atLeastOneGroupFilled (.group .inner source)
      [field 2]).evalTruthInResolving failing frame = .error "field unavailable" ∧
    (CorrelatedHavingLeaf.groupFill .atLeastOneGroupFilled (.group .inner source)
      [.group .inner other]).evalTruthInResolving failing frame = .error "group read unavailable" ∧
    (CorrelatedHavingLeaf.groupFill .atLeastOneGroupFilled (.group .inner other)
      [field 2]).evalTruthInResolving failing frame = .error "group read unavailable" ∧
    (CorrelatedHavingLeaf.groupFill .atLeastOneGroupFilled (.group .inner source)
      [field 2]).evalComputationInResolving failing frame = .ok .holds ∧
    (CorrelatedHavingLeaf.groupFill .atLeastOneGroupFilled (field 2)
      [.group .inner source]).evalComputationInResolving failing frame = .error "field unavailable" := by
  native_decide

example : (CorrelatedHavingLeaf.groupFill .allGroupsFilled (field 2)
      [.group .inner source]).evalComputationIn unavailable frame = .ok .notTrue ∧
    (CorrelatedHavingLeaf.groupFill .noGroupFilled (field 2)
      [.group .inner source]).evalComputationIn unavailable frame = .error (.groupUnavailable source.reference.path) := by
  native_decide

private def mixed (operator : GroupFillQuantifier) (first second : HavingGroupOperand) : CorrelatedHavingLeaf :=
  .groupFill operator first [second]

example : [
    (GroupFillQuantifier.allGroupsFilled, HavingGroupOperand.group .inner other, ComputationConditionResult.notTrue),
    (.noGroupFilled, .group .inner source, .notTrue),
    (.atLeastOneGroupFilled, .group .inner source, .holds),
    (.notAllGroupsFilled, .group .inner other, .holds)].all (fun (operator, group, expected) =>
      decide ((mixed operator group (field 1)).evalComputationIn (groupContext malformed) frame = .ok expected) &&
      decide ((mixed operator (field 1) group).evalComputationIn (groupContext malformed) frame = .ok (.poison .malformed))) = true ∧
    (CorrelatedHavingLeaf.groupFill .groupsNotCollectivelyFilled (.group .inner source)
      [.group .inner other, field 1]).evalComputationIn (groupContext malformed) frame = .ok .holds ∧
    (CorrelatedHavingLeaf.groupFill .groupsNotCollectivelyFilled (field 1)
      [.group .inner source, .group .inner other]).evalComputationIn (groupContext malformed) frame = .ok (.poison .malformed) := by
  native_decide

private def conditional (operator : GroupPresenceOperator := .filled) : CorrelatedHaving :=
  .leaf (.groupPresence operator .outer source)
private def ordinary (operator : GroupFillQuantifier := .atLeastOneGroupFilled) : CorrelatedHaving :=
  .leaf (.groupFill operator (.group .outer { source with dependencyKind := .ordinaryList })
    [.field { origin := .inner, field := 2 }])

example : (conditional).fieldIds = [1, 3] ∧ (conditional).markedFieldIds = [1, 3] ∧
    (ordinary).fieldIds = [1, 3, 2] ∧ (ordinary).markedFieldIds = [1, 3] ∧
    (conditional).usesInner = false ∧ (conditional).usesOuter = true ∧
    (ordinary).usesInner = true ∧ (ordinary).usesOuter = true ∧
    (conditional).referencesField 1 = true ∧ (conditional).forbidsTarget 1 = false ∧
    (conditional .notFilled).forbidsTarget 1 = true ∧ (ordinary).forbidsTarget 1 = true ∧
    (conditional).requiresProducer 1 1 (fun _ => false) = false ∧
    (conditional).requiresProducer 1 3 (fun _ => true) = false ∧
    (conditional).requiresProducer 1 3 (fun _ => false) = true ∧
    (conditional).requiresProducer 2 3 (fun _ => true) = true ∧
    (conditional .notFilled).requiresProducer 1 1 (fun _ => true) = true ∧
    (ordinary).requiresProducer 1 1 (fun _ => true) = true ∧
    (ordinary).requiresProducer 1 3 (fun _ => true) = true := by native_decide

example : [GroupFillQuantifier.allGroupsFilled, .noGroupFilled, .atLeastOneGroupFilled,
    .notAllGroupsFilled, .groupsNotCollectivelyFilled].all (fun operator =>
      (ordinary operator).forbidsTarget 1 &&
      (ordinary operator).requiresProducer 1 1 (fun _ => true)) = true ∧
    CorrelatedHaving.forbidsTarget (.and conditional ordinary) 1 = true ∧
    CorrelatedHaving.requiresProducer (.or conditional ordinary) 1 3 (fun _ => true) = true ∧
    CorrelatedHaving.fieldIds (.and conditional ordinary) = [1, 3, 2] := by native_decide

end A12Kernel.Conformance.HavingGroupPresence
