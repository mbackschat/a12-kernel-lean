import A12Kernel.Semantics.Correlation
import A12Kernel.Elaboration.HavingGroupCount

namespace A12Kernel.Conformance.HavingGroupCount
open A12Kernel

private def frame : CorrelationFrame := { innerEnv := [(10, 1)], outerEnv := [(10, 2)] }
private def path : StarPath := { axes := [{ level := 10, repeatability := some 3 }], firstStar := 0 }
private def operand (kind : HavingGroupCountKind) (star : Bool := true)
    (origin : HavingOrigin := .inner) : HavingGroupCountOperand := {
  origin, kind, capacity := some (if star then 3 else 1)
  source := {
    reference := { path := ["Form", "Rows", "Empty"], origin := .path, boundRepeatableScope := [10] }
    content := { scope := [10], fields := [], rowLevels := [] }, members := []
    starPath := if star then some path else none, dependencyKind := .ordinaryList } }
private def groups : CorrelationGroupReads CorrelationRuntimeFault := {
  validation := fun _ _ => .error .valueFailure
  computation := fun _ _ => .error .valueFailure
  fieldExtent := fun _ _ _ _ => .error .valueFailure
  groupExtent? := some fun _ _ _ => pure [[(10, 1)], [(10, 2)]] }
private def context : ResolvingCorrelationContext CorrelationRuntimeFault := {
  ({ read := fun _ _ => { rawPresent := false, parsed := none, findings := [] } } : CorrelationContext).asResolving with
  groups := some groups }
private def result (phase : Phase) (operands : List HavingGroupCountOperand)
    (reads : CorrelationGroupReads CorrelationRuntimeFault := groups) :=
  match A12Kernel.HavingGroupCount.evaluate phase { context with groups := some reads } frame operands with
  | .ok value => Sum.inr value
  | .error error => Sum.inl error

example : result .validation [operand .rows] = .inr (some (.value 2 .growOnly)) ∧
    result .computation [operand .rows] = .inr (some (.value 2 .fixed)) ∧
    result .validation [{ operand .rows with capacity := some 2 }] = .inr (some (.value 2 .fixed)) ∧
    result .computation [{ operand .rows with capacity := none }] = .inr (some (.value 2 .fixed)) := by native_decide

example : [Phase.validation, .computation].all (fun phase =>
    result phase [operand .rows] { groups with groupExtent? := none } ==
      .inl (.groupUnavailable ["Form", "Rows", "Empty"])) = true := by native_decide

private def contentReads : CorrelationGroupReads CorrelationRuntimeFault := { groups with
  validation := fun env _ => pure { content := env == frame.innerEnv, erroneous := false, relevance := .fullyRelevant }
  computation := fun env _ => pure ([], env == frame.innerEnv) }
example : result .validation [operand .content] contentReads = .inr (some (.value 1 .growOnly)) ∧
    result .computation [operand .content] contentReads = .inr (some (.value 1 .fixed)) ∧
    result .computation [operand .content false .inner, operand .content false .outer] contentReads =
      .inr (some (.value 1 .fixed)) := by native_decide

private def undecided : CorrelationGroupReads CorrelationRuntimeFault := { groups with
  validation := fun env _ => if env == frame.innerEnv then
    pure { content := false, erroneous := true, relevance := .fullyRelevant } else .error .valueFailure
  computation := fun _ _ => pure ([observeCell .computation
    ({ rawPresent := true, parsed := none, findings := [.malformed] } : CheckedCell)], false) }
example : result .validation [operand .content] undecided = .inr none ∧
    result .validation [operand .content false, operand .rows] undecided = .inr none ∧
    result .computation [operand .content] undecided = .inr (some (.value 2 .fixed)) ∧
    result .validation [operand .content] = .inl .valueFailure := by native_decide

example : (HavingNumericAtom.groupCount [operand .content false .outer]).origins = [.outer] ∧
    (HavingNumericAtom.groupCount [operand .content false .outer]).fieldOrigins = [] ∧
    A12Kernel.HavingGroupCount.firstOverlap? [operand .rows, operand .rows] = none ∧
    (A12Kernel.HavingGroupCount.firstOverlap? [operand .content false, operand .content false]).isSome = true ∧
    A12Kernel.HavingGroupCount.firstOverlap? [operand .content false .inner, operand .content false .outer] = none := by native_decide

private def model : FlatModel := {
  fields := [{
    id := 1, name := "Value", groupPath := ["Form", "Rows"], repeatableScope := [10]
    policy := { kind := .string } }]
  repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 3 }] }
private def checkedOperand : HavingGroupCountOperand := {
  origin := .inner, kind := .rows, capacity := some 3
  source := {
    reference := { path := ["Form", "Rows"], origin := .path, boundRepeatableScope := [10] }
    content := model.computationGroupSource ["Form", "Rows"], members := [1]
    starPath := some path, dependencyKind := .ordinaryList } }
example : A12Kernel.HavingGroupCount.wellFormed [checkedOperand] model [10] [] = true ∧
    A12Kernel.HavingGroupCount.wellFormed [{ checkedOperand with capacity := some 2 }] model [10] [] = false ∧
    A12Kernel.HavingGroupCount.wellFormed [{ checkedOperand with kind := .content }] model [10] [] = false ∧
    A12Kernel.HavingGroupCount.wellFormed [{ checkedOperand with source := { checkedOperand.source with members := [] } }] model [10] [] = false ∧
    A12Kernel.HavingGroupCount.wellFormed [{ checkedOperand with source := { checkedOperand.source with dependencyKind := .conditionalPresence } }] model [10] [] = false := by native_decide

end A12Kernel.Conformance.HavingGroupCount
