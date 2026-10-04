import A12Kernel.Conformance.GeneratedComputationValidation.Support.Core

/-! # Group guard phase preservation

Generated rules use validation's content/error product, not computation's stored-content presence.
The guard retains group identity so an Execute or Transform consumer can select the right phase.
-/

namespace A12Kernel.Conformance.GeneratedComputationValidation.GroupGuards

open A12Kernel
open A12Kernel.Conformance.GeneratedComputationValidation.Support.Core

private def groupModel : FlatModel := { model with fields := [
  { gate with groupPath := ["Form", "Box"] }, target, broken,
  { textGuard with groupPath := ["Form", "Spare"] }] }

private def reference (name : String) : SurfaceGroupReference :=
  .path { base := .absolute, groups := ["Form", name] }

private def guards : List (SurfaceComputationConditionOf SurfaceNumericComputationAtom SurfaceComputationPredicate) :=
  [.groupPresence .filled (reference "Box"), .groupPresence .notFilled (reference "Box")] ++
  ([.allGroupsFilled, .noGroupFilled, .atLeastOneGroupFilled, .notAllGroupsFilled,
    .groupsNotCollectivelyFilled] : List GroupFillQuantifier).map fun operator =>
      .groupFill operator { first := .group (reference "Box"), rest := [.group (reference "Spare")] }

private def evaluate (source : FlatModel)
    (surface : SurfaceComputationConditionOf SurfaceNumericComputationAtom SurfaceComputationPredicate)
    (input : DocumentData) (declaringGroup : GroupPath := ["Form"])
    (targetGroup : GroupPath := ["Form"]) : Option Char := do
  let guard ← (source.elaborateCheckedComputationCondition declaringGroup targetGroup surface).toOption
  let operation ← (elaborateNumericComputationOperation source declaringGroup target.id
    (.literal { value := 3, authoredScale := 0 })).toOption
  let rule ← (assembleGeneratedNumericOperationTableRule source {
    targetField := target.id, name := "computedTarget", commonPrecondition := some guard
    alternatives := .singleton { operation }, messagePlan }).toOption
  let prepared ← (prepareFlatStringContext evaluationWorld builtinStringPatternCompiler source).toOption
  let checked ← (checkDocument prepared "en_US" input).toOption
  let result ← (rule.evalAddressedFull {
    scalar := { fields := checked.flatContext.withWorld evaluationWorld, groups := GroupPresenceContext.unavailable }
    outer := [], input := .checked checked } true).toOption
  pure (match result with
    | .fired message => if message.messageType == .value then 'V' else 'O'
    | .notFired | .unknown => '-')

private def outcome (guard : SurfaceComputationConditionOf SurfaceNumericComputationAtom SurfaceComputationPredicate)
    (box : RawCell) (spare : Bool) : Option Char := do
  let boxRaw : RawCell := match box with | .empty => .presentEmpty | other => other
  let boxStored := match box with | .empty => "" | .parsed _ => "1" | _ => "bad"
  let spareRaw : RawCell := if spare then .parsed (.str "A") else .presentEmpty
  evaluate groupModel guard { instantiatedRows := [], cells := [
    { address := { field := target.id, path := [] }, stored := "1", raw := .parsed (.num 1) },
    { address := { field := gate.id, path := [] }, stored := boxStored, raw := boxRaw },
    { address := { field := textGuard.id, path := [] }, stored := if spare then "A" else "", raw := spareRaw }] }

private def signature (box : RawCell) (spare : Bool) : Option String :=
  String.ofList <$> guards.mapM (fun guard => outcome guard box spare)

example : signature .empty false = some "-O-O-O-" ∧
    signature (.parsed (.num 1)) false = some "V---VOO" ∧
    signature (.parsed (.num 1)) true = some "V-V-V--" ∧
    signature (.rejected .malformed) false = some "-----O-" := by native_decide

example : outcome (.groupPresence .filled (.path { base := .absolute, groups := ["Form"] }))
    .empty false = some 'V' := by native_decide

private def starredOutcome (terminal : Bool) (operator : GroupFillQuantifier)
    (rows : List RawCell) : Option Char := do
  let source : FlatModel := {
    fields := [target, { gate with groupPath := if terminal then ["Form", "Rows"] else ["Form", "Rows", "Box"], repeatableScope := [10] }]
    repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 2 }] }
  let path : SurfaceStarGroupPath := { base := .absolute, groups :=
    [{ name := "Form" }, { name := "Rows", starred := true }] ++ if terminal then [] else [{ name := "Box" }] }
  evaluate source (.groupFill operator { first := .starredGroup path, rest := [] }) {
    instantiatedRows := rows.zipIdx |>.map (fun (_, index) => { group := 10, path := [index + 1] })
    cells := [{ address := { field := target.id, path := [] }, stored := "1", raw := .parsed (.num 1) }] ++
      (rows.zipIdx.map fun (raw, index) => {
        address := { field := gate.id, path := [index + 1] }
        stored := match raw with | .empty => "" | .parsed _ => "1" | _ => "bad"
        raw := match raw with | .empty => .presentEmpty | other => other }) }

example : starredOutcome true .noGroupFilled [] = some 'O' ∧
    starredOutcome true .atLeastOneGroupFilled [.empty] = some 'V' ∧
    starredOutcome true .noGroupFilled [.empty] = some '-' ∧
    starredOutcome true .atLeastOneGroupFilled [] = some '-' ∧
    starredOutcome false .atLeastOneGroupFilled [.parsed (.num 1)] = some 'V' ∧
    starredOutcome false .noGroupFilled [.parsed (.num 1)] = some '-' ∧
    starredOutcome false .noGroupFilled [.empty] = some 'O' ∧
    starredOutcome false .atLeastOneGroupFilled [.empty] = some '-' ∧
    starredOutcome false .atLeastOneGroupFilled [.rejected .malformed] = some '-' ∧
    starredOutcome false .noGroupFilled [.rejected .malformed] = some '-' ∧
    starredOutcome false .atLeastOneGroupFilled [.empty, .empty, .parsed (.num 1)] = some '-' := by native_decide

private def crossGroupOutcome (sibling : Bool) (operator : GroupPresenceOperator)
    (reference : SurfaceGroupReference) (filled : Bool) : Option Char :=
  let targetGroup := if sibling then ["Form", "Destination"] else ["Form"]
  let source : FlatModel := { fields := [
    { gate with groupPath := ["Form", "Box"] }, { target with groupPath := targetGroup }] }
  evaluate source (.groupPresence operator reference) {
    instantiatedRows := [], cells := [
      { address := { field := target.id, path := [] }, stored := "1", raw := .parsed (.num 1) },
      { address := { field := gate.id, path := [] }, stored := if filled then "1" else "",
        raw := if filled then .parsed (.num 1) else .presentEmpty }] }
    ["Form", "Box"] targetGroup

example : [false, true].all (fun sibling =>
    crossGroupOutcome sibling .filled (.ruleGroup false) true == some 'V' &&
    crossGroupOutcome sibling .filled (.ruleGroup false) false == some '-' &&
    crossGroupOutcome sibling .notFilled (.ruleGroup false) true == some '-' &&
    crossGroupOutcome sibling .notFilled (.ruleGroup false) false == some 'O' &&
    crossGroupOutcome sibling .filled (reference "Box") true == some 'V') = true := by native_decide

private def generatedMetadataAdmission : Option (List Bool) := do
  let source : FlatModel := {
    fields := [target, { gate with groupPath := ["Form", "Rows", "Box"], repeatableScope := [10] }]
    repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 2 }] }
  let guard ← (source.elaborateCheckedComputationCondition ["Form"] ["Form"]
    (.groupFill .atLeastOneGroupFilled { first := .starredGroup { base := .absolute, groups :=
      [{ name := "Form" }, { name := "Rows", starred := true }, { name := "Box" }] }, rest := [] })).toOption
  let .leaf (.groupPresence operator operand) := guard | none
  let path ← operand.starPath
  let operation ← (elaborateNumericComputationOperation source ["Form"] target.id
    (.literal { value := 3, authoredScale := 0 })).toOption
  let variants : List ComputationGroupOperand := [operand,
    { operand with members := [] },
    { operand with content := { operand.content with fields := [] } },
    { operand with reference := { operand.reference with boundRepeatableScope := [] } },
    { operand with starPath := some { path with axes := path.axes.map fun axis =>
        { axis with repeatability := some 3 } } }]
  pure (variants.map fun variant => (assembleGeneratedNumericOperationTableRule source {
    targetField := target.id, name := "metadataGuard",
    commonPrecondition := some (.leaf (.groupPresence operator variant)),
    alternatives := .singleton { operation }, messagePlan }).isOk)

example : generatedMetadataAdmission = some [true, false, false, false, false] := by native_decide

end A12Kernel.Conformance.GeneratedComputationValidation.GroupGuards
