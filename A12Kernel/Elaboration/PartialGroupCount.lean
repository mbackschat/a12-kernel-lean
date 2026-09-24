import A12Kernel.Elaboration.StarGroup
import A12Kernel.Elaboration.CheckedIndexPreliminary
import A12Kernel.Elaboration.CheckedStarDocument

/-! # `NumberOfFilledGroups` under partial validation

The count is decided on the counted group's own instances, in four steps, and each step is what a
neighbouring coverage separates:

1. The counted group's own identifiers settle the extent: those at or above the group and every
   relevant descendant cut back to its depth, wildcard-reduced, must wildcard every reopened level.
2. The first declared instance must be fully relevant and free of errors.
3. Every declared instance the document lacks must be fully relevant: the walk covers declared
   rows, not held ones.
4. A held instance counts by its admitted content, and one no identifier reaches leaves the count
   undecidable.

A fixed group is its own first instance. A list is decided when every operand is, and counts their
sum. Each step reads the partial preliminary, so relevance and admitted content come from the same
owner the rule evaluator uses. Every step and its separating coverage are the peer's second `kf464`
table ([inbound](../../docs/SOURCES.md#inbound-2026-09-24b-kf464-partial-group-count)).
-/

namespace A12Kernel

/-- A filled-group count under partial validation: undecidable, or decided with the value full
    validation would count. -/
inductive PartialValidationFilledGroupCountResult where
  | nonRelevant
  | evaluated (count : FilledGroupCount)
  deriving Repr, DecidableEq

/-- Every declared coordinate combination of the reopened axes, first instance first. A missing
    declared capacity leaves no finite walk, so the count stays undecidable rather than acquiring an
    unmeasured bound; `RepeatableGroupDecl.repeatability` owns why no authorable model reaches it. -/
private def declaredCoordinates : List StarAxis → Option (List Env)
  | [] => some [[]]
  | axis :: rest => do
      let capacity ← axis.repeatability
      let tails ← declaredCoordinates rest
      pure ((List.range capacity).flatMap fun index =>
        tails.map fun tail => (axis.level, index + 1) :: tail)

/-- The group-presence query a partial walk reads, answered by the call's relevance-selected slice. -/
abbrev PartialGroupResolver :=
  GroupPath → Env → Except CheckedAddressingError ResolvedGroupPresenceInput

/-- Run the walk over one counted group. `bound` fixes the levels the enclosing evaluation binds,
    `reopened` lists the levels the operand walks, and `held` the instantiated in-capacity instances.
    `none` is an undecidable count, never zero. -/
private def walkGroupCount (model : FlatModel) (scope : ValidationRelevanceScope)
    (resolveGroup : PartialGroupResolver) (groupPath : GroupPath) (bound : Env) (reopened : List StarAxis) (held : List Env)
    (outer : Env) : Except CheckedAddressingError (Option Nat) := do
  if !scope.coversGroupCountExtent model groupPath (bound.map (·.1))
      (reopened.map (·.level)) outer then
    return none
  let some coordinates := declaredCoordinates reopened | return none
  let rec visit (isFirst : Bool) (count : Nat) :
      List Env → Except CheckedAddressingError (Option Nat)
    | [] => pure (some count)
    | coordinate :: remaining => do
        let environment := bound ++ coordinate
        if held.contains environment then
          let state := (← resolveGroup groupPath environment).derive
          if isFirst && (state.relevance != .fullyRelevant || state.erroneous) then
            return none
          if state.relevance == .noneRelevant then return none
          visit false (if state.content then count + 1 else count) remaining
        else if scope.groupRelevance model groupPath environment != .fullyRelevant then
          return none
        else
          visit false count remaining
  visit true 0 coordinates

namespace CheckedGroupCountOperand

/-- One operand's count under partial validation, or `none` when the walk leaves it undecidable. -/
def partialCount (operand : CheckedGroupCountOperand model) (scope : ValidationRelevanceScope)
    (resolveGroup : PartialGroupResolver) (document : Document) (outer : Env) :
    Except CheckedAddressingError (Option Nat) := do
  match operand with
  | .fixed reference =>
      let bound ← reference.boundRepeatableScope.mapM fun level => do
        pure (level, ← (outer.bindingAt level).mapError CheckedAddressingError.environment)
      walkGroupCount model scope resolveGroup reference.path bound [] [bound] outer
  | .starred source => do
      let bound ← (source.path.boundEnvironment outer).mapError .addressing
      let held ← (source.path.inCapacityEnvironments document outer).mapError .addressing
      walkGroupCount model scope resolveGroup source.group.path bound
        (source.path.axes.drop source.path.firstStar) held outer
  | .starredPresence source => do
      let bound ← (source.path.boundEnvironment outer).mapError .addressing
      let held ← (source.path.inCapacityEnvironments document outer).mapError .addressing
      walkGroupCount model scope resolveGroup source.groupPath bound
        (source.path.axes.drop source.path.firstStar) held outer

/-- A filled-group count under partial validation: decided when every operand's walk is, counting
    their sum. `resolveGroup` must answer from the same relevance-selected slice as `scope`. -/
def evaluatePartialWith (operands : List (CheckedGroupCountOperand model))
    (scope : ValidationRelevanceScope) (resolveGroup : PartialGroupResolver) (document : Document)
    (outer : Env) : Except CheckedAddressingError PartialValidationFilledGroupCountResult := do
  let counts ← operands.mapM (·.partialCount scope resolveGroup document outer)
  match counts.mapM id with
  | some each => pure (.evaluated (.value each.sum))
  | none => pure .nonRelevant

/-- The same count read off one partial preliminary, which owns both the scope and the slice. -/
def evaluatePartial (operands : List (CheckedGroupCountOperand model))
    (preliminary : CheckedPartialPreliminary model) (outer : Env) :
    Except CheckedAddressingError PartialValidationFilledGroupCountResult :=
  evaluatePartialWith operands preliminary.relevance
    (fun groupPath environment =>
      (preliminary.groupPresenceInput groupPath environment false).mapError .group)
    preliminary.index.base.source.toDocument outer

end CheckedGroupCountOperand

end A12Kernel
