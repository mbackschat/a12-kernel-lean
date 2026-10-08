import A12Kernel.Semantics.CorrelationInputs
import A12Kernel.Semantics.HavingEntityList

namespace A12Kernel

/-- Computation-only adapters retain physical row content and their current cell overlay. Validation requires its own checked product-state reader (spec/02, group presence). -/
def CorrelationContext.withComputationGroups (context : CorrelationContext) (document : Document) :
    CorrelationContext :=
  { context with groups := some {
      groupExtent? := context.groups.bind (·.groupExtent?)
      fieldExtent := fun path env depth field => match context.groups with
        | some groups => groups.fieldExtent path env depth field
        | none => .error (.groupUnavailable path)
      validation := fun env reference => match context.groups with
        | some groups => groups.validation env reference
        | none => .error (.groupUnavailable reference.path)
      computation := fun env source =>
        (source.content.read document context.read env).mapError fun _ =>
          .groupUnavailable source.reference.path } }

/-- Addressed computation adapters preserve their own structural read and binding errors. -/
def ResolvingCorrelationContext.withComputationGroups (context : ResolvingCorrelationContext Error)
    (document : Document) : ResolvingCorrelationContext Error :=
  { context with groups := some {
      groupExtent? := context.groups.bind (·.groupExtent?)
      fieldExtent := fun path env depth field => match context.groups with
        | some groups => groups.fieldExtent path env depth field
        | none => .error (context.groupUnavailable path)
      validation := fun env reference => match context.groups with
        | some groups => groups.validation env reference
        | none => .error (context.groupUnavailable reference.path)
      computation := fun env source =>
        source.content.readWith document context.read context.bindingError env } }

def HavingGroupOperand.origin : HavingGroupOperand → HavingOrigin
  | .field reference => reference.origin
  | .group origin _ => origin

def HavingGroupOperand.fieldIds : HavingGroupOperand → List FieldId
  | .field reference => [reference.field]
  | .group _ source => source.members

def HavingGroupOperand.presenceSlot : HavingGroupOperand → HavingFieldListSlot HavingPresenceRef
  | .field reference => .direct reference
  | .group origin source => .extent (match source.starPath with
      | none => .group source.reference
      | some path => .starredGroup source.reference.path path)
      (source.members.map fun field => { origin, field })

private def readValidationGroup (context : ResolvingCorrelationContext Error)
    (frame : CorrelationFrame) (origin : HavingOrigin) (source : ComputationGroupOperand) :
    Except Error GroupPresenceState := do
  let some groups := context.groups | throw (context.groupUnavailable source.reference.path)
  groups.validation (frame.envAt origin) source.reference

def evalHavingGroupPresenceValidation (operator : GroupPresenceOperator)
    (origin : HavingOrigin) (source : ComputationGroupOperand)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame) : Except Error Verdict := do
  pure (operator.eval (← readValidationGroup context frame origin source))

private def HavingGroupOperand.readValidation (operand : HavingGroupOperand)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame) :
    Except Error GroupListPresenceTally :=
  match operand with
  | .field reference => do
      pure (GroupListPresenceTally.ofStates [(← reference.observeInAtResolving .validation context frame).asGroupListPresence])
  | .group origin source => do
      match source.starPath with
      | none => pure (GroupListPresenceTally.ofGroupStates [← readValidationGroup context frame origin source])
      | some path =>
          let some groups := context.groups | throw (context.groupUnavailable source.reference.path)
          let some extent := groups.groupExtent? | throw (context.groupUnavailable source.reference.path)
          let environments ← extent source.reference.path (frame.envAt origin) path
          -- A terminal repeatable group contributes structure, while a fixed terminal below a
          -- star contributes its product state (spec/07 §5; ordinary group-list tally).
          if path.axes.getLast?.any (fun axis => source.content.rowLevels.contains axis.level) then
            pure (GroupListPresenceTally.filledOnly environments.length)
          else
            GroupListPresenceTally.ofGroupStates <$> environments.mapM (fun env => groups.validation env source.reference)

def evalHavingGroupFillValidation (operator : GroupFillQuantifier)
    (first : HavingGroupOperand) (rest : List HavingGroupOperand)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame) : Except Error Verdict := do
  let tallies ← (first :: rest).mapM (·.readValidation context frame)
  pure ((operator.evalTally (tallies.foldl GroupListPresenceTally.add (GroupListPresenceTally.ofStates []))).asConservativeVerdict)

def evalHavingGroupPresenceComputation (operator : GroupPresenceOperator)
    (origin : HavingOrigin) (source : ComputationGroupOperand)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame) :
    Except Error ComputationConditionResult := do
  let some groups := context.groups | throw (context.groupUnavailable source.reference.path)
  match source.starPath with
  | none =>
      let (cells, rows) ← groups.computation (frame.envAt origin) source
      pure (operator.evalComputation cells rows)
  | some path =>
      let some extent := groups.groupExtent? | throw (context.groupUnavailable source.reference.path)
      let environments ← extent source.reference.path (frame.envAt origin) path
      let instances ← environments.mapM fun env => do
        let (cells, rows) ← groups.computation env source
        pure (GroupPresenceOperator.filled.evalComputation cells rows)
      let present := instances.any (· == .holds)
      pure (if (match operator with | .filled => present | .notFilled => !present) then .holds else .notTrue)

def havingGroupFillTree (operator : GroupFillQuantifier)
    (first : HavingGroupOperand) (rest : List HavingGroupOperand) :
    ConditionTree (GroupPresenceOperator × HavingGroupOperand) :=
  let pair operand := (ConditionTree.leaf (.filled, operand), ConditionTree.leaf (.notFilled, operand))
  operator.conditionTree (pair first) (rest.map pair)

private def HavingGroupOperand.evalComputation (operand : HavingGroupOperand)
    (operator : GroupPresenceOperator) (context : ResolvingCorrelationContext Error)
    (frame : CorrelationFrame) : Except Error ComputationConditionResult :=
  match operand with
  | .field reference => do
      let observation ← reference.observeInAtResolving .computation context frame
      pure (match operator with
        | .filled => observation.evalComputationFilled
        | .notFilled => observation.evalComputationNotFilled)
  | .group origin source => evalHavingGroupPresenceComputation operator origin source context frame

def evalHavingGroupFillComputation (operator : GroupFillQuantifier)
    (first : HavingGroupOperand) (rest : List HavingGroupOperand)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame) :
    Except Error ComputationConditionResult :=
  (havingGroupFillTree operator first rest).evalComputationExcept fun (operator, operand) =>
    operand.evalComputation operator context frame

private def havingGroupDependencyLeaf :
    GroupPresenceOperator × HavingGroupOperand → ComputationConditionLeaf Empty Empty
  | (.filled, .field reference) => .fieldFilled reference.field
  | (.notFilled, .field reference) => .fieldNotFilled reference.field
  | (operator, .group _ source) => .groupPresence operator source

/-- Dependency queries consume the same expansion as evaluation while retaining the authored group's dependency classification (spec/09 §5). -/
def havingGroupFillDependencies (operator : GroupFillQuantifier)
    (first : HavingGroupOperand) (rest : List HavingGroupOperand) : ComputationConditionOf Empty Empty :=
  (havingGroupFillTree operator first rest).map havingGroupDependencyLeaf

end A12Kernel
