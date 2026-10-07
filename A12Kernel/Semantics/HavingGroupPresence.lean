import A12Kernel.Semantics.CorrelationInputs

namespace A12Kernel

/-- Computation-only adapters retain physical row content and their current cell overlay. Validation requires its own checked product-state reader (spec/02, group presence). -/
def CorrelationContext.withComputationGroups (context : CorrelationContext) (document : Document) :
    CorrelationContext :=
  { context with groups := some {
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
    Except Error GroupListPresenceState :=
  match operand with
  | .field reference =>
      CellObservation.asGroupListPresence <$> reference.observeInAtResolving .validation context frame
  | .group origin source =>
      GroupPresenceState.asGroupListPresence <$> readValidationGroup context frame origin source

def evalHavingGroupFillValidation (operator : GroupFillQuantifier)
    (first : HavingGroupOperand) (rest : List HavingGroupOperand)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame) : Except Error Verdict := do
  let states ← (first :: rest).mapM (·.readValidation context frame)
  pure ((operator.evalPresence states).asConservativeVerdict)

def evalHavingGroupPresenceComputation (operator : GroupPresenceOperator)
    (origin : HavingOrigin) (source : ComputationGroupOperand)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame) :
    Except Error ComputationConditionResult := do
  let some groups := context.groups | throw (context.groupUnavailable source.reference.path)
  let (cells, rows) ← groups.computation (frame.envAt origin) source
  pure (operator.evalComputation cells rows)

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
