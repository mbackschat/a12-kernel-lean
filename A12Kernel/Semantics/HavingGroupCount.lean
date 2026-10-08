import A12Kernel.Semantics.HavingEntityList

namespace A12Kernel

/-- A starred repeatable terminal contributes rows; every other counted group contributes
content per instance. Field membership is retained separately from either runtime projection. -/
inductive HavingGroupCountKind where
  | content
  | rows
  deriving Repr, DecidableEq

structure HavingGroupCountOperand where
  origin : HavingOrigin
  source : ComputationGroupOperand
  kind : HavingGroupCountKind
  capacity : Option Nat
  deriving Repr, DecidableEq

namespace HavingGroupCountOperand

def bindingScope (operand : HavingGroupCountOperand) : List RepeatableLevel :=
  operand.source.starPath.map (·.bindingScope) |>.getD operand.source.reference.boundRepeatableScope

def presenceSlot (operand : HavingGroupCountOperand) : HavingFieldListSlot HavingPresenceRef :=
  .extent (match operand.source.starPath with
    | none => .group operand.source.reference
    | some path => .starredGroup operand.source.reference.path path)
    (operand.source.members.map fun field => { origin := operand.origin, field })

private def contentCount (operand : HavingGroupCountOperand) (phase : Phase)
    (groups : CorrelationGroupReads Error) (environment : Env) : Except Error (Option Nat) := do
  match phase with
  | .validation =>
      let state ← groups.validation environment operand.source.reference
      pure (match numberOfFilledGroups [state] with | .unknown => none | .value count => some count)
  | .computation =>
      let (cells, rows) ← groups.computation environment operand.source
      pure (some (GroupCountOperandReading.fixed cells rows).contribution)

private def countInstances (operand : HavingGroupCountOperand) (phase : Phase)
    (groups : CorrelationGroupReads Error) : List Env → Nat → Except Error (Option Nat)
  | [], total => pure (some total)
  | environment :: rest, total => do
      match ← operand.contentCount phase groups environment with
      | none => pure none
      | some count => countInstances operand phase groups rest (total + count)

/-- Terminal stars never inspect cell content; a fixed terminal below a star does so once
per in-capacity environment (spec/07 §5, ordinary `GroupCountOperandReading`). -/
def readCount (operand : HavingGroupCountOperand) (phase : Phase)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame) : Except Error (Option Nat) := do
  let some groups := context.groups | throw (context.groupUnavailable operand.source.reference.path)
  let environment := frame.envAt operand.origin
  match operand.source.starPath with
  | none => operand.contentCount phase groups environment
  | some path =>
      let some extent := groups.groupExtent? | throw (context.groupUnavailable operand.source.reference.path)
      let environments ← extent operand.source.reference.path environment path
      match operand.kind with
      | .rows => pure (some environments.length)
      | .content => operand.countInstances phase groups environments 0

end HavingGroupCountOperand

namespace HavingGroupCount

def capacity? (operands : List HavingGroupCountOperand) : Option Nat :=
  operands.foldlM (m := Option) (init := 0) fun total operand => (total + ·) <$> operand.capacity

private def readTotal (phase : Phase) (context : ResolvingCorrelationContext Error)
    (frame : CorrelationFrame) : List HavingGroupCountOperand → Nat → Except Error (Option Nat)
  | [], total => pure (some total)
  | operand :: rest, total => do
      match ← operand.readCount phase context frame with
      | none => pure none
      | some count => readTotal phase context frame rest (total + count)

def evaluate (phase : Phase) (context : ResolvingCorrelationContext Error)
    (frame : CorrelationFrame) (operands : List HavingGroupCountOperand) : Except Error (Option NumericOperand) := do
  let total ← readTotal phase context frame operands 0
  pure (total.bind fun count => match phase with
    | .computation => some (.value count .fixed)
    | .validation => (capacity? operands).bind fun capacity =>
        ((FilledGroupCount.value count).availableWithFillability? capacity).map fun (count, movement) =>
          .value count movement)

end HavingGroupCount
end A12Kernel
