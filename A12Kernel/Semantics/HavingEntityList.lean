import A12Kernel.Semantics.CorrelationContext
import A12Kernel.Semantics.StarAddressing

namespace A12Kernel

/-- Authored extent identity remains available to scope and pointer consumers (spec/07 §5).
The row resolver uses the operand's depth, independently of the surrounding filter's depth. -/
inductive HavingEntityExtent where
  | starField (groupPath : GroupPath) (selection : StarPath)
  | group (reference : ResolvedGroupReference)
  | starredGroup (groupPath : GroupPath) (selection : StarPath)
  deriving Repr, DecidableEq

def HavingEntityExtent.groupPath : HavingEntityExtent → GroupPath
  | .starField path _ | .starredGroup path _ => path
  | .group reference => reference.path

def HavingEntityExtent.boundCount : HavingEntityExtent → Nat
  | .starField _ selection | .starredGroup _ selection => selection.firstStar
  | .group reference => reference.boundRepeatableScope.length

/-- One authored field-list slot. An extent retains declaration order and each declaration's
origin; checked admission certifies that the origins within one extent agree. -/
inductive HavingFieldListSlot (Ref : Type) where
  | direct (reference : Ref)
  | extent (source : HavingEntityExtent) (references : List Ref)
  deriving Repr, DecidableEq

namespace HavingFieldListSlot

variable {Ref Error Accumulator Result : Type}

def references : HavingFieldListSlot Ref → List Ref
  | .direct reference => [reference]
  | .extent _ references => references

def map (transform : Ref → Other) : HavingFieldListSlot Ref → HavingFieldListSlot Other
  | .direct reference => .direct (transform reference)
  | .extent source references => .extent source (references.map transform)

def mapM [Monad m] (transform : Ref → m Other) : HavingFieldListSlot Ref → m (HavingFieldListSlot Other)
  | .direct reference => .direct <$> transform reference
  | .extent source references => .extent source <$> references.mapM transform

def isDirect : HavingFieldListSlot Ref → Bool
  | .direct _ => true
  | .extent _ _ => false

private def foldEnvironments (reference : Ref)
    (step : Accumulator → Ref → Env → Except Error (Sum Accumulator Result))
    (accumulator : Accumulator) : List Env → Except Error (Sum Accumulator Result)
  | [] => pure (.inl accumulator)
  | environment :: remaining => do
      match ← step accumulator reference environment with
      | .inl next => foldEnvironments reference step next remaining
      | .inr result => pure (.inr result)

private def foldExtent (source : HavingEntityExtent)
    (origin : Ref → HavingOrigin) (field : Ref → FieldId)
    (groups : CorrelationGroupReads Error) (frame : CorrelationFrame)
    (step : Accumulator → Ref → Env → Except Error (Sum Accumulator Result))
    (onOmitted : Accumulator → Ref → Except Error (Sum Accumulator Result))
    (accumulator : Accumulator) : List Ref → Except Error (Sum Accumulator Result)
  | [] => pure (.inl accumulator)
  | reference :: remaining => do
      let (environments, omitted) ← groups.fieldExtent source.groupPath (frame.envAt (origin reference))
        source.boundCount (field reference)
      let result ← foldEnvironments reference step accumulator environments
      let result ← match result with
        | .inl next => if omitted then onOmitted next reference else pure (.inl next)
        | .inr result => pure (.inr result)
      match result with
      | .inl next => foldExtent source origin field groups frame step onOmitted next remaining
      | .inr result => pure (.inr result)

/-- Acquire declarations and read their rows only as requested by the consumer's continuation.
The ordinary group walk's declaration-major ordering and in-capacity domain (spec/07 §5) are
retained without eagerly acquiring a later declaration or inventing capacity-tail cells.
Each exhausted declaration's omitted tail invokes `onOmitted` before the next declaration;
the default ignores it, while field-fill consumers use one marker (`evalComputation_omittedRun`). -/
def foldRead (origin : Ref → HavingOrigin) (field : Ref → FieldId)
    (context : ResolvingCorrelationContext Error) (frame : CorrelationFrame)
    (step : Accumulator → Ref → Env → Except Error (Sum Accumulator Result))
    (accumulator : Accumulator) (slots : List (HavingFieldListSlot Ref))
    (onOmitted : Accumulator → Ref → Except Error (Sum Accumulator Result) := fun next _ => pure (.inl next)) :
    Except Error (Sum Accumulator Result) := match slots with
  | [] => pure (.inl accumulator)
  | slot :: remaining => do
      let result ← match slot with
        | .direct reference => step accumulator reference (frame.envAt (origin reference))
        | .extent source references => do
            let some groups := context.groups | throw (context.groupUnavailable source.groupPath)
            foldExtent source origin field groups frame step onOmitted accumulator references
      match result with
      | .inl next => foldRead origin field context frame step next remaining onOmitted
      | .inr result => pure (.inr result)

end HavingFieldListSlot
end A12Kernel
