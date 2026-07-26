import A12Kernel.Document

/-! # Parallel-computation post-loop clearing

This capsule begins after checked computation analysis has selected the kernel's parallel-iteration marking route and supplied model-derived repeatable scopes. An invalid joined index column emits a cause-blind mark from one target instance's coordinates truncated to the common scope shared with the malformed index group's parent. The mark may therefore cover more target instances than the one from which it was created. Route selection, index checking, computation execution, and public clearing remain separate. -/

namespace A12Kernel

/-- Longest common outer repeatable scope, preserving model order. -/
def commonRepeatablePrefix :
    List RepeatableLevel → List RepeatableLevel → List RepeatableLevel
  | left :: leftRest, right :: rightRest =>
      if left == right then
        left :: commonRepeatablePrefix leftRest rightRest
      else
        []
  | _, _ => []

/-- The checked-scope information needed by post-loop invalid marking. The constructor derives the shared scope rather than accepting a caller-supplied truncation width. -/
structure ParallelComputationMarkPlan where
  private mk ::
  targetScope : List RepeatableLevel
  malformedIndexParentScope : List RepeatableLevel
  sharedScope : List RepeatableLevel
  deriving Repr, DecidableEq

namespace ParallelComputationMarkPlan

def ofScopes (targetScope malformedIndexParentScope :
    List RepeatableLevel) : ParallelComputationMarkPlan :=
  {
    targetScope
    malformedIndexParentScope
    sharedScope :=
      commonRepeatablePrefix targetScope malformedIndexParentScope
  }

end ParallelComputationMarkPlan

/-- One cause-blind invalidity key tied to its exact scope plan. -/
structure ParallelComputationMark (plan : ParallelComputationMarkPlan) where
  private mk ::
  coordinates : List Nat
  deriving Repr, DecidableEq

namespace ParallelComputationMarkPlan

/-- A clean index column emits no mark. Any unavailable-column cause emits the same prefix key after structurally resolving the complete target instance. -/
def markForUnavailable (plan : ParallelComputationMarkPlan)
    (unavailable : Option FormalCause) (targetEnvironment : Env) :
    Except EnvBindingError (Option (ParallelComputationMark plan)) :=
  match unavailable with
  | none => pure none
  | some _ =>
      match targetEnvironment.pathForScope plan.targetScope with
      | .error fault => .error fault
      | .ok path => .ok (some {
          coordinates := path.take plan.sharedScope.length
        })

/-- Whether one target instance lies in the mark's shared-prefix blast radius. -/
def covers (plan : ParallelComputationMarkPlan)
    (mark : ParallelComputationMark plan) (targetEnvironment : Env) :
    Except EnvBindingError Bool :=
  match targetEnvironment.pathForScope plan.targetScope with
  | .error fault => .error fault
  | .ok path =>
      .ok (path.take plan.sharedScope.length == mark.coordinates)

/-- Whether any cause-blind mark covers one complete target instance. Structural failure remains explicit and a decisive match stops the scan. -/
def coversAny (plan : ParallelComputationMarkPlan)
    (targetEnvironment : Env) :
    List (ParallelComputationMark plan) →
      Except EnvBindingError Bool
  | [] => pure false
  | mark :: marks => do
      if ← plan.covers mark targetEnvironment then
        pure true
      else
        plan.coversAny targetEnvironment marks

end ParallelComputationMarkPlan

end A12Kernel
