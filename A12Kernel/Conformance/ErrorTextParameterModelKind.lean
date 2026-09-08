import A12Kernel.Elaboration.ErrorTextParameterModelKind

/-! # Locks on the model-kind gate over the `#` message parameters

`INVALID_HASH_LFDNR_FOR_PARALLEL_ITERATION` is measured with its admitted control; the four H-model-side
classes are source-derived and unwitnessed from this project's A12-only route, which the shadowing law
explains rather than excuses
([checkpoint](../../docs/SOURCES.md#src-message-parameter-surface-and-iteration-gates)).

The matrix separates the kind test from the iteration test it precedes, the serial parameter's
independence from the kind, the suppression asymmetry an unparsed condition creates between neighbours,
and the two gates' opposite directions.
-/

namespace A12Kernel.Conformance.ErrorTextParameterModelKind

open A12Kernel

private def key? (kind : ModelKind) (iteration : ConditionIteration) (parameter : HashParameter) :
    Option String :=
  (hashParameterRefusal kind iteration parameter).map KernelStaticDiagnostic.kernelCode

private def pathKey? (kind : ModelKind) (slash : Bool) : Option String :=
  (pathSpecRefusal kind slash).map KernelStaticDiagnostic.kernelCode

/- **The kind test precedes the iteration test, so the same condition reports two different classes in
   the two worlds.** One `ConditionIteration` read four ways: the iteration class appears only on the
   H-model, and only when that iteration is absent. -/
example :
    key? .a12 {} .line = some "PARAM_INVALID_IN_NEW_WORLD" ∧
      key? .hModel {} .line = some "NO_Z_ITERATION" ∧
      key? .hModel { lineIteration := true } .line = none ∧
      key? .a12 { lineIteration := true } .line = some "PARAM_INVALID_IN_NEW_WORLD" := by
  native_decide

/- **The sub-scope parameter has its own class and its own iteration flag**, so the two iteration
   parameters are not one mechanism reported twice: each condition flag moves only its own parameter. -/
example :
    key? .hModel {} .subScope = some "NO_U_ITERATION" ∧
      key? .hModel { subScopeIteration := true } .subScope = none ∧
      key? .hModel { subScopeIteration := true } .line = some "NO_Z_ITERATION" ∧
      key? .hModel { lineIteration := true } .subScope = some "NO_U_ITERATION" := by
  native_decide

/- **The serial parameter reads neither the model kind nor its own iteration.** Both worlds agree on
   every row, and the two iteration flags that move its neighbours leave it alone. -/
example :
    key? .a12 { parallelIteration := true } .serial =
        some "INVALID_HASH_LFDNR_FOR_PARALLEL_ITERATION" ∧
      key? .hModel { parallelIteration := true } .serial =
        some "INVALID_HASH_LFDNR_FOR_PARALLEL_ITERATION" ∧
      key? .a12 {} .serial = none ∧
      key? .a12 { lineIteration := true, subScopeIteration := true } .serial = none := by
  native_decide

/- **The measured pair.** A parallel-iterating condition refuses the serial parameter, and the identical
   parameter under a non-parallel condition is admitted — the control that keeps the class on the
   condition's shape rather than on the parameter. -/
example :
    key? .a12 { parallelIteration := true } .serial =
        some "INVALID_HASH_LFDNR_FOR_PARALLEL_ITERATION" ∧
      key? .a12 { parallelIteration := false } .serial = none := by
  native_decide

/- **The suppression asymmetry.** An unparsed condition admits the serial parameter and every H-model
   iteration parameter, while the A12 world refusal stands — so on an A12 model a broken condition
   changes one neighbour's verdict and not the other's. -/
example :
    key? .a12 { parsed := false, parallelIteration := true } .serial = none ∧
      key? .a12 { parsed := false } .line = some "PARAM_INVALID_IN_NEW_WORLD" ∧
      key? .hModel { parsed := false } .line = none ∧
      key? .hModel { parsed := false } .subScope = none := by
  native_decide

/- **The two gates point in opposite directions**, which is what stops the model kind being read as a
   feature switch: the slash-bearing name is refused in exactly the world that admits the `#` iteration
   parameters, and admitted in the one that refuses them. -/
example :
    pathKey? .hModel true = some "INVALID_PATH_SPEC" ∧
      pathKey? .a12 true = none ∧
      pathKey? .hModel false = none ∧
      key? .a12 {} .line = some "PARAM_INVALID_IN_NEW_WORLD" := by
  native_decide

end A12Kernel.Conformance.ErrorTextParameterModelKind
