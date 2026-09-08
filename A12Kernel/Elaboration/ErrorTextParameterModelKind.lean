import A12Kernel.Elaboration.StaticDiagnostic

/-! # The model kind partitions the `#` message-parameter vocabulary, in both directions

A12 models and H-models are two authoring worlds, and the error-text checker gates parts of the
parameter surface on which one it is looking at. The gate is not a single "H-model features are extra"
rule: each kind forbids something the other allows, and on an A12 model one class **shadows** two
others that a naive reading would expect to see.

**The two iteration `#` parameters test the model kind first, and unconditionally.** `#Zeile` and `#Usb`
each check the kind before anything else and refuse an A12 model outright, so on an A12 model neither
`NO_Z_ITERATION` nor `NO_U_ITERATION` is reachable: both collapse into one class that names the world
rather than the iteration. A consumer that maps a refused `#Zeile` to "the condition does not iterate the
line" is reading an H-model rule into an A12 diagnostic.

**The serial parameter is the exception, and it is a deliberate one with a recorded reason.** `#LfdNr`
carries **no** model-kind gate at all. The Kernel's own note says why: restricting it to serial iteration
would break rules a derived model inherits when that model caps the form's repetition at one — the same
restriction-to-one this project models as the repeatability-restriction refusals. So the parameter stays
legal in both worlds and its single class is about *parallel* iteration instead.

**Those two behaviours also differ in what an unparsed condition does to them**, which is the sharpest
observable split between them. The serial parameter returns early when the checker holds no parsed
condition, so an unparseable condition **admits** it. The kind test has no such guard, so on an A12 model
`#Zeile` is refused whether the condition parsed or not. One parameter is suppressed by a broken
condition and its neighbour is not.

**The path-spec gate runs the other way.** A slash-bearing name in a parameter is refused on an
**H**-model, where paths are not the addressing form, and is ordinary on an A12 model. Taken with the two
above, the model kind is not a feature switch in one direction: each world forbids a spelling the other
requires.

**Evidence.** The parallel-iteration refusal is measured with its admitted control — the identical
parameter from the identical error field under a non-parallel condition
([checkpoint](../../docs/SOURCES.md#src-message-parameter-surface-and-iteration-gates)). The four
H-model-side classes are **source-derived and unwitnessed from this project's A12-only route**, which is
itself the content of the shadowing claim rather than a gap in it: `NO_Z_ITERATION`, `NO_U_ITERATION` and
`INVALID_PATH_SPEC` are unreachable from an A12 document model by construction, and no route here
authors an H-model. `PARAM_INVALID_IN_NEW_WORLD` is the A12-side class and is the one an A12 consumer
actually meets.

This module carries no rendered message text, by the licensing boundary in [`CLAUDE.md`](../../CLAUDE.md).
-/

namespace A12Kernel

/-- Which authoring world the checked model belongs to. -/
inductive ModelKind where
  /-- The older H-model world, where the `#` iteration parameters and the coordinate specifiers live. -/
  | hModel
  /-- The A12 document-model world this project targets. -/
  | a12
  deriving Repr, DecidableEq

/-- The three `#` parameters this gate governs. -/
inductive HashParameter where
  /-- `#Zeile`, the line coordinate. -/
  | line
  /-- `#Usb`, the sub-scope coordinate. -/
  | subScope
  /-- `#LfdNr`, the serial coordinate — the one with no model-kind gate. -/
  | serial
  deriving Repr, DecidableEq

/-- What the checker knows about the rule's condition when it reads a parameter. -/
structure ConditionIteration where
  /-- A condition was parsed. When false the serial parameter is not examined at all; the kind test is
  unaffected, which is the two parameters' sharpest observable difference. -/
  parsed : Bool := true
  /-- The condition iterates the line coordinate. -/
  lineIteration : Bool := false
  /-- The condition iterates the sub-scope coordinate. -/
  subScopeIteration : Bool := false
  /-- The condition iterates two sibling groups in parallel. -/
  parallelIteration : Bool := false
  deriving Repr, DecidableEq

/-- **The gate.** The two iteration parameters test the model kind before their own iteration; the serial
parameter tests neither kind nor its own iteration, only whether the condition iterates in parallel. -/
def hashParameterRefusal (kind : ModelKind) (iteration : ConditionIteration) :
    HashParameter → Option KernelStaticDiagnostic
  | .line =>
      match kind with
      | .a12 => some .parameterInvalidInNewWorld
      | .hModel =>
          if iteration.parsed && !iteration.lineIteration then some .noLineIteration else none
  | .subScope =>
      match kind with
      | .a12 => some .parameterInvalidInNewWorld
      | .hModel =>
          if iteration.parsed && !iteration.subScopeIteration then some .noSubScopeIteration else none
  | .serial =>
      if !iteration.parsed then none
      else if iteration.parallelIteration then some .serialParameterInParallelIteration
      else none

/-- **The opposite-direction gate.** A slash-bearing name is the ordinary addressing form on an A12
model and is refused on an H-model. -/
def pathSpecRefusal (kind : ModelKind) (nameCarriesSlash : Bool) : Option KernelStaticDiagnostic :=
  match kind with
  | .hModel => if nameCarriesSlash then some .pathSpecNotAllowed else none
  | .a12 => none

end A12Kernel
