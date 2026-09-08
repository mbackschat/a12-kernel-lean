import A12Kernel.Elaboration.StaticDiagnostic

/-! # When an entity is renamed or moved, what happens to the rules that name it

The Kernel offers a **rule-change service**: given a rule and an entity's old and new full names, it
returns the rule's condition text and its error messages with the references rewritten. This is the
machinery a rename or a move in a model editor runs, and it is the one place in the Kernel's
vocabulary that speaks to a *transformation* consumer rather than a validating one — a rule-refactoring
tool must reproduce not only what the service rewrites but what it declines to.

**It declines a move in an A12 model, and it declines it twice with two different names.** The
condition entry point reports one class and the error-text entry point another, for the identical
situation, so a caller can tell which surface refused. A **rename** in the same model is propagated
normally, which is what makes this a policy about moves rather than a limit on rewriting.

**The two entry points do not agree on what they look at first, and that is observable.** The
condition side resolves the old name in the model's entity container and, when it finds nothing,
returns the text **unchanged** — deliberately, for a rule name or an unknown entity. The error-text
side never consults the container at all. So one and the same request is a silent no-op on the
condition and a refusal on the error text, and a consumer that runs one and infers the other is
wrong on exactly those inputs.

**Their parse gates differ too.** The condition side always parses the condition first, so an
unparseable condition abandons the request before the move is ever considered. The error-text side
parses **only when some message carries a parameter**, so a rule with plain messages never reads its
condition here and an unparseable condition is invisible. The error-text side additionally validates
the messages before the move gate, so an invalid message hides the move refusal the same way.

**Three outcomes, not two, and the middle one is the trap.** A request may be rewritten, returned
*unchanged*, or refused. `unchanged` is not a quiet success: on the unknown-name arm the references
were not examined, and a consumer treating it as "nothing needed updating" will leave stale
references behind. The one arm where `unchanged` is genuinely correct is an H model's moved,
un-renamed field, because H-model conditions name fields by short name and a move does not change one.

**Rename-and-move is not rename-then-move.** A single change that alters both the parent and the
short name is a move, so in an A12 model it is refused outright and the rename half is not propagated
either — where the same rename alone would have been.

**Evidence.** Source-derived. `dmtool`'s own `field move` **does** rewrite conditions, error-field
relative paths and message parameters, and the result passes the Kernel's model check — measured — so
an independent implementation performs the propagation this service declines
([checkpoint](../../docs/SOURCES.md#src-rule-change-propagation)). That measurement establishes the
rewrite is possible and sound, not that the Kernel behaves differently: `dmtool` reaches the model
through its own editor rather than through this service, so neither class has a witness on that route
and both are stated here as the total function the Kernel computes.

This module carries no rendered message text, by the licensing boundary in [`CLAUDE.md`](../../CLAUDE.md).
-/

namespace A12Kernel

/-- What a change did to an entity's full name. The two axes are independent: a change may move,
rename, do both, or — when the names agree — neither. -/
structure NameChange where
  /-- The parent path differs. This is the Kernel's notion of a **move**. -/
  parentChanged : Bool := false
  /-- The last path segment differs. This is a **rename**. -/
  shortNameChanged : Bool := false
  deriving Repr, DecidableEq

/-- The identity change: neither axis moved. -/
def NameChange.isIdentity (change : NameChange) : Bool :=
  !change.parentChanged && !change.shortNameChanged

/-- What one entry point did with the request. -/
inductive PropagationOutcome where
  /-- References were rewritten to the new name. -/
  | rewritten
  /-- The text was returned as it stood, deliberately. **Not** a quiet success on every arm — see the
  module note. -/
  | unchanged
  /-- The service reported a class and returned nothing. -/
  | refused (diagnostic : KernelStaticDiagnostic)
  /-- The request was abandoned before the move gate, by a failure this family does not name. -/
  | abandoned
  deriving Repr, DecidableEq

/-- What the condition entry point reads. -/
structure ConditionRequest where
  hModel : Bool := false
  /-- The condition parsed. The gate runs first, so a failure hides everything below it. -/
  conditionParses : Bool := true
  /-- The model's entity container resolves the **old** name. A rule name, or an entity the container
  does not hold, is `false`. -/
  oldNameKnown : Bool := true
  /-- The moved entity is a field rather than a group. Read only on the H-model arm. -/
  isField : Bool := false
  change : NameChange := {}
  deriving Repr

/-- **The condition entry point**, in run order. -/
def conditionPropagation (request : ConditionRequest) : PropagationOutcome :=
  if !request.conditionParses then .abandoned
  else if !request.oldNameKnown then .unchanged
  else if request.change.parentChanged then
    if !request.hModel then .refused .entityMoveInA12ModelCondition
    else if !request.change.shortNameChanged && request.isField then .unchanged
    else .rewritten
  else if request.change.shortNameChanged then .rewritten
  else .unchanged

/-- What the error-text entry point reads. It consults **no** entity container. -/
structure ErrorTextRequest where
  hModel : Bool := false
  /-- Some message carries an interpolated parameter, which is the only reason this side parses the
  condition at all. -/
  messageUsesParameter : Bool := false
  conditionParses : Bool := true
  /-- The messages pass the Kernel's error-text checker. -/
  errorTextValid : Bool := true
  change : NameChange := {}
  deriving Repr

/-- **The error-text entry point**, in run order. Its parse gate is conditional and its validity gate
is not, and both precede the move gate. -/
def errorTextPropagation (request : ErrorTextRequest) : PropagationOutcome :=
  if request.messageUsesParameter && !request.conditionParses then .abandoned
  else if !request.errorTextValid then .abandoned
  else if !request.hModel && request.change.parentChanged then
    .refused .entityMoveInA12ModelErrortext
  else .rewritten

/-- The class an outcome reports, if any. -/
def PropagationOutcome.diagnostic? : PropagationOutcome → Option KernelStaticDiagnostic
  | .refused diagnostic => some diagnostic
  | _ => none

/-- Whether the outcome leaves the rule's references pointing at the old name. Both a refusal and an
`unchanged` do; only a rewrite does not. This is the projection a refactoring consumer needs, because
the two non-rewriting outcomes differ in whether anything was *reported*. -/
def PropagationOutcome.leavesStaleReferences : PropagationOutcome → Bool
  | .rewritten => false
  | _ => true

end A12Kernel
