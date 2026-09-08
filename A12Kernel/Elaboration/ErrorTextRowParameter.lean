import A12Kernel.Elaboration.StaticDiagnostic

/-! # The error-text row-index parameter, and the condition it silently depends on

An error message may interpolate a repeatable group's **1-based row index** by naming the group. That
one parameter is checked against the *condition*, not the model alone, and its four-stage cascade is
where a message and a condition are coupled most tightly — change the condition's wildcards and a
message that was legal stops being so.

**The cascade, in order.** The named path must resolve to a group; the condition's references must
accept it; the group must be referenced **without** a star somewhere; and the parameter's semantic
index, if written, must be consistent with the condition's iteration. The first two stages report the
**same code** for two genuinely different causes — a path that names nothing, and a path that names a
group the condition does not reach — so that code is many-to-one and a repair tool cannot tell from
it which of the two to fix.

**The star rule asks whether an unstarred reference exists, not whether every reference is
unstarred.** A condition holding both a starred and an unstarred reference to the same group admits
the parameter; only a group reached exclusively through a star refuses. Measured, with the
starred-only and both-references rows differing in one added conjunct
([checkpoint](../../docs/SOURCES.md#src-error-text-row-parameter)).

**The last stage's class is chosen by the parameter's own spelling, not by the failure.** One check
decides both, and it reports the semantic-index class when the parameter wrote a semantic index and
the iteration class when it did not — so the two codes do not name two conditions.

**The whole cascade is skipped when the condition is unavailable.** If the checker holds no parsed
condition it returns without examining the parameter at all, so an unparseable condition *admits*
every row parameter it would otherwise refuse. The same unparseable condition separately produces the
`INVALID_CONDITION` finding — and that finding is **accumulated beside** the other error-text results
rather than replacing them, so a consumer sees both an "unchecked" report and a clean parameter list
and must not read the second as an endorsement.

**The trigger for all of this is the character `$`, not a parameter.** The Kernel decides whether it
needs the condition by testing whether any message contains a dollar sign, and its own source records
that this **also flags an escaped `$$`**. A message whose only dollar is an escaped literal therefore
drags the condition into the check and can draw `INVALID_CONDITION` while containing no parameter at
all.

**Evidence.** The star rule is measured with four separating rows, including the both-references row
that identifies the rule and a plain-message control that keeps the class on the parameter rather than
the condition; the resolve stage's class is measured on an undeclared group
([checkpoint](../../docs/SOURCES.md#src-error-text-row-parameter)). `INVALID_CONDITION` has **no
witness**: neither the candidate-rule gate nor the whole-model gate surfaces it — both stop at the
condition's own parse class — so the escaped-dollar quirk is recorded from the Kernel's own source
note and not from an observation. `INVALID_PATH_SPEC_IN_PARAMETER` is guarded on a non-A12 model and
is unreachable through this project's A12-only route by construction.

This module carries no rendered message text, by the licensing boundary in [`CLAUDE.md`](../../CLAUDE.md).
-/

namespace A12Kernel

/-- How the condition references the group a row parameter names. The three facts are independent
because the star rule is existential over the condition's references. -/
structure GroupReferenceProfile where
  /-- The path resolves to a group in the model. -/
  resolvesToGroup : Bool := true
  /-- The condition's references accept the group as a row parameter's subject at all. -/
  admittedByCondition : Bool := true
  /-- Some reference to the group carries no star. -/
  referencedWithoutStar : Bool := true
  /-- The parameter's iteration, semantic index included, is consistent with the condition's. -/
  iterationConsistent : Bool := true
  deriving Repr, DecidableEq

/-- What the parameter itself wrote. -/
structure RowParameterSpelling where
  /-- The parameter carries a semantic index. This chooses the last stage's class and nothing else. -/
  hasSemanticIndex : Bool := false
  deriving Repr, DecidableEq

/-- **The four-stage cascade**, first-match-wins, run only when a parsed condition is available.
Stages one and two share a code; stage four's code is chosen by the spelling. -/
def rowParameterRefusal (profile : GroupReferenceProfile) (spelling : RowParameterSpelling) :
    Option KernelStaticDiagnostic :=
  if !profile.resolvesToGroup then some .invalidGroupInParameter
  else if !profile.admittedByCondition then some .invalidGroupInParameter
  else if !profile.referencedWithoutStar then some .iterParamWithStarReference
  else if !profile.iterationConsistent then
    if spelling.hasSemanticIndex then some .invalidUseOfSemanticIndex
    else some .invalidUseOfIterationParam
  else none

/-- **The cascade behind its availability gate.** With no parsed condition the parameter is not
examined, so every refusal above is suppressed and the parameter is admitted. -/
def rowParameterOutcome (conditionAvailable : Bool) (profile : GroupReferenceProfile)
    (spelling : RowParameterSpelling) : Option KernelStaticDiagnostic :=
  if conditionAvailable then rowParameterRefusal profile spelling else none

/-- Whether a message drags the condition into the error-text check. The Kernel's test is the
character, so an escaped literal dollar counts — its own source records the false positive. -/
def messageNeedsCondition (containsDollar : Bool) : Bool := containsDollar

/-- **The whole error-text check for one rule.** The condition finding accumulates beside the other
findings rather than replacing them: the Kernel reports it and then runs the error-text checker
anyway, deliberately, so that every check not needing the condition still contributes.

`conditionIndependentFindings` stands for those other checks' results. It is an input rather than a
clause because this module owns only the row-index parameter; without it the accumulation would be
unobservable here, since the one check modelled below is exactly the one an unparsed condition
suppresses. -/
def errorTextFindings (containsDollar conditionParses : Bool)
    (conditionIndependentFindings : List KernelStaticDiagnostic)
    (profile : GroupReferenceProfile) (spelling : RowParameterSpelling) :
    List KernelStaticDiagnostic :=
  let needsCondition := messageNeedsCondition containsDollar
  -- The checker holds a condition **only** when a message's dollar caused one to be parsed. No
  -- dollar means no parse was attempted, so the cascade is skipped for that reason too.
  let conditionAvailable := needsCondition && conditionParses
  (if needsCondition && !conditionParses then [KernelStaticDiagnostic.errorTextInvalidCondition]
    else []) ++ conditionIndependentFindings ++
    (rowParameterOutcome conditionAvailable profile spelling).toList

end A12Kernel
