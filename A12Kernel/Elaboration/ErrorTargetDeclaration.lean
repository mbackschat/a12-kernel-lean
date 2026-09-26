import A12Kernel.Elaboration.StaticDiagnostic

/-! # What a rule declares as its error target, and the four gates that declaration passes

Every validation rule names an **error field**: the cell a violation is reported against. It may
additionally name two lists of *error-causing entities*, one used when they are filled and one when
they are not. Those declarations are checked by three separate mechanisms at three different times,
and the resulting eight-class vocabulary is one a rule-authoring or refactoring consumer meets
constantly, because it is the vocabulary of "your rule points somewhere it may not".

**The declaration gate runs before the grammar.** The Kernel checks the error field is set and known
*before* it applies the condition's grammar rule, and it throws rather than reporting. So a rule with
no error field never has its condition parsed at all: whatever syntax errors that text holds are
invisible until an error field is supplied, and a consumer that parses first and validates the
declaration afterwards reports a class the Kernel does not. [`conditionParsed`](#A12Kernel.conditionParsed)
is that fact as a function.

**Lenient parsing excuses only the second of the two.** A missing error field is refused in either
mode; an unknown one is refused only in strict mode. The asymmetry is real and not a rounding of "the
lenient parser is more permissive": the unknown-name test carries the lenient guard and the
absent-declaration test does not.

**The reference partition is three overlapping roles, not three disjoint sets.** After the parse, the
condition's references are sorted by how each stands to the error field: *direct* when it names the
very same entity, *containing* when it is a non-root group at or above it, and *form* when it is the
root group at or above it. An error field that is itself a non-root group makes a direct reference to
it **also** a containing one, which is why the Kernel unions the three sets where a naive reading
would partition them. A consumer that treats them as a partition drops references in exactly that
case.

**The iteration cascade opens only when the condition reaches the error field through its form
alone**, that is when no direct and no containing reference exists. That branch has its own three
classes and its own order, and the branch condition ignores the form references entirely — so a
condition with no references at all enters it too, whenever the whole-rule reference gate was
satisfied by the `AnzahlAngegebenerUSB` escape rather than by a reference.

**The two custom error-entity slots accumulate.** Unlike every gate above, they are not
first-match-wins: a rule whose *if filled* and *if not filled* slots both hold an unreferenced path
draws **both** classes in one run. Each slot reports **once**, carrying all of its offending paths, so
the finding count is the number of offending slots and never the number of offending paths.

**Two carrier facts a consumer gets wrong.** The candidate paths come from the **unexpanded**
condition, deliberately, so a reference that appears only after expansion does not count. And an
H model offers **no** candidates at all, so there every declared path is refused — the same rule text
and the same condition, admitted in one model kind and refused in the other.

**Iteration at a level is not a star in the text.** The cascade tests whether a reference's index at
a level is the iteration marker, and the parse sets that marker for an unstarred per-row read just as
it does for a starred one. Measured: a condition carrying no star anywhere draws the plain-iteration
class, because the rule's own group binds the level
([checkpoint](../../docs/SOURCES.md#src-error-target-declaration)). A consumer that looks for the star
finds nothing and admits the rule.

**Evidence.** Four of the eight classes are measured. The two cascade classes are separated against
each other and against two admitted controls on one model — form-only with a deeper plain iteration
draws the plain class, form-only with a sibling indexed group draws the parallel one, the same
parallel condition with a direct reference added is admitted, and form-only with no deeper iteration
is admitted. The missing-declaration class is measured through a hand-edited model copy, and the
whole-rule reference class has its own retained control. The remaining four have no witness through
any route this project currently has: the unknown-name class needs an error entity that resolves but
is absent from the container, the row-iteration class needs a non-A12 model, and the two custom-slot
classes need a rule property the A12 model format does not carry — a model hand-edited to declare one
fails DM-JSON deserialization outright, which is the measured denominator rather than a claim that no
model can express it ([checkpoint](../../docs/SOURCES.md#src-error-target-declaration)).

The two model-kind guards in the cascade are spelled differently in the Kernel — one tests *not H
model* and the other tests *is A12 model* — and those are the same predicate, so the cascade below
uses one flag for both rather than modelling a third model kind that does not exist.

This module carries no rendered message text, by the licensing boundary in [`CLAUDE.md`](../../CLAUDE.md).
-/

namespace A12Kernel

/-- What the rule's error field amounts to by the time the gate reads it.

`absent` is the Kernel's *error entity is null* state, and it is **wider than "the rule declared
nothing"**: a declared relative path that resolves to no entity lands here too, so an unresolvable
path draws the missing-declaration class rather than the unknown-name one. Measured — a rule whose
path names a nonexistent sibling, and a rule whose path is the empty string, both draw the missing
class ([checkpoint](../../docs/SOURCES.md#src-error-target-declaration)).

`declared` therefore means an error entity object exists, and `knownToModel` is the narrower second
question of whether the model's entity container holds its full name. -/
inductive ErrorFieldDeclaration where
  | absent
  | declared (knownToModel : Bool)
  deriving Repr, DecidableEq

/-- **The declaration gate**, which runs before the condition's grammar. A lenient parse suppresses
the unknown-name class and leaves the absent-declaration class standing. -/
def declarationRefusal (lenient : Bool) : ErrorFieldDeclaration → Option KernelStaticDiagnostic
  | .absent => some .missingErrorField
  | .declared known => if known || lenient then none else some .errorFieldNotValid

/-- Whether the condition text is parsed at all. The declaration gate throws, so its refusal hides
every class the condition itself would report — including plain syntax errors. -/
def conditionParsed (lenient : Bool) (declaration : ErrorFieldDeclaration) : Bool :=
  (declarationRefusal lenient declaration).isNone

/-- One reference the condition makes, as far as the error-target gate reads it. The four facts are
independent inputs rather than a classification, because the roles derived from them overlap.

The list holds only the references outside every filter body and the `$`-marked ones inside: a
body's unmarked read reaches none of these gates
([inbound](../../docs/SOURCES.md#inbound-2026-09-26d-reference-set)). -/
structure ConditionReference where
  /-- Names the very entity the error field names. -/
  sameEntity : Bool := false
  /-- Refers to a group rather than a field. -/
  isGroup : Bool := false
  /-- That group is a root group. -/
  isRootGroup : Bool := false
  /-- Lies at or above the error field on the entity path. -/
  ancestorOrEqual : Bool := false
  deriving Repr, DecidableEq

namespace ConditionReference

/-- A direct reference: same full name. Note it does **not** require `ancestorOrEqual`; equality is
tested on the name alone. -/
def isDirect (reference : ConditionReference) : Bool := reference.sameEntity

/-- A containing reference: a non-root group at or above the error field. -/
def isContaining (reference : ConditionReference) : Bool :=
  reference.isGroup && !reference.isRootGroup && reference.ancestorOrEqual

/-- A form reference: the root group at or above the error field. -/
def isForm (reference : ConditionReference) : Bool :=
  reference.isGroup && reference.isRootGroup && reference.ancestorOrEqual

end ConditionReference

/-- Whether any of the three roles is filled. This is the whole-rule reference gate's subject. -/
def referencesErrorField (references : List ConditionReference) : Bool :=
  references.any fun reference =>
    reference.isDirect || reference.isContaining || reference.isForm

/-- Whether the iteration cascade's branch is taken: no direct and no containing reference. Form
references are **not** consulted, so an empty reference list satisfies this too. -/
def reachedThroughFormAlone (references : List ConditionReference) : Bool :=
  !references.any (fun reference => reference.isDirect) &&
    !references.any (fun reference => reference.isContaining)

/-- The iteration facts the form-only branch reads.

`firstInnerLevel` is the lowest level in the half-open range from one to the error field's level count
that carries plain iteration, meaning an unstarred and unkeyed read of that level among the references
`ConditionReference` admits, so a starred, keyed or unmarked body read carries none; level zero is the root group's own and is deliberately skipped, being
checked further down the cascade. `indexFieldLevel` is the **rule's** index-field level rather than
the offending reference's — the Kernel's guard and its message parameter read two different subjects
through two same-named helpers, and it is the guard's subject that decides. -/
structure IterationProfile where
  /-- Some reference carries row iteration. -/
  rowIteration : Bool := false
  /-- The lowest inner level carrying plain iteration, if any. -/
  firstInnerLevel : Option Nat := none
  /-- Some reference carries parallel iteration. -/
  parallelIteration : Bool := false
  /-- The rule's own index-field level. Zero is the root-group level. -/
  indexFieldLevel : Nat := 0
  deriving Repr, DecidableEq

/-- **The form-only iteration cascade**, split by model kind: the row-iteration class is reachable
only in an H model, and the other two only in an A12 model, so no single model can produce all three.
Clearing the cascade leaves the root-group and sub-scope iteration checks, whose vocabulary this
module does not own.

The two A12 classes are ordered and **the parallel one wins**: a profile carrying an inner plain
level *and* a parallel iteration at a nonzero index-field level answers with
`MVK_ERROR_FIELDGROUP_ITERATION5_INVALID`. This module read it the other way until the peer measured
the pair in both authored text orders, one order alone being unable to separate that precedence from
"the later read decides" ([inbound](../../docs/SOURCES.md#inbound-2026-09-21-corrections)). -/
def formOnlyIterationRefusal (hModel : Bool) (profile : IterationProfile) :
    Option KernelStaticDiagnostic :=
  if hModel then
    if profile.rowIteration then some .errorFieldAndZIterationInvalid else none
  else if profile.parallelIteration && profile.indexFieldLevel > 0 then
    some .errorFieldGroupIteration5Invalid
  else
    match profile.firstInnerLevel with
    | some _ => some .errorFieldGroupIteration4Invalid
    | none => none

/-- Everything the condition-side gates read. -/
structure ErrorTargetInput where
  hModel : Bool := false
  lenient : Bool := false
  declaration : ErrorFieldDeclaration
  references : List ConditionReference := []
  /-- The condition uses the supplied-sub-scope count, which admits an error field no reference
  reaches. It does **not** skip the cascade below, only the reference gate. -/
  anzahlAngegebenerUsb : Bool := false
  iteration : IterationProfile := {}
  deriving Repr

/-- **The condition-side gate in run order**: the declaration before the grammar, the reference gate
after the parse tree exists, then the cascade the form-only branch opens. First-match-wins throughout.
A `none` here is not blanket admission — it means this module's gates are clear and the direct/
containing branch's own vocabulary, owned elsewhere, decides next. -/
def conditionSideRefusal (input : ErrorTargetInput) : Option KernelStaticDiagnostic :=
  match declarationRefusal input.lenient input.declaration with
  | some refusal => some refusal
  | none =>
      if !referencesErrorField input.references && !input.anzahlAngegebenerUsb then
        some .errorFieldNotReferenced
      else if reachedThroughFormAlone input.references then
        formOnlyIterationRefusal input.hModel input.iteration
      else none

/-- One of the two slots naming error-causing entities. -/
inductive CustomErrorEntitySlot where
  | ifFilled
  | ifNotFilled
  deriving Repr, DecidableEq

/-- The class each slot reports. Two classes rather than one because both can arrive together. -/
def CustomErrorEntitySlot.refusal : CustomErrorEntitySlot → KernelStaticDiagnostic
  | .ifFilled => .refErrorEntityIfFilledNotReferenced
  | .ifNotFilled => .refErrorEntityIfNotFilledNotReferenced

/-- The relative paths a rule declares in the two slots. -/
structure CustomErrorEntityDeclaration where
  ifFilled : List String := []
  ifNotFilled : List String := []
  deriving Repr, DecidableEq

namespace CustomErrorEntityDeclaration

/-- The paths declared in one slot. -/
def slot : CustomErrorEntityDeclaration → CustomErrorEntitySlot → List String
  | declaration, .ifFilled => declaration.ifFilled
  | declaration, .ifNotFilled => declaration.ifNotFilled

/-- Whether this check parses the condition. Two empty slots short-circuit before the parse, so a
rule declaring no error-causing entities cannot draw a parse diagnostic from this check — a second
place where a declaration decides whether a condition is read at all. -/
def parsesCondition (declaration : CustomErrorEntityDeclaration) : Bool :=
  !(declaration.ifFilled.isEmpty && declaration.ifNotFilled.isEmpty)

end CustomErrorEntityDeclaration

/-- The candidate relative paths the condition offers. An H model offers none, which refuses every
declared path there regardless of the condition. -/
def candidateRelpaths (hModel : Bool) (fromCondition : List String) : List String :=
  if hModel then [] else fromCondition

/-- The declared paths no candidate matches. Membership is exact string equality against the
candidate set, so two spellings of one entity are two different answers. -/
def unreferencedPaths (candidates declared : List String) : List String :=
  declared.filter fun path => !candidates.contains path

/-- **The custom error-entity gate, which accumulates.** Both slots report in one run, in slot order,
and each reports once however many of its paths offend. A condition that failed to parse suppresses
both, because the check abandons before comparing. -/
def customErrorEntityRefusals (hModel conditionParsed : Bool) (fromCondition : List String)
    (declaration : CustomErrorEntityDeclaration) : List KernelStaticDiagnostic :=
  if !conditionParsed then []
  else
    let candidates := candidateRelpaths hModel fromCondition
    [CustomErrorEntitySlot.ifFilled, CustomErrorEntitySlot.ifNotFilled].filterMap fun slot =>
      if (unreferencedPaths candidates (declaration.slot slot)).isEmpty then none
      else some slot.refusal

end A12Kernel
