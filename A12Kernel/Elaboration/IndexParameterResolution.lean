import A12Kernel.Elaboration.StaticDiagnostic

/-! # Resolving an `index(...)` message parameter, and the repeatability it must agree with

An error message may name a repeatable group's index field. Before the parameter's suffix is read at
all, the Kernel resolves *which* index field the short name means and then cross-checks it against
every index field the **rule's own condition** references under that same name. This module owns those
two stages; the suffix stage that follows them is a separate responsibility.

**The class vocabulary here is prefix-free, and one member collides by sight with a declaration
class.** `INVALID_INDEX_FIELD` is the error-text checker's; `MVK_INVALID_INDEX_FIELD` is the model's own
index-field declaration refusal, owned by [`IndexAndSortDeclaration`](IndexAndSortDeclaration.lean).
A consumer matching on the code must not treat them as one.

**Resolution looks only at the error field's own path.** The candidate set is the index fields lying on
that path, filtered by the parameter's short name: none refuses, several refuse under their own class,
and exactly one resolves. Then the *resolved field's own group* is tested for a composed index. So all
three resolution classes are decided without consulting the condition.

**The repeatability stage is the one that reads the condition, and its central class means disagreement
rather than a state.** The Kernel branches on whether the resolved index field's group repeats, and
raises `INVALID_INDEX_FIELD_REP` from *both* branches in opposite directions — a repeatable referenced
field under a non-repeatable error path, and a non-repeatable one under a repeatable error path. An
account that reads the class as "something repeats that should not" gets one of the two directions
backwards.

**The other two classes live one per branch, so they are mutually exclusive by construction.** Only a
repeatable error path can produce `INVALID_INDEX_FIELD_REP_ITER`, and only a non-repeatable one can
produce `INVALID_INDEX_FIELD_NONREP_ENUM`; no model reports both, and which is even reachable is fixed
before the condition is examined. `indexFieldClassesExclusive` proves it.

**An empty referenced set skips the stage entirely.** When the condition references no index field of
that short name the scan has nothing to reject, which is why a parameter can be admitted beside a
condition that never mentions the index field it names.

**Evidence.** The resolution classes, `INVALID_INDEX_FIELD_REP_ITER`, and the non-repeatable branch's
admitting shape are measured
([resolution and cross-check](../../docs/SOURCES.md#src-index-terminal-refusal-classes),
[non-repeatable gate](../../docs/SOURCES.md#src-nonrepeatable-index-field-gate)).
`INVALID_INDEX_FIELD_COMPOSED_INDEX` and `INVALID_INDEX_FIELD_REP` are **source-derived and unwitnessed**:
the first needs a group declaring several index-field names, which the A12 model surface has no spelling
for, and the second needs a repeatability disagreement that survives the gates before it. The
Enumeration conjunct inside the non-repeatable shape is likewise read rather than measured, because only
an Enumeration may declare a value set or an s-value at all — recorded with its denominator at the second
checkpoint.

This module carries no rendered message text, by the licensing boundary in [`CLAUDE.md`](../../CLAUDE.md).
-/

namespace A12Kernel

/-- An index field's declared type, as the non-repeatable gate reads it.

`other` carries no value count because no non-Enumeration field type may declare one; that is the model
format's constraint and not a simplification, which is why the gate's Enumeration conjunct cannot be
separated by observation. -/
inductive IndexFieldType where
  /-- An Enumeration declaring `valueCount` legal values, with its s-value set or not. -/
  | enumeration (valueCount : Nat) (sValueSet : Bool)
  /-- Any other field type. -/
  | other
  deriving Repr, DecidableEq

/-- **The non-repeatable branch's admitting shape.** The Kernel tests that the s-value is *set*, never
that it names the declared value; the stronger reading is unreachable because a non-member s-value is
refused by the model gate before any parameter is examined. -/
def IndexFieldType.admitsNonRepeatable : IndexFieldType → Bool
  | .enumeration valueCount sValueSet => valueCount == 1 && sValueSet
  | .other => false

/-- An index field the **condition** references under the parameter's short name. -/
structure ReferencedIndexField where
  /-- Its own group repeats. -/
  repeatable : Bool := true
  /-- Its read is an iteration or a parallel iteration, rather than a plain or keyed one. -/
  iterating : Bool := true
  /-- Its declared type, consulted only on the non-repeatable branch. -/
  fieldType : IndexFieldType := .other
  deriving Repr, DecidableEq

/-- What the error field's own path offers for the parameter's short name. -/
structure ErrorPathIndexFields where
  /-- Index fields on that path carrying the short name. -/
  matching : Nat := 1
  /-- Index-field names declared by the resolved field's own group. -/
  declaredNamesOnGroup : Nat := 1
  /-- That group repeats, which selects the whole repeatability branch below. -/
  groupRepeatable : Bool := true
  deriving Repr, DecidableEq

/-- **Stage one, decided without the condition.** First match wins, but only one of the two orderings
here is observable: the empty and the several-candidate guards are disjoint, so their relative order
carries no meaning and no case pins it. What *is* observable is that both outrank the composed-index
test, which a path can satisfy at the same time. -/
def resolutionRefusal (path : ErrorPathIndexFields) : Option KernelStaticDiagnostic :=
  if path.matching == 0 then some .indexFieldUnresolved
  else if path.matching > 1 then some .indexFieldAmbiguous
  else if path.declaredNamesOnGroup > 1 then some .indexFieldComposedIndex
  else none

/-- **Stage two, for one referenced index field.** The mismatch test is symmetric in the two
repeatability flags, which is what makes its class a statement about disagreement; only once they agree
does the branch-specific check run. -/
def repeatabilityRefusal (errorPathRepeatable : Bool) (referenced : ReferencedIndexField) :
    Option KernelStaticDiagnostic :=
  if referenced.repeatable != errorPathRepeatable then some .indexFieldRepeatabilityMismatch
  else if errorPathRepeatable then
    if referenced.iterating then none else some .indexFieldNotIterating
  else if referenced.fieldType.admitsNonRepeatable then none
  else some .indexFieldNonRepeatableEnum

/-- **The scan over the condition's referenced set**, first refusal wins. The Kernel walks the set in a
deterministic name order; this clause takes the order as given, because the order is observable only
through *which* refusal a multiply-offending condition reports. -/
def repeatabilityScan (errorPathRepeatable : Bool) :
    List ReferencedIndexField → Option KernelStaticDiagnostic
  | [] => none
  | referenced :: rest =>
      match repeatabilityRefusal errorPathRepeatable referenced with
      | some refusal => some refusal
      | none => repeatabilityScan errorPathRepeatable rest

/-- **Both stages behind the availability gate.** With no parsed condition the checker returns before
resolving anything, so every refusal here is suppressed — the same gate the row-index parameter sits
behind, and the reason an unparseable condition admits parameters it would otherwise refuse. -/
def indexParameterRefusal (conditionAvailable : Bool) (path : ErrorPathIndexFields)
    (referenced : List ReferencedIndexField) : Option KernelStaticDiagnostic :=
  if !conditionAvailable then none
  else match resolutionRefusal path with
    | some refusal => some refusal
    | none => repeatabilityScan path.groupRepeatable referenced

end A12Kernel
