import A12Kernel.Elaboration.IndexGroupResolution

/-! # In what order the Kernel refuses a semantic-index operand

`[Field For key]` selects a row of an indexed group by the *value* of its index field rather than by
position. One checker admits it, and it is a **strict first-hit cascade**: every gate throws
immediately, so a site offending several reports exactly the earliest. Thirteen positions, seven of
whose classes already have owners here, are threaded into one function because the order is the
semantic content — a consumer that runs the gates as independent predicates gets the right set and
the wrong answer.

**The key has two arms and they are not symmetric.** A key is either a reference to another field or
a string constant, and *five* of the classes are reachable from one arm only: not-a-field, a starred
key, a category suffix and the no-value-validation refusal need a reference, while the invalid-key
class needs a constant. So a grid built entirely from constant keys cannot see four of these gates at
all, and one built from references cannot see the fifth. That is a **forced axis** of the construct,
not an omission in any fixture.

**Two different classes are both about a wildcard, and they sit at opposite ends.** A star on the
*key reference* is caught first, before anything about the value spec has been looked at; a star on
the *value spec itself*, at the index group's own level, is caught last, after every other gate has
passed. A consumer treating "semantic index and wildcard" as one rule reports the wrong class and the
wrong precedence together.

**The empty constant is refused by its own disjunct**, written beside the type test rather than
through it, so a key type that would accept the empty string still refuses it here.

**One gate is silenced by a lenient parse** — the no-value-validation refusal — so a lenient reader
sees twelve positions where a strict one sees thirteen.

**A key written with its own filter is outside this cascade.** An entity key takes a `Having` of its
own, while a string key takes none, so a `Having` after it is the operand's. On the key's filter a
group key draws the kind class, a refused comparison or an iteration the filter does not cover in its
body answers ahead of stage A even on a starred key, and an unstarred key draws the filter's star
class ahead of the last stage. The peer measures these, and no input here carries a filter
([inbound](../../docs/SOURCES.md#inbound-2026-09-25c-key-filter)).

This capsule owns the **order**. Resolution of the index group itself belongs to
[`IndexGroupResolution`](IndexGroupResolution.lean) and is consumed whole rather than restated; the
value *lookup* a semantic index performs once admitted belongs to
[`SemanticIndex`](SemanticIndex.lean). Neither is re-implemented here.

**One catalog key in this family is deliberately not a diagnostic.** `MVK_SEMANTIC_INDEX_REF_OP` is
substituted into the no-value-validation message as the name of the offending operation; the Kernel's
own error documentation marks it not relevant, its German entry is a placeholder, and its only use is
that substitution. Registering it as a refusal class would assert a refusal that does not exist.

**Evidence.** The order is read from the Kernel's semantic-index checker and its two entity helpers.
Which of its classes and orders carry Kernel rows is owned by the
[implementation map](../../docs/implementation/cross-clause.md#cap-semantic-index-admission). This
module carries no rendered message text, by the licensing boundary in [`CLAUDE.md`](../../CLAUDE.md).
-/

namespace A12Kernel

/-- A key written as a reference to another field, as far as the cascade reads it. -/
structure SemanticIndexAdmissionKeyRef where
  /-- Whether the named entity resolves to a field rather than to a group. -/
  resolvesToField : Bool := true
  /-- Whether the reference carries a wildcard at any level. -/
  starred : Bool := false
  /-- Whether its base type matches the index field's. Deriving base-type agreement is the field-kind
  family's work; this gate consumes the verdict. -/
  baseTypeMatchesIndexField : Bool := true
  /-- Whether the key entity lies at or below the group it would index, which is the circularity the
  cascade refuses. -/
  containedInIndexGroup : Bool := false
  /-- Whether any field the reference expands to is declared to carry no value validation. -/
  expandsToNoValueValidation : Bool := false
  /-- Whether the reference carries a category suffix. -/
  carriesCategory : Bool := false
  deriving Repr, DecidableEq

/-- The two ways a semantic index's key may be written. -/
inductive SemanticIndexAdmissionKey where
  /-- `[A For B]` — a reference to another field. -/
  | reference (spec : SemanticIndexAdmissionKeyRef)
  /-- `[A For "k"]` — a string constant, paired with whether the index field's type accepts it. For a
  String index field that verdict is a conjunction of the declared length bounds and the declared
  pattern, either failing refuses the key, and the pattern is matched against the whole key over code
  points ([inbound](../../docs/SOURCES.md#inbound-2026-09-26m-index-key-pattern)). -/
  | constant (text : String) (applicableToIndexField : Bool)
  deriving Repr, DecidableEq

/-- The value spec's own situation, independent of how the key was written. -/
structure SemanticIndexAdmissionSite where
  /-- Whether the value spec is itself a semantic index. -/
  valueSpecIsSemanticIndex : Bool := false
  /-- The groups on the value spec's upward path, innermost first, for the settled walk in
  [`IndexGroupResolution`](IndexGroupResolution.lean). -/
  indexPath : List IndexDeclaringGroup := []
  /-- Whether the value spec carries a wildcard at the index group's **own** level. -/
  starredAtIndexLevel : Bool := false
  /-- Whether the parse is lenient, which silences exactly one gate below. -/
  lenient : Bool := false
  deriving Repr, DecidableEq

/-- **Stage A — the key reference's own shape**, checked before anything about the value spec. A
constant key skips the stage entirely. -/
def keyShapeRefusal : SemanticIndexAdmissionKey → Option KernelStaticDiagnostic
  | .constant _ _ => none
  | .reference r =>
      if !r.resolvesToField then some .semanticIndexKeyNotField
      else if r.starred then some .semanticIndexKeyStarred
      else none

/-- **Stage D — the key against the resolved index field**, which is the one stage where the two arms
report different classes for the same disagreement. The constant arm's empty test is a separate
disjunct, so an accepting type does not rescue an empty key. -/
def keyAgreementRefusal : SemanticIndexAdmissionKey → Option KernelStaticDiagnostic
  | .reference r =>
      if r.baseTypeMatchesIndexField then none else some .indexTypeInconsistent
  | .constant text applicable =>
      if !applicable || text.isEmpty then some .semanticIndexConstantInvalid else none

/-- **Stage F — the two remaining reference-arm gates**, in the Kernel's order: the value-validation
refusal, which a lenient parse skips, then the category suffix. -/
def keyUsageRefusal (lenient : Bool) : SemanticIndexAdmissionKey → Option KernelStaticDiagnostic
  | .constant _ _ => none
  | .reference r =>
      if !lenient && r.expandsToNoValueValidation then some .rawTypeOperandInvalid
      else if r.carriesCategory then some .semanticIndexKeyWithCategory
      else none

/-- Whether the key lies inside the group it would index. A constant key has no locus, so the
circularity gate cannot fire on that arm. -/
def keyContainedInIndexGroup : SemanticIndexAdmissionKey → Bool
  | .constant _ _ => false
  | .reference r => r.containedInIndexGroup

/-- **The whole cascade, first hit wins.** Composed with the settled index-group walk rather than
restating it: that walk's own three classes enter at stage C exactly as the Kernel raises them, and
an absent index group is this cascade's `noIndexField` rather than the walk's business. -/
def semanticIndexAdmissionRefusal (site : SemanticIndexAdmissionSite) (key : SemanticIndexAdmissionKey) :
    Option KernelStaticDiagnostic :=
  match keyShapeRefusal key with
  | some refusal => some refusal
  | none =>
      if site.valueSpecIsSemanticIndex then some .semanticIndexOnSemanticIndex
      else match indexResolution site.indexPath with
        | .error refusal => some refusal
        | .ok none => some .noIndexField
        | .ok (some _) =>
            match keyAgreementRefusal key with
            | some refusal => some refusal
            | none =>
                if keyContainedInIndexGroup key then some .semanticIndexContainedInIndex
                else match keyUsageRefusal site.lenient key with
                  | some refusal => some refusal
                  | none =>
                      if site.starredAtIndexLevel then some .semanticIndexAndWildcard else none

/-- Whether a site admits its key outright. -/
def semanticIndexSiteAdmitted (site : SemanticIndexAdmissionSite) (key : SemanticIndexAdmissionKey) : Bool :=
  (semanticIndexAdmissionRefusal site key).isNone

end A12Kernel
