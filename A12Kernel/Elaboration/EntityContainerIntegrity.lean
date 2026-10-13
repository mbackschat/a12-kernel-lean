/-! # The per-entity integrity cascade, whose first four stages hide the whole subtree beneath them

Before generating code the Kernel walks the flattened entity container and checks each entity against
six structural invariants. The stages are **not** uniform, and the difference is the family's whole
content: the first four `return` on failure, so each hides every later stage **and stops the walk from
descending into that entity's children**; the last two report and fall through, so one entity can draw
both of them plus its field-level diagnostics.

**A failure high in the tree therefore silences everything below it.** That is the static counterpart
of the over-repetition subtree suppression, and it means the diagnostic set is not monotone in the
model: fixing one entity's path can reveal many further errors that were always there.

**The two max-value stages are independent despite sharing a test.** Both begin by rejecting an absent
maximum, and the second even carries a comment noting the duplication — so an absent maximum draws
both codes. A *present but non-positive* maximum draws only the first, measured: a root group declared
with repeatability zero draws the invalid-maximum code on **every** entity of the model, eight of
eight, and the inconsistency code on none, because a uniformly zero tree is still internally
consistent ([checkpoint](../../docs/sources/model-structure-and-declaration-probes.md#src-entity-container-integrity)).

**The path stage reads the entity's *name*, not its identifier.** A root group whose DM-JSON `id`
carries a dash is admitted; the same group with a dashed *name* draws the path class, and both together
draw it too — three variants differing in exactly those two keys. So the identifier a model file uses to
address an entity is not the full name this walk validates, and a reimplementer validating the id
checks the wrong string. A digit-initial name draws an earlier and more specific class instead, so the
path stage is not the first name gate either.

**Three stages test container invariants.** The path-consistency, field-containment and
parent-presence stages compare a path derived from an entity's own name against the one the walk
carried, and look the parent up in the container. A name holding `/` makes the derived path disagree:
a field named `Co/de` draws the path-consistency class (row `pa-slash` of the field-declaration
capture). For the other two stages no witness is known as of Kernel 30.8.1; a model file supplies a
tree from which both sides are derived together, so they are recorded as unknown rather than as
unreachable.

**Two stages are shadowed, each measured.** A field placed among the root groups draws no
integrity class at all: the model fails to load, with a build failure carrying no diagnostic class. And
the two generated-code name stages read the **code generator's** parameters rather than the model, so
they are out of reach from a model file — three model names, including one that fails the name pattern
outright, are all admitted.

**One stage was not reached.** The duplicate dynamic-enumeration stage reads the generator's derivation
list; a model carrying two rules that derive the same target is admitted by the static check, and the
runtime probe reported no derivation block for it. Its identity is modelled and its evidence is absent.

This module carries no rendered message text, by the licensing boundary in [`CLAUDE.md`](../../CLAUDE.md).
-/

namespace A12Kernel

/-- A class the code-generation model check can report about one entity or the container. -/
inductive EntityIntegrityRefusal where
  /-- The entity's full name is not a legal path. -/
  | pathInvalid
  /-- The parent path derived from the name disagrees with the one the walk carried. -/
  | pathsInconsistent
  /-- A field contains entities. -/
  | fieldWithContainedEntities
  /-- The derived parent is not in the container. -/
  | parentEntityMissing
  /-- The maximum-repetition vector is absent or has a non-positive entry. -/
  | maxValuesInvalid
  /-- The maximum-repetition vector disagrees with the parent's. -/
  | maxValuesInconsistent
  /-- A field sits directly among the root groups. -/
  | fieldNoParent
  /-- The generator's artifact name is not legal for generated code. -/
  | invalidNameForGeneratedCode
  /-- The generator's package name is not legal for generated code. -/
  | invalidPackageNameForGeneratedCode
  /-- Two derivations target one dynamic-enumeration field. -/
  | duplicateDynamicEnum
  deriving Repr, DecidableEq

namespace EntityIntegrityRefusal

/-- The exact catalog key. -/
def catalogKey : EntityIntegrityRefusal → String
  | .pathInvalid => "MVK_PATH_INVALID"
  | .pathsInconsistent => "MVK_PATHS_INCONSISTENT"
  | .fieldWithContainedEntities => "MVK_FIELD_WITH_CONTAINED_ENTITIES"
  | .parentEntityMissing => "MVK_PARENT_ENTITY_MISSING"
  | .maxValuesInvalid => "MVK_MAX_VALUES_INVALID"
  | .maxValuesInconsistent => "MVK_MAX_VALUES_INCONSISTENT"
  | .fieldNoParent => "MVK_FIELD_NO_PARENT"
  | .invalidNameForGeneratedCode => "MVK_INVALID_NAME_4_GENERATED_CODE"
  | .invalidPackageNameForGeneratedCode => "MVK_INVALID_PACKAGE_NAME_4_GENERATED_CODE"
  | .duplicateDynamicEnum => "MVK_DUPLICATE_DYNAMIC_ENUM"

/-- Whether the stage stops the entity's check and the walk's descent into its children. The four
blocking stages are what make the diagnostic set non-monotone in the model. -/
def isBlocking : EntityIntegrityRefusal → Bool
  | .pathInvalid | .pathsInconsistent | .fieldWithContainedEntities | .parentEntityMissing => true
  | _ => false

/-- The stages the per-entity cascade runs, in order. The container- and generator-level classes are
not among them. -/
def cascade : List EntityIntegrityRefusal :=
  [.pathInvalid, .pathsInconsistent, .fieldWithContainedEntities, .parentEntityMissing,
   .maxValuesInvalid, .maxValuesInconsistent]

def all : List EntityIntegrityRefusal :=
  cascade ++ [.fieldNoParent, .invalidNameForGeneratedCode, .invalidPackageNameForGeneratedCode,
    .duplicateDynamicEnum]

end EntityIntegrityRefusal

/-- What the cascade reads about one entity. Each field is the *negation* of a stage's failure, named
positively so a well-formed entity is all-true. -/
structure EntityShape where
  pathValid : Bool := true
  pathConsistentWithParent : Bool := true
  /-- False when the entity is a field that contains entities. -/
  fieldContainsNothing : Bool := true
  parentPresent : Bool := true
  maxValid : Bool := true
  maxConsistentWithParent : Bool := true
  deriving Repr, DecidableEq

/-- The first blocking stage the entity fails, if any. -/
def blockingRefusal (shape : EntityShape) : Option EntityIntegrityRefusal :=
  if !shape.pathValid then some .pathInvalid
  else if !shape.pathConsistentWithParent then some .pathsInconsistent
  else if !shape.fieldContainsNothing then some .fieldWithContainedEntities
  else if !shape.parentPresent then some .parentEntityMissing
  else none

/-- **One entity's refusals.** A blocking failure yields exactly that one class; otherwise the two
accumulating stages each report independently, so an entity may draw none, one, or both. -/
def entityIntegrityRefusals (shape : EntityShape) : List EntityIntegrityRefusal :=
  match blockingRefusal shape with
  | some refusal => [refusal]
  | none =>
      (if shape.maxValid then [] else [.maxValuesInvalid]) ++
        (if shape.maxConsistentWithParent then [] else [.maxValuesInconsistent])

/-- Whether the walk descends into this entity's children. -/
def visitsChildren (shape : EntityShape) : Bool :=
  (blockingRefusal shape).isNone

/-- The container as the walk sees it: an entity and the entities directly beneath it.

No `Repr` instance: deriving one for a nested inductive emits an unsafe recursor, which the
environment audit rejects from the trusted library, and nothing here needs to print a tree. -/
inductive EntityTree where
  | node (shape : EntityShape) (children : List EntityTree)

/-- **The whole container's refusals.** A blocking failure contributes its one class and the subtree
beneath it is never visited, which is where the non-monotonicity comes from. -/
def treeIntegrityRefusals : EntityTree → List EntityIntegrityRefusal
  | .node shape children =>
      entityIntegrityRefusals shape ++
        (if visitsChildren shape then children.flatMap treeIntegrityRefusals else [])

/-- An absent maximum-repetition vector fails **both** max stages, because the second repeats the
first's test rather than assuming it. A present non-positive entry fails only the first. -/
def absentMaximumShape : EntityShape :=
  { maxValid := false, maxConsistentWithParent := false }

/-- The measured shape: a declared repeatability of zero. Present, so the consistency stage is
satisfied whenever the parent agrees — which in a uniformly zero tree it does. -/
def nonPositiveMaximumShape : EntityShape := { maxValid := false }

end A12Kernel
