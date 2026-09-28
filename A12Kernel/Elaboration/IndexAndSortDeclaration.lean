/-! # A repeatable group's index field and sort fields, and the one property that disqualifies both

A repeatable group may nominate one **index field** — the row key that arms `RepetitionNotUnique`, the semantic index, and parallel iteration — and any number of **sort fields** that order its rows for display. Both nominations are checked at code-generation time, and both run the same short cascade: the name must resolve to a direct child field, that field must not switch value validation off, and an index field must additionally not be a table enumeration.

**The disqualifying property is the one [`ValueFormalCheck.lean`](../Semantics/ValueFormalCheck.lean) already owns.** A String declaration that switches value validation off ends the stored-value pipeline before the technical length cap, storing whatever was authored; a field the Kernel never inspects cannot serve as a row key or a sort key, because both need a comparable value. This is that switch's second consumer, and the first one outside the value pipeline.

**The unresolved arm is live; the group arm has no known witness.** A nomination is bound against the model as authored, where a name resolving nowhere fails the build with no class, measured on both roles. It is then judged by the group's direct child field of that short name in the default variant, so a nominated field filtered `ONLY`, or a relative `../Key` that binds to the parent's field while its local namesake is filtered or physically absent, reaches `MVK_INVALID_INDEX_FIELD` and `MVK_INVALID_SORT_FIELD`, filter or no filter ([inbound](../../docs/SOURCES.md#inbound-2026-09-27a-index-and-sort-lookup)); this module's earlier reading of those classes as unreachable was defeated by those two carriers. No row reaches the class through a namesake that is a group, so `NominatedTarget.group` is the source-read arm, not a measured one. The table-enumeration arm inherits [`TableEnumeration.lean`](TableEnumeration.lean)'s constant: no A12 enumeration is a table enumeration, so an index field can never be one.

**The asymmetry worth keeping.** A group carries at most one index field and any number of sort fields, so the index cascade runs once and the sort cascade once per nominated field — but the classes stay distinct per role, which is what lets a consumer say *which* nomination is at fault when a group carries both.

**Evidence.** Both value-validation classes are measured against the real Kernel on hand-authored declarations, alongside an accepted control for each role; the build failure of a nomination resolving nowhere is measured too ([checkpoint](../../docs/SOURCES.md#src-index-and-sort-field-declaration)).

This module carries no rendered message text, by the licensing boundary in [`CLAUDE.md`](../../CLAUDE.md).
-/

namespace A12Kernel

/-- Which of a group's two row-key roles a nomination fills. The cascade is the same; the classes
are not, so a consumer can name the offending nomination. -/
inductive RowFieldRole where
  | indexField
  | sortField
  deriving Repr, DecidableEq

/-- A refusal from the index- or sort-field declaration cascade. -/
inductive RowFieldRefusal where
  /-- The nominated name does not resolve to a direct child field. -/
  | nameUnresolved (role : RowFieldRole)
  /-- The nominated field switches value validation off. -/
  | valueValidationOff (role : RowFieldRole)
  /-- An index field is a table enumeration. Has no sort-field counterpart. -/
  | indexFieldTableEnum
  deriving Repr, DecidableEq

namespace RowFieldRefusal

/-- The exact catalog key. -/
def catalogKey : RowFieldRefusal → String
  | .nameUnresolved .indexField => "MVK_INVALID_INDEX_FIELD"
  | .nameUnresolved .sortField => "MVK_INVALID_SORT_FIELD"
  | .valueValidationOff .indexField => "MVK_INDEX_FIELD_NO_VALUE_VALIDATION"
  | .valueValidationOff .sortField => "MVK_SORT_FIELD_NO_VALUE_VALIDATION"
  | .indexFieldTableEnum => "MVK_INDEX_FIELD_NO_TABLE_ENUM"

/-- Every class of the family. -/
def all : List RowFieldRefusal :=
  [.nameUnresolved .indexField, .valueValidationOff .indexField, .indexFieldTableEnum,
   .nameUnresolved .sortField, .valueValidationOff .sortField]

end RowFieldRefusal

/-- What a nomination resolves to: the group's direct child of the nominated short name in the
default variant. The caller derives it, and nothing here separates that namesake from the field a
relative nomination binds to, although the peer measures that the namesake's declaration decides.
Absence and a non-field both fail the first arm, and they are kept apart because only one of them is
what an author usually wrote. -/
inductive NominatedTarget where
  /-- No direct child of that name. -/
  | unresolved
  /-- A direct child that is a group rather than a field. -/
  | group
  /-- A direct child field, with the two properties the later arms read. -/
  | field (valueValidationOff : Bool) (tableEnumeration : Bool)
  deriving Repr, DecidableEq

/-- One nomination's cascade, first-match-wins. The table-enumeration arm exists only for the index
role, which is why the role is an argument rather than two copies of the function. -/
def rowFieldRefusal (role : RowFieldRole) : NominatedTarget → Option RowFieldRefusal
  | .unresolved => some (.nameUnresolved role)
  | .group => some (.nameUnresolved role)
  | .field valueValidationOff tableEnumeration =>
      if valueValidationOff then some (.valueValidationOff role)
      else if tableEnumeration then
        match role with
        | .indexField => some .indexFieldTableEnum
        | .sortField => none
      else none

/-- A repeatable group's row-key declarations: at most one index nomination, any number of sort
nominations. -/
structure RowFieldDeclarations where
  index : Option NominatedTarget := none
  sort : List NominatedTarget := []
  deriving Repr, DecidableEq

/-- Every refusal the group's declarations draw, index first then the sort nominations in order.
A list rather than a first match, because the two roles are checked independently and a group can be
wrong in both. -/
def rowFieldDeclarationRefusals (declarations : RowFieldDeclarations) : List RowFieldRefusal :=
  (declarations.index.bind (rowFieldRefusal .indexField)).toList ++
    declarations.sort.filterMap (rowFieldRefusal .sortField)

end A12Kernel
