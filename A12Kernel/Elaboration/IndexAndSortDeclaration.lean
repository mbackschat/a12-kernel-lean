import A12Kernel.Elaboration.Flat.Model

/-! # A repeatable group's index field and sort fields, and the one property that disqualifies both

A repeatable group may nominate one **index field** — the row key that arms `RepetitionNotUnique`, the semantic index, and parallel iteration — and any number of **sort fields** that order its rows for display. Both nominations are checked at code-generation time, and both run the same short cascade: the name must resolve to a direct child field, that field must not switch value validation off, and an index field must additionally not be a table enumeration.

**The disqualifying property is the one [`ValueFormalCheck.lean`](../Semantics/ValueFormalCheck.lean) already owns.** A String declaration that switches value validation off ends the stored-value pipeline before the technical length cap, storing whatever was authored; a field the Kernel never inspects cannot serve as a row key or a sort key, because both need a comparable value. This is that switch's second consumer, and the first one outside the value pipeline.

**The unresolved arm is live; the group arm has no known witness.** A nomination is bound against the model as authored, where a name resolving nowhere fails the build with no class, measured on both roles. It is then judged by the group's direct child field of that short name in the default variant, so a nominated field filtered `ONLY`, or a relative `../Key` that binds to the parent's field while its local namesake is filtered or physically absent, reaches `MVK_INVALID_INDEX_FIELD` and `MVK_INVALID_SORT_FIELD`, filter or no filter ([inbound](../../docs/sources/inbound-handbacks.md#inbound-2026-09-27a-index-and-sort-lookup)); this module's earlier reading of those classes as unreachable was defeated by those two carriers. No row reaches the class through a namesake that is a group, so `NominatedTarget.group` is the source-read arm, not a measured one. The table-enumeration arm inherits [`TableEnumeration.lean`](TableEnumeration.lean)'s constant: no A12 enumeration is a table enumeration, so an index field can never be one.

**The asymmetry worth keeping.** A group carries at most one index field and any number of sort fields, so the index cascade runs once and the sort cascade once per nominated field — but the classes stay distinct per role, which is what lets a consumer say *which* nomination is at fault when a group carries both.

**Evidence.** Both value-validation classes are measured against the real Kernel on hand-authored declarations, alongside an accepted control for each role; the build failure of a nomination resolving nowhere is measured too ([checkpoint](../../docs/sources/model-structure-and-declaration-probes.md#src-index-and-sort-field-declaration)).

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
  /-- A sort list naming one field more than once among its first three entries. A judgement of the
  list, so it is reported once however many names repeat. -/
  | sortFieldDuplicate
  /-- A sort list of more than three entries. The Kernel's notification carries no code. -/
  | sortListCapacity
  deriving Repr, DecidableEq

namespace RowFieldRefusal

/-- The exact catalog key, `none` for the codeless capacity notification. -/
def kernelCode? : RowFieldRefusal → Option String
  | .nameUnresolved .indexField => some "MVK_INVALID_INDEX_FIELD"
  | .nameUnresolved .sortField => some "MVK_INVALID_SORT_FIELD"
  | .valueValidationOff .indexField => some "MVK_INDEX_FIELD_NO_VALUE_VALIDATION"
  | .valueValidationOff .sortField => some "MVK_SORT_FIELD_NO_VALUE_VALIDATION"
  | .indexFieldTableEnum => some "MVK_INDEX_FIELD_NO_TABLE_ENUM"
  | .sortFieldDuplicate => some "MVK_SORT_FIELD_DUPLICATE"
  | .sortListCapacity => none

/-- Whether the class is one of the Kernel's index and sort checks, which wait on the entity walk: a
model whose walk refused anything draws none of them. Measured beside a refused path and a count below
one; the table-enumeration class shares the index check by source reading only
([October 21 letter](../../docs/sources/inbound-handbacks.md#src-inbound-2026-10-21), §2.16). -/
def isOrderingGate : RowFieldRefusal → Bool
  | .nameUnresolved _ | .valueValidationOff _ | .indexFieldTableEnum => true
  | .sortFieldDuplicate | .sortListCapacity => false

/-- Every class of the family. -/
def all : List RowFieldRefusal :=
  [.nameUnresolved .indexField, .valueValidationOff .indexField, .indexFieldTableEnum,
   .nameUnresolved .sortField, .valueValidationOff .sortField, .sortFieldDuplicate, .sortListCapacity]

end RowFieldRefusal

/-- What a nomination resolves to: the group's direct child of the nominated short name in the
default variant, which `FlatModel.nominatedTarget` derives. Absence and a non-field both fail the
first arm, and they are kept apart because only one of them is what an author usually wrote. -/
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

/-- Why a nomination fails the build before any class is drawn. The Kernel reports no class for
either; the cause is kept only so a consumer can say which step refused. -/
inductive NominationBuildFailure where
  | invalidModel (cause : ResolveError)
  | unbound (cause : ResolveError)
  deriving Repr, DecidableEq

/-- Derive a nomination's target the way the Kernel does: bind the authored path against the model
as authored, then ask the group's direct child of that short name in the default variant.

The two steps can read different fields. `../Key` binds to the parent's `Key`, but the local `Key`
is judged, so the parent's variant filter or value-validation switch changes nothing while the local
one's decides ([inbound](../../docs/sources/inbound-handbacks.md#inbound-2026-09-27a-index-and-sort-lookup)).
`dropped` lists the fields a variant filter `ONLY` removes from the default variant; `ALL_EXCEPT`
keeps the field, so it is simply not listed. The model must validate, which excludes the peer's two
same-named siblings told apart only by their filters: this model cannot declare two fields at one
path. -/
def FlatModel.nominatedTarget (model : FlatModel) (dropped : List FieldId)
    (group : GroupPath) (nomination : SurfaceFieldPath) :
    Except NominationBuildFailure NominatedTarget := do
  if let .error cause := model.validate then throw (.invalidModel cause)
  let _ ← model.resolveFieldDeclarationUnchecked group nomination |>.mapError .unbound
  let name := nomination.field
  match model.fields.find? fun field =>
      field.groupPath == group && field.name == name && !dropped.contains field.id with
  -- No A12 enumeration is a table enumeration (`TableEnumeration.lean`), so the arm stays false.
  | some field => pure (.field field.isRawString false)
  | none => pure (if model.hasGroupPath (group ++ [name]) then .group else .unresolved)

/-- A repeatable group's row-key declarations: at most one index nomination, any number of sort
nominations, each sort nomination with the name it is written as. -/
structure RowFieldDeclarations where
  index : Option NominatedTarget := none
  sort : List (String × NominatedTarget) := []
  /-- Sort names the duplicate judgement skips: those whose kept short name draws the field-name
  shape ([October 21 letter](../../docs/sources/inbound-handbacks.md#src-inbound-2026-10-21), §2.16). -/
  refusedNames : List String := []
  deriving Repr, DecidableEq

/-- Keep an entry unless its name is already kept, so each name is judged at its first entry. -/
def keepFirstName (kept : List (String × NominatedTarget)) (entry : String × NominatedTarget) :
    List (String × NominatedTarget) :=
  if kept.any (·.1 == entry.1) then kept else kept ++ [entry]

/-- Every refusal the group's declarations draw: the index nomination's, then each distinct sort
name's once in written order, then the list's two judgements. A list rather than a first match,
because the Kernel judges every name, a fourth entry's included: two disqualified sort fields draw two
classes, while a field named twice draws its own class once. The duplicate class reads only the first
three entries, so a name repeated only at the fourth draws none, and every entry beyond the third
draws one codeless capacity notification ([declaration-report](../../docs/sources/model-structure-and-declaration-probes.md#src-declaration-report-withholding-k14)
and [sort-list](../../docs/sources/model-structure-and-declaration-probes.md#src-sort-list-capacity) rows; peer
`CheckerDeclarationWithholdingAgreementTest` measured a five-entry list drawing two, a12-dmkits
`6bdfe70f4`). A repeated name is the written one, measured on identical spellings. -/
def rowFieldDeclarationRefusals (declarations : RowFieldDeclarations) : List RowFieldRefusal :=
  let distinct := declarations.sort.foldl keepFirstName []
  let leading := ((declarations.sort.take 3).map (·.1)).filter (!declarations.refusedNames.contains ·)
  (declarations.index.bind (rowFieldRefusal .indexField)).toList ++
    distinct.filterMap (rowFieldRefusal .sortField ·.2) ++
    (if leading.Nodup then [] else [.sortFieldDuplicate]) ++
    List.replicate (declarations.sort.length - 3) .sortListCapacity

end A12Kernel
