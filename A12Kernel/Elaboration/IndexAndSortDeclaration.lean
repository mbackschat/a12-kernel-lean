import A12Kernel.Elaboration.DeclarationAdmission
import A12Kernel.Elaboration.Flat.Model

/-! # A repeatable group's index field and sort fields, and the one property that disqualifies both

A repeatable group may nominate one **index field** — the row key that arms `RepetitionNotUnique`, the semantic index, and parallel iteration — and any number of **sort fields** that order its rows for display. Both nominations are checked at code-generation time, and both run the same short cascade: the name must resolve to a direct child field, that field must not switch value validation off, and an index field must additionally not be a table enumeration.

**The disqualifying property is the one [`ValueFormalCheck.lean`](../Semantics/ValueFormalCheck.lean) already owns.** A String declaration that switches value validation off ends the stored-value pipeline before the technical length cap, storing whatever was authored; a field the Kernel never inspects cannot serve as a row key or a sort key, because both need a comparable value. This is that switch's second consumer, and the first one outside the value pipeline.

**A nomination is a name, not a position.** Kernel 31.1.1 joins the written spelling to the group's own path and keeps only the last segment of the result, wherever it lands, then judges that short name against the group's own direct children (a12-dmkits `GroupIndexAndSortReferenceLawsTest` at `1124b523f`, KF653): `..` steps up one level from the group itself, every other segment descends, and the field the group declares under that name enters the cascade. A name no direct child field carries, a name that is a rule and a name that is a child group all draw the role's unresolved class, so `../Key` naming only the parent's field reaches `MVK_INVALID_INDEX_FIELD` and `MVK_INVALID_SORT_FIELD` and the local namesake alone decides ([inbound](../../docs/sources/inbound-handbacks.md#inbound-2026-09-27a-index-and-sort-lookup)). Kernel 30.8.1 left no model for a spelling that bound nowhere. Two spellings leave no model in this account: an absolute one and one climbing above the model root. Kernel 31.3.1 resolves the ordering member as a field reference, so a spelling landing on a group draws the role's unresolved class where 31.1.1 left no model, and a sort name written empty draws the sort role's unresolved class with a codeless unset-name notification (a12-dmkits KF680, [inbound](../../docs/sources/inbound-handbacks.md#src-inbound-2026-11-07) §3). The empty index spelling is joined to the group itself, so it keeps the group's own name. The table-enumeration arm inherits [`TableEnumeration.lean`](TableEnumeration.lean)'s constant: no A12 enumeration is a table enumeration, so an index field can never be one.

**The asymmetry worth keeping.** A group carries at most one index field and any number of sort fields, so the index cascade runs once and the sort cascade once per nominated field — but the classes stay distinct per role, which is what lets a consumer say *which* nomination is at fault when a group carries both.

**Evidence.** Both value-validation classes are measured against the real Kernel on hand-authored declarations, alongside an accepted control for each role ([checkpoint](../../docs/sources/model-structure-and-declaration-probes.md#src-index-and-sort-field-declaration)); the spelling laws are the 31.1.1 measurements cited above.

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
  /-- A sort list holding, among its first three entries, a name that is blank without being empty: an
  unfilled entry of the Kernel's own metamodel. A judgement of the list, reported once however many
  entries are blank. -/
  | sortInfoMissing
  /-- A sort entry whose name is written empty. A judgement of the list, read once however many entries are
  empty, a multiplicity no row measures; the Kernel's notification carries no code. -/
  | sortNameUnset
  deriving Repr, DecidableEq

namespace RowFieldRefusal

/-- The exact catalog key, `none` for the two codeless notifications. -/
def kernelCode? : RowFieldRefusal → Option String
  | .nameUnresolved .indexField => some "MVK_INVALID_INDEX_FIELD"
  | .nameUnresolved .sortField => some "MVK_INVALID_SORT_FIELD"
  | .valueValidationOff .indexField => some "MVK_INDEX_FIELD_NO_VALUE_VALIDATION"
  | .valueValidationOff .sortField => some "MVK_SORT_FIELD_NO_VALUE_VALIDATION"
  | .indexFieldTableEnum => some "MVK_INDEX_FIELD_NO_TABLE_ENUM"
  | .sortFieldDuplicate => some "MVK_SORT_FIELD_DUPLICATE"
  | .sortListCapacity => none
  | .sortInfoMissing => some "MVK_SORT_INFO_MISSING"
  | .sortNameUnset => none

/-- The capture label: the catalog key, or for a codeless notification its observed label. -/
def label : RowFieldRefusal → String
  | .sortListCapacity => "codeless:sort-list-capacity"
  | .sortNameUnset => "codeless:sort-name-unset"
  | refusal@(.nameUnresolved _) | refusal@(.valueValidationOff _) | refusal@.indexFieldTableEnum
  | refusal@.sortFieldDuplicate | refusal@.sortInfoMissing => refusal.kernelCode?.getD ""

/-- Whether the class is one of the Kernel's index and sort checks, which wait on the entity walk: a
model whose walk refused anything draws none of them. Measured beside a refused path and a count below
one; the table-enumeration class shares the index check by source reading only
([October 21 letter](../../docs/sources/inbound-handbacks.md#src-inbound-2026-10-21), §2.16). Whether the
unfilled-entry class waits too is unmeasured, and it is read as a list judgement like the duplicate class. -/
def isOrderingGate : RowFieldRefusal → Bool
  | .nameUnresolved _ | .valueValidationOff _ | .indexFieldTableEnum => true
  | .sortFieldDuplicate | .sortListCapacity | .sortInfoMissing | .sortNameUnset => false

/-- Every class of the family. -/
def all : List RowFieldRefusal :=
  [.nameUnresolved .indexField, .valueValidationOff .indexField, .indexFieldTableEnum,
   .nameUnresolved .sortField, .valueValidationOff .sortField, .sortFieldDuplicate, .sortListCapacity,
   .sortInfoMissing, .sortNameUnset]

end RowFieldRefusal

/-- What a nomination resolves to: the group's direct child of the nominated short name, which
`FlatModel.nominatedTarget` derives. Absence and a non-field, a rule included, both fail the
first arm, and they are kept apart because only one of them is what an author usually wrote. -/
inductive NominatedTarget where
  /-- No direct child field of that name. -/
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

/-- Why a written spelling leaves no model, whatever the rest of the model holds (a12-dmkits
`GroupIndexAndSortReferenceLawsTest` at `1124b523f`, kernel 31.1.1). The Kernel reports no class for any of
them; the cause is kept only so a consumer can say which step refused. -/
inductive NominationFailure where
  /-- A leading `/`: the Kernel's reader cannot read an absolute spelling as a relative path. -/
  | absolute
  /-- More `..` steps than the group has enclosing levels, so a step climbs past the model root. -/
  | climbsAboveRoot
  deriving Repr, DecidableEq

/-- Why a nomination fails the build before any class is drawn. -/
inductive NominationBuildFailure where
  | invalidModel (cause : ResolveError)
  | spelling (failure : NominationFailure)
  deriving Repr, DecidableEq

/-- The path a written nomination reads as, joined to its group: each `..` steps up one level from the
group itself and every other segment descends, empty segments (a doubled or trailing `/`) being dropped,
a choice no measurement settles. `none` when a step climbs above the root, so the group's own depth is the
number of `..` it may take. -/
def nominationLanding (group : GroupPath) (written : String) : Option GroupPath :=
  ((written.splitOn "/").filter (!·.isEmpty)).foldlM (init := group) fun path step =>
    if step == ".." then (if path.isEmpty then none else some path.dropLast) else some (path ++ [step])

/-- The short name a nomination is judged by: the last segment of its joined path, and for the empty
spelling the group's own name. A path with no segment left keeps no name, which draws the unresolved
class; no measurement reaches it. -/
def nominationShortName (group : GroupPath) (written : String) : String :=
  ((nominationLanding group written).bind (·.getLast?)).getD ""

/-- What the spelling alone makes of a nomination: it leaves no model when absolute or when it climbs above
the model root. -/
def nominationFailure? (group : GroupPath) (written : String) : Option NominationFailure :=
  if written.startsWith "/" then some .absolute
  else match nominationLanding group written with
    | none => some .climbsAboveRoot
    | some _ => none

/-- Derive a nomination's target the way the Kernel does: read the spelling against the group's path, then
ask the group's direct child of the short name it keeps.

Two paths can differ. `../Key` lands on the parent's `Key`, but the local `Key` is judged, so the parent's
value-validation switch changes nothing while the local one's decides
([inbound](../../docs/sources/inbound-handbacks.md#inbound-2026-09-27a-index-and-sort-lookup)). The model
must validate, which excludes the peer's two same-named siblings told apart only by retired variant
filters: this model cannot declare two fields at one path. -/
def FlatModel.nominatedTarget (model : FlatModel) (role : RowFieldRole)
    (group : GroupPath) (written : String) : Except NominationBuildFailure NominatedTarget := do
  if let .error cause := model.validate then throw (.invalidModel cause)
  if let some failure := nominationFailure? group written then throw (.spelling failure)
  -- An empty sort name names no field, even beside a child named like the group.
  if role == .sortField && written.isEmpty then return .unresolved
  let name := nominationShortName group written
  match model.fields.find? fun field => field.groupPath == group && field.name == name with
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

/-- A sort name the metamodel reads as an unfilled entry: written, not empty, and blank as Java's `isBlank`
reads it, so an em space counts and trimming would not. An empty name is not an unfilled entry: it draws the
unresolved-name class and the codeless unset notification (`sortNameUnset`), where kernel 31.1.1 built no model. -/
def unfilledSortName (written : String) : Bool := !written.isEmpty && ExecutableDeclaration.blank written

/-- Keep an entry unless its name is already kept, so each name is judged at its first entry. -/
def keepFirstName (kept : List (String × NominatedTarget)) (entry : String × NominatedTarget) :
    List (String × NominatedTarget) :=
  if kept.any (·.1 == entry.1) then kept else kept ++ [entry]

/-- Every refusal the group's declarations draw: the index nomination's, then each distinct sort
name's once in written order, then the list's judgements. A list rather than a first match,
because the Kernel judges every name, a fourth entry's included: two disqualified sort fields draw two
classes, while a field named twice draws its own class once. The duplicate class reads only the first
three entries, so a name repeated only at the fourth draws none, and every entry beyond the third
draws one codeless capacity notification ([declaration-report](../../docs/sources/model-structure-and-declaration-probes.md#src-declaration-report-withholding-k14)
and [sort-list](../../docs/sources/model-structure-and-declaration-probes.md#src-sort-list-capacity) rows; peer
`CheckerDeclarationWithholdingAgreementTest` measured a five-entry list drawing two, a12-dmkits
`6bdfe70f4`). The unfilled-entry class is drawn once when any of the first three names is unfilled, however
many are (two blank entries draw one); it reads the three entries the metamodel holds, as a12-dmkits'
checker does, and a blank name beyond the third is unmeasured. A repeated name is the written one,
measured on identical spellings. -/
def rowFieldDeclarationRefusals (declarations : RowFieldDeclarations) : List RowFieldRefusal :=
  let distinct := declarations.sort.foldl keepFirstName []
  let leading := ((declarations.sort.take 3).map (·.1)).filter (!declarations.refusedNames.contains ·)
  (declarations.index.bind (rowFieldRefusal .indexField)).toList ++
    distinct.filterMap (rowFieldRefusal .sortField ·.2) ++
    (if leading.Nodup then [] else [.sortFieldDuplicate]) ++
    List.replicate (declarations.sort.length - 3) .sortListCapacity ++
    (if (declarations.sort.take 3).any (unfilledSortName ·.1) then [.sortInfoMissing] else []) ++
    (if declarations.sort.any (·.1.isEmpty) then [.sortNameUnset] else [])

end A12Kernel
