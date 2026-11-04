import A12Kernel.Elaboration.IndexAndSortDeclaration

/-! # Locks on the index- and sort-field declaration cascade

The cases pin the cascade's order, the one arm on which the two roles differ, the catalog keys a consumer switches on, and how a written spelling is read against the group's own path. The two value-validation classes and their accepted controls are measured; the unresolved arm is reached by a relative nomination whose local namesake is absent, measured by the peer ([inbound](../../docs/sources/inbound-handbacks.md#inbound-2026-09-27a-index-and-sort-lookup)), and on kernel 31.1.1 by any spelling whose short name no direct child field carries (a12-dmkits `GroupIndexAndSortReferenceLawsTest` at `1124b523f`). The group arm has no known witness.
-/

namespace A12Kernel.Conformance.IndexAndSortDeclaration

open A12Kernel

/- The measured pair, in both roles: an ordinary field is accepted and the same field with value
   validation switched off is refused, under the role's own class. -/
example :
    rowFieldRefusal .indexField (.field false false) = none ∧
      rowFieldRefusal .indexField (.field true false) =
        some (.valueValidationOff .indexField) ∧
      rowFieldRefusal .sortField (.field false false) = none ∧
      rowFieldRefusal .sortField (.field true false) =
        some (.valueValidationOff .sortField) := by
  native_decide

/- Name resolution runs first, so a nomination that resolves to nothing reports that rather than any
   property of a field it does not have. A nomination resolving to a group takes the same arm — the
   check is "a direct child field", not "a direct child". -/
example :
    rowFieldRefusal .indexField .unresolved = some (.nameUnresolved .indexField) ∧
      rowFieldRefusal .indexField .group = some (.nameUnresolved .indexField) ∧
      rowFieldRefusal .sortField .group = some (.nameUnresolved .sortField) := by
  native_decide

/- Value validation is checked before the table-enumeration arm, so a field that is both reports the
   switch. Reversing the two would report a class a sort nomination cannot even draw. -/
example :
    rowFieldRefusal .indexField (.field true true) =
        some (.valueValidationOff .indexField) ∧
      rowFieldRefusal .indexField (.field false true) = some .indexFieldTableEnum := by
  native_decide

/- The one arm on which the roles differ: a table enumeration disqualifies an index field and is
   irrelevant to a sort field. A consumer sharing one implementation must branch here and nowhere
   else. -/
example :
    rowFieldRefusal .sortField (.field false true) = none ∧
      rowFieldRefusal .indexField (.field false true) ≠
        rowFieldRefusal .sortField (.field false true) := by
  native_decide

/- The two roles are independent within a group, so a group wrong in both draws both, index first.
   A consumer reporting only the first refusal hides the sort defect entirely. -/
example :
    rowFieldDeclarationRefusals
        { index := some (.field true false), sort := [("NVV", .field true false), ("K", .field false false)] } =
      [.valueValidationOff .indexField, .valueValidationOff .sortField] ∧
      rowFieldDeclarationRefusals { index := some (.field false false), sort := [] } = [] := by
  native_decide

/- Every sort row of the [declaration-report](../../docs/sources/model-structure-and-declaration-probes.md#src-declaration-report-withholding-k14)
   and [sort-list](../../docs/sources/model-structure-and-declaration-probes.md#src-sort-list-capacity) captures, compared as a
   multiset of codes with `none` for the codeless capacity notification. They separate per-entry from
   per-name judgement (`s-same-opaque-twice`, `s-opaque-thrice`), a whole-list from a three-entry
   duplicate window (`s-dup-at-fourth`), and an unjudged from a judged fourth entry (`s-invalid-at-fourth`). -/
private def nominated : String → NominatedTarget
  | "NVV" | "NVV2" => .field true false
  | "../Value" | "../Other" => .unresolved
  | _ => .field false false

private def sortRows : List (String × Option String × List String × List (Option String)) := [
  ("s-control", none, ["K"], []),
  ("s-two-opaque", none, ["NVV", "NVV2"], [some "MVK_SORT_FIELD_NO_VALUE_VALIDATION", some "MVK_SORT_FIELD_NO_VALUE_VALIDATION"]),
  ("s-second-opaque", none, ["K", "NVV"], [some "MVK_SORT_FIELD_NO_VALUE_VALIDATION"]),
  ("s-same-opaque-twice", none, ["NVV", "NVV"], [some "MVK_SORT_FIELD_NO_VALUE_VALIDATION", some "MVK_SORT_FIELD_DUPLICATE"]),
  ("s-same-plain-twice", none, ["K", "K"], [some "MVK_SORT_FIELD_DUPLICATE"]),
  ("s-two-dup-pairs", none, ["K", "K", "V", "V"], [none, some "MVK_SORT_FIELD_DUPLICATE"]),
  ("s-same-plain-thrice", none, ["K", "K", "K"], [some "MVK_SORT_FIELD_DUPLICATE"]),
  ("s-invalid-then-opaque", none, ["../Value", "NVV"], [some "MVK_INVALID_SORT_FIELD", some "MVK_SORT_FIELD_NO_VALUE_VALIDATION"]),
  ("s-opaque-then-invalid", none, ["NVV", "../Value"], [some "MVK_SORT_FIELD_NO_VALUE_VALIDATION", some "MVK_INVALID_SORT_FIELD"]),
  ("s-two-invalid", none, ["../Value", "../Other"], [some "MVK_INVALID_SORT_FIELD", some "MVK_INVALID_SORT_FIELD"]),
  ("s-index-and-sort-opaque", some "NVV", ["NVV"], [some "MVK_INDEX_FIELD_NO_VALUE_VALIDATION", some "MVK_SORT_FIELD_NO_VALUE_VALIDATION"]),
  ("s-index-opaque-two-sorts-opaque", some "NVV", ["NVV", "NVV2"], [some "MVK_INDEX_FIELD_NO_VALUE_VALIDATION", some "MVK_SORT_FIELD_NO_VALUE_VALIDATION", some "MVK_SORT_FIELD_NO_VALUE_VALIDATION"]),
  ("s-three-control", none, ["K", "V", "W"], []),
  ("s-four-distinct", none, ["K", "V", "W", "X"], [none]),
  ("s-dup-at-fourth", none, ["K", "V", "W", "K"], [none]),
  ("s-dup-in-three", none, ["K", "K", "V"], [some "MVK_SORT_FIELD_DUPLICATE"]),
  ("s-opaque-at-first-and-fourth", none, ["NVV", "V", "W", "NVV"], [some "MVK_SORT_FIELD_NO_VALUE_VALIDATION", none]),
  ("s-invalid-at-fourth", none, ["K", "V", "W", "../Value"], [some "MVK_INVALID_SORT_FIELD", none]),
  ("s-opaque-thrice", none, ["NVV", "NVV", "NVV"], [some "MVK_SORT_FIELD_NO_VALUE_VALIDATION", some "MVK_SORT_FIELD_DUPLICATE"])]

example : sortRows.all (fun (_, index, sort, expected) =>
    let actual := (rowFieldDeclarationRefusals
      { index := index.map nominated, sort := sort.map fun name => (name, nominated name) }).map (·.kernelCode?)
    actual.length == expected.length && expected.all fun code => actual.count code == expected.count code) = true := by
  native_decide

/- Every entry beyond the third draws its own capacity notification: the peer's five-entry list, two
   plain names around two opaque ones with the first repeated last, draws two besides the opaque pair's
   classes (`CheckerDeclarationWithholdingAgreementTest`, a12-dmkits `6bdfe70f4`). Four entries, where
   "once" and "per entry" agree, cannot separate the two accounts. -/
example :
    (rowFieldDeclarationRefusals { index := none, sort :=
        ["K", "V", "NVV", "NVV2", "K"].map fun name => (name, nominated name) }).map (·.kernelCode?) =
      [some "MVK_SORT_FIELD_NO_VALUE_VALIDATION", some "MVK_SORT_FIELD_NO_VALUE_VALIDATION", none, none] := by
  native_decide

/- Seven distinct keys across two roles and the list, beside the codeless capacity class. The index and sort
   spellings differ by more than a prefix, so a consumer deriving one from the other by substitution gets a
   key the Kernel never emits. -/
example :
    (RowFieldRefusal.all.filterMap (·.kernelCode?)).eraseDups.length = 7 ∧
      RowFieldRefusal.all.length = 8 ∧
      RowFieldRefusal.sortInfoMissing.kernelCode? = some "MVK_SORT_INFO_MISSING" ∧
      (RowFieldRefusal.valueValidationOff .indexField).kernelCode? =
        some "MVK_INDEX_FIELD_NO_VALUE_VALIDATION" ∧
      (RowFieldRefusal.valueValidationOff .sortField).kernelCode? =
        some "MVK_SORT_FIELD_NO_VALUE_VALIDATION" := by
  native_decide

/- The peer's ordering-lookup model: a root `/Order/Key` beside a repeatable `/Order/Items` holding
   `Key` and `Spare`, the group nominating `Key` or `../Key`
   ([inbound](../../docs/sources/inbound-handbacks.md#inbound-2026-09-27a-index-and-sort-lookup)). Ids 1 and 2 are the
   parent's and the local `Key`. -/
private def items : GroupPath := ["Order", "Items"]

private def stringField (id : FieldId) (groupPath : GroupPath) (name : String)
    (raw : Bool := false) : FlatFieldDecl :=
  { id, groupPath, name, policy := { kind := .string }
    stringValueMode := if raw then .raw else .evaluated
    stringPolicy := { lineBreaksPermitted := true }
    repeatableScope := if groupPath == items then [10] else [] }

private def lookupModel (parent own : Option Bool) : FlatModel :=
  { fields := (parent.map (stringField 1 ["Order"] "Key" ·)).toList ++
      (own.map (stringField 2 items "Key" ·)).toList ++ [stringField 3 items "Spare"]
    repeatableGroups := [{ level := 10, path := items, repeatability := some 2 }] }

/-- A nomination's outcome. The build failure is kept apart from a model that fails validation, so a
fixture that stopped validating cannot pass as a spelling that leaves no model. -/
private inductive Lookup where
  | noModel
  | invalidModel
  | cascade (refusal : Option RowFieldRefusal)
  deriving Repr, DecidableEq

private def Lookup.of (role : RowFieldRole) :
    Except NominationBuildFailure NominatedTarget → Lookup
  | .ok target => .cascade (rowFieldRefusal role target)
  | .error (.invalidModel _) => .invalidModel
  | .error _ => .noModel

private def lookup (role : RowFieldRole) (written : String)
    (parent own : Option Bool := some false) : Lookup :=
  .of role ((lookupModel parent own).nominatedTarget role items written)

/- One row per branch of the peer's scenarios, in both roles. The local namesake decides: removing it
   draws the unresolved class and switching its value validation off the switch's class, while the same
   change to the parent's `Key` that `../Key` lands on changes nothing. A spelling landing on nothing is
   only a name, so `../Key` with no parent `Key` is admitted by the local one and a plain `Key` with no
   local one is unresolved, where kernel 30.8.1 left no model for both (a12-dmkits
   `GroupIndexAndSortReferenceLawsTest` at `1124b523f`, kernel 31.1.1). The peer's two same-named siblings
   told apart only by their variant filters are outside this model, which refuses two fields with one
   path. -/
example : [RowFieldRole.indexField, .sortField].all (fun role =>
    [lookup role "Key",
      lookup role "Key" (own := none),
      lookup role "../Key",
      lookup role "../Key" (parent := none),
      lookup role "../Key" (own := none),
      lookup role "../Key" (parent := some true),
      lookup role "../Key" (own := some true)] ==
    [.cascade none,
      .cascade (some (.nameUnresolved role)),
      .cascade none,
      .cascade none,
      .cascade (some (.nameUnresolved role)),
      .cascade none,
      .cascade (some (.valueValidationOff role))]) = true := by
  native_decide

/- A written spelling is read against the group's own path: `..` steps up one level from the group itself,
   every other segment descends, and the last segment of the result is the short name judged. The empty
   spelling keeps the group's own name; a spelling climbing one level past the root keeps no landing. The
   group's depth is the number of `..` it may take, so two reach the root from `Order/Items` and a third is
   above it. -/
example :
    nominationLanding items "Key" = some ["Order", "Items", "Key"] ∧
      nominationLanding items "../Key" = some ["Order", "Key"] ∧
      nominationLanding items "../../Key" = some ["Key"] ∧
      nominationLanding items "../../../Key" = none ∧
      nominationLanding items "Items/Key" = some ["Order", "Items", "Items", "Key"] ∧
      nominationLanding items "" = some items ∧
      nominationShortName items "" = "Items" ∧
      nominationShortName items "../../Key" = "Key" ∧
      nominationShortName ["Order"] ".." = "" := by
  native_decide

/- Only an absolute spelling, a climb above the root and a non-empty spelling landing on a group leave no
   model; the group is whatever `isGroup` names, and the empty spelling lands on the group itself without
   that being a failure. -/
example :
    let isGroup := fun path => path == ["Order"] || path == items
    nominationFailure? isGroup items "/Order/Items/Key" = some .absolute ∧
      nominationFailure? isGroup items "../../../Key" = some .climbsAboveRoot ∧
      nominationFailure? isGroup items ".." = some .landsOnGroup ∧
      nominationFailure? isGroup ["Order"] "Items" = some .landsOnGroup ∧
      nominationFailure? isGroup items "" = none ∧
      nominationFailure? isGroup items "../../Key" = none ∧
      nominationFailure? isGroup items "../Key" = none := by
  native_decide

/- A sort name written empty binds no reference and leaves no model, where an index written empty keeps the
   group's own name and is unresolved; a spelling landing on a group is no model in either role. -/
example :
    lookup .sortField "" = .noModel ∧
      lookup .indexField "" = .cascade (some (.nameUnresolved .indexField)) ∧
      lookup .indexField ".." = .noModel ∧
      lookup .sortField "/Order/Items/Key" = .noModel := by
  native_decide

/- The list's unfilled-entry class is drawn once however many of the first three names are blank but not
   empty, and an empty name is no entry: it is a judgement of the list, kept apart from each name's own. A
   blank name at the fourth entry draws only its own class and the capacity notification, which is a12-dmkits'
   reading of the three entries the metamodel holds and no measurement. -/
example :
    (rowFieldDeclarationRefusals { sort := [("   ", .unresolved), ("\t", .unresolved)] }).map (·.kernelCode?) =
      [some "MVK_INVALID_SORT_FIELD", some "MVK_INVALID_SORT_FIELD", some "MVK_SORT_INFO_MISSING"] ∧
    unfilledSortName "" = false ∧ unfilledSortName "\u2003" = true ∧ unfilledSortName "\u00A0" = false ∧
    (rowFieldDeclarationRefusals { sort := [("K", .field false false), ("V", .field false false),
        ("W", .field false false), ("   ", .unresolved)] }).map (·.kernelCode?) =
      [some "MVK_INVALID_SORT_FIELD", none] := by
  native_decide

end A12Kernel.Conformance.IndexAndSortDeclaration
