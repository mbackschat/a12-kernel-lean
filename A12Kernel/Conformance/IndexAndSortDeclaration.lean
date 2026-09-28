import A12Kernel.Elaboration.IndexAndSortDeclaration

/-! # Locks on the index- and sort-field declaration cascade

The cases pin the cascade's order, the one arm on which the two roles differ, and the four catalog keys a consumer switches on. The two value-validation classes and their accepted controls are measured; the unresolved arm is reached by a nominated field the default variant drops and by a relative nomination whose local namesake is absent, measured by the peer, while the group arm has no known witness ([inbound](../../docs/SOURCES.md#inbound-2026-09-27a-index-and-sort-lookup)), while a name resolving nowhere in the authored model fails the build first, which the [checkpoint](../../docs/SOURCES.md#src-index-and-sort-field-declaration) records.
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
        { index := some (.field true false), sort := [.field true false, .field false false] } =
      [.valueValidationOff .indexField, .valueValidationOff .sortField] ∧
      rowFieldDeclarationRefusals { index := some (.field false false), sort := [] } = [] := by
  native_decide

/- Each sort nomination is checked on its own, so the list's refusals track its members positionally
   rather than collapsing to one. -/
example :
    rowFieldDeclarationRefusals
        { sort := [.field false false, .unresolved, .field true false] } =
      [.nameUnresolved .sortField, .valueValidationOff .sortField] := by
  native_decide

/- Five distinct keys across two roles. The index and sort spellings differ by more than a prefix,
   so a consumer deriving one from the other by substitution gets a key the Kernel never emits. -/
example :
    (RowFieldRefusal.all.map (·.catalogKey)).eraseDups.length = 5 ∧
      RowFieldRefusal.all.length = 5 ∧
      (RowFieldRefusal.valueValidationOff .indexField).catalogKey =
        "MVK_INDEX_FIELD_NO_VALUE_VALIDATION" ∧
      (RowFieldRefusal.valueValidationOff .sortField).catalogKey =
        "MVK_SORT_FIELD_NO_VALUE_VALIDATION" := by
  native_decide

/- The peer's ordering-lookup model: a root `/Order/Key` beside a repeatable `/Order/Items` holding
   `Key` and `Spare`, the group nominating `Key` or `../Key`
   ([inbound](../../docs/SOURCES.md#inbound-2026-09-27a-index-and-sort-lookup)). Ids 1 and 2 are the
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

private def direct : SurfaceFieldPath := { base := .relative 0, groups := [], field := "Key" }
private def remote : SurfaceFieldPath := { base := .relative 1, groups := [], field := "Key" }

/-- `none` is the build failure, which draws no class; `some none` an admitted nomination. -/
private def lookup (role : RowFieldRole) (nomination : SurfaceFieldPath)
    (parent own : Option Bool := some false) (dropped : List FieldId := []) :
    Option (Option RowFieldRefusal) :=
  ((lookupModel parent own).nominatedTarget dropped items nomination).toOption.map
    (rowFieldRefusal role)

/- One row per branch of the peer's scenarios, in both roles. The local namesake decides: dropping
   or removing it draws the invalid class and switching its value validation off the switch's class,
   while the same change to the parent's `Key` that `../Key` binds to changes nothing. A name binding
   nowhere in the authored model fails the build, whichever field the default variant keeps. The
   peer's two same-named siblings told apart only by their variant filters are outside this model,
   which refuses two fields with one path. -/
example : [RowFieldRole.indexField, .sortField].all (fun role =>
    [lookup role direct,
      lookup role direct (dropped := [2]),
      lookup role direct (own := none),
      lookup role remote,
      lookup role remote (dropped := [1]),
      lookup role remote (parent := none),
      lookup role remote (dropped := [2]),
      lookup role remote (dropped := [1, 2]),
      lookup role remote (own := none),
      lookup role remote (parent := some true),
      lookup role remote (own := some true)] ==
    [some none,
      some (some (.nameUnresolved role)),
      none,
      some none,
      some none,
      none,
      some (some (.nameUnresolved role)),
      some (some (.nameUnresolved role)),
      some (some (.nameUnresolved role)),
      some none,
      some (some (.valueValidationOff role))]) = true := by
  native_decide

/- The index nomination of a root-group field the default variant drops draws the invalid class too;
   the peer measures no sort nomination there. -/
example :
    let root : FlatModel := { fields := [stringField 1 ["Order"] "Key"] }
    (root.nominatedTarget [1] ["Order"] direct).toOption.map (rowFieldRefusal .indexField) =
      some (some (.nameUnresolved .indexField)) := by
  native_decide

end A12Kernel.Conformance.IndexAndSortDeclaration
