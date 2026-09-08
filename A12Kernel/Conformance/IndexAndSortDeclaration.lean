import A12Kernel.Elaboration.IndexAndSortDeclaration

/-! # Locks on the index- and sort-field declaration cascade

The cases pin the cascade's order, the one arm on which the two roles differ, and the four catalog keys a consumer switches on. The two value-validation classes and their accepted controls are measured; the name-resolution arms are modelled from the Kernel's check and shadowed in DM-JSON by an earlier model-build failure, which the [checkpoint](../../docs/SOURCES.md#src-index-and-sort-field-declaration) records as measured in its own right.
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

end A12Kernel.Conformance.IndexAndSortDeclaration
