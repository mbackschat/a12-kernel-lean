import A12Kernel.Elaboration.EnumerationComparability

/-! # Ordinary Enumeration direct-field comparability locks

These examples begin after every Enumeration operand is a legal ordinary closed declaration, every category name is resolved exactly, every String operand is an admitted ordinary plain value-readable field, and equality/inequality plus direct-field operand shape have already been checked. Identity display labels and category exemption are retained because they are the main discriminators; table, dynamic, partial, duplicate-display, literal, and arbitrary String-expression cases remain outside this capsule.
-/

namespace A12Kernel

private def fact (locale stored display : String) : EnumerationDisplayFact :=
  { locale, stored, display }

private def enum (facts : List EnumerationDisplayFact) :
    DirectComparableField :=
  .enumeration { facts }

private def plainString : DirectComparableField := .plainString

private def category : DirectComparableField := .category

/- No labels and authored identity labels are both effectively textless. -/
example :
    classifyDirectFieldComparison plainString (enum []) = .accepted ∧
      classifyDirectFieldComparison plainString
        (enum [fact "en" "A" "A", fact "de" "A" "A"]) = .accepted ∧
      classifyDirectFieldComparison
        (enum [fact "en" "A" "A"]) (enum []) = .accepted := by
  native_decide

/- Category access bypasses the direct-field display-remapping gate in either operand position. -/
example :
    classifyDirectFieldComparison category plainString = .accepted ∧
    classifyDirectFieldComparison plainString category = .accepted ∧
    classifyDirectFieldComparison category (enum [fact "en" "A" "Alpha"]) = .accepted ∧
    classifyDirectFieldComparison (enum [fact "en" "A" "Alpha"]) category = .accepted ∧
    classifyDirectFieldComparison category category = .accepted := by
  native_decide

/- One genuine display remapping makes an Enumeration incompatible with a direct String field in either operand order. -/
example :
    classifyDirectFieldComparison plainString
        (enum [fact "en" "A" "Alpha"]) =
      .rejected .displayClassMismatch ∧
    classifyDirectFieldComparison
        (enum [fact "en" "A" "Alpha"]) plainString =
      .rejected .displayClassMismatch := by
  native_decide

/- Textless and display-bearing Enumerations are in different comparability classes. -/
example :
    classifyDirectFieldComparison
        (enum [fact "en" "A" "A"])
        (enum [fact "en" "A" "Alpha"]) =
      .rejected .displayClassMismatch := by
  native_decide

/- Equal and compatibly overlapping display maps are accepted; complete declaration equality is not required. -/
example :
    classifyDirectFieldComparison
        (enum [fact "en" "A" "Alpha", fact "en" "B" "Beta"])
        (enum [fact "en" "A" "Alpha", fact "en" "C" "Gamma"]) =
      .accepted := by
  native_decide

/- A shared stored token may not carry different display text in a shared locale. -/
example :
    classifyDirectFieldComparison
        (enum [fact "en" "A" "Alpha"])
        (enum [fact "en" "A" "Another"]) =
      .rejected .displayMapConflict := by
  native_decide

/- A shared display text may not denote different stored tokens in a shared locale. -/
example :
    classifyDirectFieldComparison
        (enum [fact "en" "A" "Alpha"])
        (enum [fact "en" "B" "Alpha"]) =
      .rejected .displayMapConflict := by
  native_decide

/- Identity facts remain part of the consistency relation once another fact makes each profile display-bearing. -/
example :
    classifyDirectFieldComparison
        (enum [fact "en" "A" "A", fact "en" "X" "Ex"])
        (enum [fact "en" "B" "A", fact "en" "Y" "Why"]) =
      .rejected .displayMapConflict := by
  native_decide

/- Disjoint maps and the same tokens in noncommon locales remain comparable. -/
example :
    classifyDirectFieldComparison
        (enum [fact "en" "A" "Alpha"])
        (enum [fact "en" "B" "Beta"]) =
      .accepted ∧
    classifyDirectFieldComparison
        (enum [fact "en" "A" "Alpha"])
        (enum [fact "de" "A" "Anders"]) =
      .accepted := by
  native_decide

end A12Kernel
