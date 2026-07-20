/-! # Ordinary Enumeration direct-field comparability

This static capsule begins after equality/inequality and direct-field operand shape have been checked. Every Enumeration operand is a resolved legal ordinary closed declaration, and every String operand is an already-admitted ordinary plain value-readable String field. Its facts use canonical locale keys and complete display maps with unique stored tokens and injective display text per locale. Those declaration and field-kind checks are preceding obligations, not reconstructed here.

An Enumeration is effectively display-bearing only when at least one localized display differs from its stored token. Two display-bearing Enumerations need only form one consistent partial bijection in every shared locale; unshared tokens, display texts, and locales are irrelevant. Table, open/dynamic, partial, duplicate-display, category, literal, and arbitrary String-expression cases are deliberately outside this boundary.
-/

namespace A12Kernel

/-- One resolved localized stored/display association from a legal ordinary Enumeration declaration. -/
structure EnumerationDisplayFact where
  locale : String
  stored : String
  display : String
  deriving Repr, DecidableEq

namespace EnumerationDisplayFact

/-- Whether this authored display changes the stored token visible to users. -/
def isEffectiveDisplay (fact : EnumerationDisplayFact) : Bool :=
  fact.display != fact.stored

/-- Two associations conflict only in a shared locale, either by disagreeing on a shared stored token or by assigning one display to different stored tokens. -/
def conflictsWith (left right : EnumerationDisplayFact) : Bool :=
  left.locale == right.locale &&
    ((left.stored == right.stored && left.display != right.display) ||
      (left.display == right.display && left.stored != right.stored))

end EnumerationDisplayFact

/-- The display facts needed by direct-field comparability; the stored-token domain itself belongs to the preceding declaration check. -/
structure ResolvedEnumerationDisplay where
  facts : List EnumerationDisplayFact
  deriving Repr, DecidableEq

namespace ResolvedEnumerationDisplay

/-- Identity labels do not make an Enumeration display-bearing. -/
def hasEffectiveDisplay (profile : ResolvedEnumerationDisplay) : Bool :=
  profile.facts.any EnumerationDisplayFact.isEffectiveDisplay

/-- Whether the two declarations disagree on their common locale/token/display relation. -/
def conflictsWith (left right : ResolvedEnumerationDisplay) : Bool :=
  left.facts.any fun leftFact =>
    right.facts.any leftFact.conflictsWith

end ResolvedEnumerationDisplay

/-- The two already-resolved direct field kinds admitted by this static gate. -/
inductive DirectComparableField where
  | plainString
  | enumeration (display : ResolvedEnumerationDisplay)
  deriving Repr, DecidableEq

/-- Closed rejection classes at this boundary. Both map-conflict directions correspond to the same outward kernel diagnostic family. -/
inductive EnumerationComparabilityError where
  | displayClassMismatch
  | displayMapConflict
  deriving Repr, DecidableEq

/-- Static admission result, separate from runtime equality/inequality evaluation. -/
inductive EnumerationComparisonAdmission where
  | accepted
  | rejected (error : EnumerationComparabilityError)
  deriving Repr, DecidableEq

namespace EnumerationComparisonAdmission

def isAccepted : EnumerationComparisonAdmission → Bool
  | .accepted => true
  | .rejected _ => false

end EnumerationComparisonAdmission

/-- Decide comparability for two direct fields. Equality and inequality share this gate. -/
def classifyDirectFieldComparison :
    DirectComparableField → DirectComparableField →
      EnumerationComparisonAdmission
  | .plainString, .plainString => .accepted
  | .plainString, .enumeration profile
  | .enumeration profile, .plainString =>
      if profile.hasEffectiveDisplay then
        .rejected .displayClassMismatch
      else
        .accepted
  | .enumeration left, .enumeration right =>
      if left.hasEffectiveDisplay != right.hasEffectiveDisplay then
        .rejected .displayClassMismatch
      else if left.hasEffectiveDisplay && left.conflictsWith right then
        .rejected .displayMapConflict
      else
        .accepted

/-- Boolean view used by checked consumers and universal admission laws. -/
def directFieldComparisonAllowed
    (left right : DirectComparableField) : Bool :=
  (classifyDirectFieldComparison left right).isAccepted

end A12Kernel
