import A12Kernel.Elaboration.StaticDiagnostic

/-! # A literal compared against an enumeration, and the category that changes what it must be

An enumeration field may declare named **categories**: parallel classifications whose values line up
one-for-one with the enumeration's own. A condition may read a value's category instead of the value,
and a literal compared against that reading must be a value **of the category**, which is a different
set from the enumeration's. The Kernel checks this in three places with the same rule and reports it
with three different classes.

**An enumeration value is not a category value.** This is the whole trap. Reading a field's category
and comparing it to one of the field's own values is refused, even though the literal is perfectly
legal against the same field read directly. Measured on one model with three enumeration values and
one two-valued category: the enumeration value is admitted against the plain reading and refused
against the category reading ([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-enumeration-category-constant)).

**The class depends on the carrier as much as on the rule.** The **value-list** carrier keeps the two
arms apart: a literal outside the category draws the category class and a literal outside the
enumeration draws the enumeration class. The **equality** carrier collapses both onto one comparison
class, so the same distinction that is visible in a list is invisible in a comparison. A consumer
reusing one carrier's mapping on the other reports a class the Kernel does not — the split is a
property of where the literal sits, not only of whether a category was written.

**An unknown category is refused earlier and separately**, by its own class, so the value check never
runs against a category that does not exist. That ordering is what keeps the value classes meaning
"this value is wrong" rather than "something about this category is wrong".

**The list carrier is first-invalid-wins over an unordered search.** A list whose members are checked
finds *some* offending literal rather than the first by position, so a consumer reporting the earliest
offender agrees on the class and may disagree on the message's named value.

**Evidence.** Twelve rows on one model measure every cell: both carriers, category written and not,
a literal valid for the enumeration but not the category, a literal valid for neither, an unknown
category, an all-valid list, and a mixed list ([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-enumeration-category-constant)).

This module carries no rendered message text, by the licensing boundary in [`CLAUDE.md`](../../CLAUDE.md).
-/

namespace A12Kernel

/-- Where the literal sits. The Kernel's class vocabulary differs between these two, which is why the
carrier is an input rather than an assumption. -/
inductive EnumConstantCarrier where
  /-- A value list, which keeps the category and whole-enumeration arms apart. -/
  | valueList
  /-- An equality comparison, which collapses them onto one class. -/
  | equality
  deriving Repr, DecidableEq

/-- What the reference reads: the field's own value, or one named category of it. -/
inductive EnumReading where
  | wholeEnumeration
  | category (declared : Bool)
  deriving Repr, DecidableEq

/-- The membership facts a literal has against the field. Both are supplied because a literal may be
a valid enumeration value and an invalid category value at once — the case that carries the trap. -/
structure LiteralMembership where
  /-- The literal is one of the enumeration's own values. -/
  inEnumeration : Bool := false
  /-- The literal is one of the read category's values. Meaningless when no category is read. -/
  inCategory : Bool := false
  deriving Repr, DecidableEq

/-- Whether the literal satisfies whatever the reference actually reads. -/
def LiteralMembership.satisfies (membership : LiteralMembership) : EnumReading → Bool
  | .wholeEnumeration => membership.inEnumeration
  | .category _ => membership.inCategory

/-- **One literal against one reading.** The unknown-category class precedes the value check, and the
carrier decides which vocabulary the value failure is reported in. -/
def enumConstantRefusal (carrier : EnumConstantCarrier) (reading : EnumReading)
    (membership : LiteralMembership) : Option KernelStaticDiagnostic :=
  match reading with
  | .category false => some .categoryUnknown
  | _ =>
      if membership.satisfies reading then none
      else match carrier with
        | .equality => some .invalidStringConstantForEnumComparison
        | .valueList =>
            match reading with
            | .category _ => some .invalidStringConstantForEnumerationCategory
            | .wholeEnumeration => some .invalidStringConstantForEnumeration

/-- **A whole value list.** Some offending literal decides; an all-satisfying list is admitted. -/
def enumConstantListRefusal (reading : EnumReading) (literals : List LiteralMembership) :
    Option KernelStaticDiagnostic :=
  match reading with
  | .category false => some .categoryUnknown
  | _ =>
      match literals.find? fun membership => !membership.satisfies reading with
      | none => none
      | some membership => enumConstantRefusal .valueList reading membership

end A12Kernel
