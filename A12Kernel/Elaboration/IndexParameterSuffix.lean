import A12Kernel.Elaboration.StaticDiagnostic

/-! # What an `index(...)` parameter's suffix reads, and why the two suffixes disagree

Once the parameter's short name has resolved and the repeatability cross-check has passed
([`IndexParameterResolution`](IndexParameterResolution.lean)), the Kernel reads the suffix. There are two,
they run entirely different checkers over the *same* set of referenced index-field declarations, and the
parts of a declaration they consult are almost disjoint. This module owns that stage.

**Writing neither suffix is itself a refusal.** A bare index reference is not defaulted to either
reading; it draws its own class.

**The two suffixes disagree about a wholly non-Enumeration set, and that is the family's sharpest
separator.** `->Category` demands every referenced declaration be an Enumeration and refuses the first
that is not. `.value` only asks whether they *agree*: it compares each against the first, so a set in
which none is an Enumeration is consistent and therefore **admitted**. An account that models "the
parameter requires enumerations" is right about one suffix and wrong about the other.

**Past that, each suffix reads a part of the declaration the other never touches.** Both compare the
declared value set. Only `->Category` compares the value-to-category mapping; only `.value` compares the
supported display locales and the display values. So a pair of declarations differing solely in their
category mapping is refused under one suffix and admitted under the other, and a pair differing solely in
their display mapping is refused the other way round. Both halves are locked as separators in this family's conformance module rather than proved in a
quantified form.

**One shape here is deliberately not modelled as two things.** The Kernel raises the display class from
two sites — differing supported locales, and differing display values inside a shared locale — and
reports the same class for both, so nothing in this result domain distinguishes them and the clause
folds them. Likewise the category checker compares each declaration against its **predecessor** while the
value checker compares each against the **first**; for the equality tests both perform, those two walks
accept exactly the same sets, and they differ only in which entity name the message would carry, which
this vocabulary does not model. Both simplifications are recorded rather than silent, because each is a
distinction a later message-rendering consumer would have to reintroduce.

**Evidence.** `FIELD_NO_ENUM`, `INVALID_CATEGORY`, the suffix-missing class, and the two value-set and
category-mapping classes are measured
([checkpoint](../../docs/SOURCES.md#src-index-terminal-refusal-classes),
[cross-field pairs](../../docs/SOURCES.md#src-message-parameter-surface-and-iteration-gates)).
`INVALID_INDEX_FIELD_ENUM_XML_TO_DISPLAY` and `INVALID_INDEX_FIELD_INCONSISTENT_TYPES` are
**source-derived and unwitnessed**: the first needs two Enumeration index fields differing only in display
labels, the second one Enumeration against another kind under a shared short name, and the Kernel's own
source notes that the rule parser already refuses the second before this checker sees it.

This module carries no rendered message text, by the licensing boundary in [`CLAUDE.md`](../../CLAUDE.md).
-/

namespace A12Kernel

/-- One index-field declaration the condition references, projected onto the parts the two suffix
checkers compare. The value and display lists are ordered, because the Kernel compares sequences and a
reordering is a difference. -/
structure ReferencedDeclaration where
  /-- The field's type is an Enumeration. -/
  isEnumeration : Bool := true
  /-- Its Enumeration declares the category the parameter named. -/
  declaresCategory : Bool := true
  /-- Its declared value set, in declaration order. -/
  values : List String := []
  /-- The named category's values, aligned to `values`. Read by the category suffix only. -/
  categoryValues : List String := []
  /-- Its supported display locales together with the display values under them, folded because the
  Kernel reports one class for a difference in either. Read by the value suffix only. -/
  displayMapping : List String := []
  deriving Repr, DecidableEq

/-- Which suffix the parameter wrote. -/
inductive ParameterSuffix where
  /-- `->Category`. -/
  | category
  /-- `.value`. -/
  | value
  /-- Neither, which is itself refused. -/
  | absent
  deriving Repr, DecidableEq

/-- **The category suffix**, folding each declaration against its predecessor. The type and category
tests run on every declaration including the first; the two comparisons need a predecessor and so are
skipped for it. -/
def categorySuffixScan (previous : Option ReferencedDeclaration) :
    List ReferencedDeclaration → Option KernelStaticDiagnostic
  | [] => none
  | declaration :: rest =>
      if !declaration.isEnumeration then some .indexFieldNoEnumeration
      else if !declaration.declaresCategory then some .indexFieldCategoryUnknown
      else match previous with
        | none => categorySuffixScan (some declaration) rest
        | some earlier =>
            if earlier.values != declaration.values then some .indexFieldEnumValuesDiffer
            else if earlier.categoryValues != declaration.categoryValues then
              some .indexFieldCategoryMappingDiffers
            else categorySuffixScan (some declaration) rest

/-- **The value suffix**, comparing each declaration against the first. It asks only for agreement, so a
set whose declarations are uniformly non-Enumeration passes without any Enumeration test. -/
def valueSuffixScan (first : ReferencedDeclaration) :
    List ReferencedDeclaration → Option KernelStaticDiagnostic
  | [] => none
  | declaration :: rest =>
      if first.isEnumeration != declaration.isEnumeration then some .indexFieldInconsistentTypes
      else if !first.isEnumeration then valueSuffixScan first rest
      else if first.values != declaration.values then some .indexFieldEnumValuesDiffer
      else if first.displayMapping != declaration.displayMapping then
        some .indexFieldDisplayMappingDiffers
      else valueSuffixScan first rest

/-- **The suffix stage.** An absent suffix refuses before either checker runs, and an empty referenced
set admits under both — the same skip the repeatability stage has, for the same reason. -/
def suffixRefusal : ParameterSuffix → List ReferencedDeclaration → Option KernelStaticDiagnostic
  | .absent, _ => some .indexFieldSuffixMissing
  | .category, referenced => categorySuffixScan none referenced
  | .value, [] => none
  | .value, first :: rest => valueSuffixScan first (first :: rest)

end A12Kernel
