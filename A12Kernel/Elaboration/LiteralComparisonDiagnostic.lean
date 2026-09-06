import A12Kernel.Elaboration.Flat.Types

/-! # The literal-comparison diagnostic ladder

When a literal of one family meets a field of another kind, the Kernel refuses, and **which** class
it reports is decided by an ordered ladder over the pair rather than by either side alone.

**The name is carrier-neutral on purpose.** This ladder was first measured at a constant assignment
and its vocabulary said so — "constant", "target". Two further carriers then turned out to draw the
same table: a `Having` filter, where nothing is a target, and a plain rule comparison, where nothing
is a constant. Prose authored from one carrier inherits that carrier's words silently, and the
inherited word only stops reading as neutral once a second carrier exists to test it against; a12-dmkits
shipped a user-facing corrective with exactly that defect on the same day and had to withdraw it.
The three carriers are recorded at the [filter checkpoint](../../docs/SOURCES.md#src-having-filter-comparison-and-scope-classes). Measured as a complete eight-literal by eleven-kind grid
([checkpoint](../../docs/SOURCES.md#src-constant-assignment-diagnostic-ladder)), the three rungs
are:

1. **A Boolean or Confirm field kind outranks every literal**, a temporal one included, and the two
   kinds report *different* classes.
2. **A temporal literal then reports its own family** whatever the remaining kind is — a date
   literal against a String field draws the date class, not the string one. All three temporal
   families share the single class, and so does a temporal target whose declared format refused
   the constant.
3. **Otherwise the field's declared kind decides.**

The grid is what makes the ladder legible, because two of its cells are the only places the pair
matters. At a Number target a string-like constant draws `invalidCompareToEnumOrString` while a
Boolean one draws `inconsistentTypesCompared`; and rung 2 inverts the whole reading for temporal
constants. A carrier that read its table off a measured sibling instead of measuring its own would
therefore be wrong in exactly those cells, which is why this ladder is one shared function over the
pair rather than a per-carrier map of the target kind.

The function answers a **kind** question only. Whether an admitted pair then survives the target's
own format, decimal scale, or declared enumeration domain belongs to that target's policy, and the
pairs this returns `none` for are the ones no kind gate refuses.

**The ladder is the Kernel's comparison vocabulary rather than an assignment-specific table**, and a
second carrier measures it independently: inside a `Having` filter, a field compared against a String
literal draws this function's `stringLike` row cell for cell, on every kind and on all three
operators tested ([checkpoint](../../docs/SOURCES.md#src-having-filter-comparison-and-scope-classes)).
A **plain rule comparison** carrying neither construct draws the same class, so the vocabulary is the
comparison's and not either carrier's. *Why* an assignment reaches it is a separate, undischarged
question: the natural account is the generated equality rule, which would also explain the `COMPARE_TO`
naming, but no witness separates that from a classifier both routes call, so it stays a hypothesis. A **numeric** comparison is a different column and gets its own
function below rather than being forced through this one — measured, its non-Number kinds collapse to
a single class where the literal column spreads them across five.
-/

namespace A12Kernel

/-- The literal families the comparison ladder distinguishes.

These are **content** classifications, not authored surfaces. The Kernel lexer has one string-literal
syntax, so `"x"` and `"05.03.2024"` are the same authored form and differ only in what their content
parses as — witnessed directly by the grid, where the two draw different classes at the *same* String
target. Rung 2 is therefore the Kernel reinterpreting a string literal, not a separate surface
reaching the gate. The three temporal families then collapse into one because the Kernel's own class
does not separate them here. -/
inductive ComparedLiteralFamily where
  | stringLike
  | number
  | temporal
  | booleanLike
  deriving Repr, DecidableEq

/-- The class a wrong-kind constant assignment reports, or `none` where the Kernel's kind gate does
not refuse the pair at all.

`none` is returned for the four admitting pairs, and each is admitted for its own reason: a
string-like constant at a String target, a Number at a Number target, and a Boolean at either
Boolean or Confirm are outright admitted, while a string-like constant at an **Enumeration** target
is gated on the literal's membership in the declared domain rather than on its kind — a declared
token is admitted and an undeclared one draws `invalidStringConstantForEnumComparison`, which is a
value refusal this function is not given the domain to decide.

A temporal target is deliberately **not** in that list. Its admission reads the declared format
string and not the declared kind, so a caller reaching here with a temporal target has already been
refused by format, and rung 2 records that the refusal draws the same class. -/
def literalComparisonDiagnostic? :
    ComparedLiteralFamily → SurfaceScalarKind → Option KernelStaticDiagnostic
  | .booleanLike, .boolean | .booleanLike, .confirm => none
  | .number, .number => none
  | .stringLike, .string | .stringLike, .enumeration => none
  | _, .boolean => some .invalidCompareToYesNo
  | _, .confirm => some .invalidCompareToYes
  | .temporal, _ => some .invalidCompareToDate
  | _, .temporal _ => some .invalidCompareToDate
  | _, .dateRange => some .invalidCompareToDateRange
  | .booleanLike, .number => some .inconsistentTypesCompared
  | .stringLike, .number
  | .number, .string | .number, .enumeration
  | .booleanLike, .string | .booleanLike, .enumeration =>
      some .invalidCompareToEnumOrString

/-- The class a **numeric** comparison reports for a field side of the given kind, or `none` where
the kind is admitted.

This is deliberately not the ladder above at a `number` family, and the measurement is what forces
the separation: a numeric comparison collapses String, Enumeration, Boolean, Confirm and DATE_RANGE
into one class, where the same kinds against a String *literal* spread across four
([checkpoint](../../docs/SOURCES.md#src-having-filter-comparison-and-scope-classes)). Only the
temporal row agrees. Reading one column off the other would report the literal column's spread at a
numeric comparison, which is wrong for six kinds out of eight — the two temporal families are the
only ones the two columns agree on. -/
def numericComparisonDiagnostic? :
    SurfaceScalarKind → Option KernelStaticDiagnostic
  | .number => none
  | .temporal _ => some .invalidCompareToDate
  | .string | .enumeration | .boolean | .confirm | .dateRange =>
      some .invalidTypeForComparison

end A12Kernel
