import A12Kernel.Elaboration.Flat.Types

/-! # The constant-assignment diagnostic ladder

A computation that assigns a bare constant to a target of the wrong kind is refused, and **which**
class the Kernel reports is decided by an ordered ladder over the (constant family, target kind)
pair rather than by either side alone. Measured as a complete eight-constant by ten-target grid on
repeatable targets ([checkpoint](../../docs/SOURCES.md#src-constant-assignment-diagnostic-ladder)),
the three rungs are:

1. **A Boolean or Confirm target outranks every constant**, a temporal one included, and the two
   kinds report *different* classes.
2. **A temporal constant then reports its own family** whatever the remaining target is — a date
   constant at a String target draws the date class, not the string one. All three temporal
   families share the single class, and so does a temporal target whose declared format refused
   the constant.
3. **Otherwise the target's declared kind decides.**

The grid is what makes the ladder legible, because two of its cells are the only places the pair
matters. At a Number target a string-like constant draws `invalidCompareToEnumOrString` while a
Boolean one draws `inconsistentTypesCompared`; and rung 2 inverts the whole reading for temporal
constants. A carrier that read its table off a measured sibling instead of measuring its own would
therefore be wrong in exactly those cells, which is why this ladder is one shared function over the
pair rather than a per-carrier map of the target kind.

The function answers a **kind** question only. Whether an admitted pair then survives the target's
own format, decimal scale, or declared enumeration domain belongs to that target's policy, and the
pairs this returns `none` for are the ones no kind gate refuses.
-/

namespace A12Kernel

/-- The constant families the assignment ladder distinguishes. The three temporal families collapse
into one because the Kernel's own class does not separate them at this gate. -/
inductive ConstantAssignmentFamily where
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
def constantAssignmentDiagnostic? :
    ConstantAssignmentFamily → SurfaceScalarKind → Option KernelStaticDiagnostic
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

end A12Kernel
