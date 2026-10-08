import A12Kernel.Elaboration.ErrorTextParameterModelKind

/-! # What a message parameter may say about *where* its value comes from

Once a parameter's entity has resolved, three further gates read what the parameter wrote around it: an
old-world coordinate specifier pinning a form position, a relative path climbing towards the root, and
the value suffix's own two preconditions. They are grouped here because each is a statement about the
address rather than about the value, and because two of them carry traps a reimplementation reproduces
only by accident.

**The two coordinate specifiers are one mechanism under two class names.** The serial and line
coordinates run the identical test against different positions of the field's declared maximum, and
report different classes. `coordinateRefusal_class_follows_coordinate` proves the shape is shared, so the
two classes are a naming distinction and not a semantic one.

**That mechanism's special case is a string comparison, not a number.** The specifier `1` is admitted at
any declared maximum, *including* a maximum of one — but the test is equality with the literal `1`, so a
numeral spelling the same value differently is **not** the special case and is refused wherever the
maximum is one. A port that parses the specifier before comparing it silently admits what the Kernel
refuses.

**And the bound check applies to numerals only.** A specifier that is not numeric at all skips the
upper-bound comparison entirely; it still meets the maximum-of-one test, so it is refused only there. A
port that treats every non-`1` specifier as a number gets the symbolic case wrong in the permissive
direction.

**The value suffix's star gate is A12-only, which is the reverse of the `#` parameters' gate.** Reading a
value through a reference the condition only reaches with a star is refused on an A12 model and
unchecked on an H-model — where [`ErrorTextParameterModelKind`](ErrorTextParameterModelKind.lean) has the
A12 world forbidden outright. So neither world is the permissive one; each checks what the other does
not.

**Its second gate is keyed on the field's declared kind.** Skipping value validation is a String-type
declaration, so the checker asks the field's kind first and a non-String field can never reach that class
however it is declared.

**The relative-path gate is arithmetic, and its comparison is the one a `Nat` port breaks.** The Kernel
subtracts the written climb from the rule group's level and refuses a negative result. Written with
truncated natural subtraction that test can never fire, so the clause below compares the operands
directly instead.

**Evidence.** The relative-path gate's class and boundary are **witnessed** on the group position,
whose checked resolver walks with `GroupPath.walkUp` rather than calling this clause: from a rule two
levels below the root, `$#../..$` reaches the root group and is admitted while `$#../../..$` draws the
class, and from one level below `$#../../Probe$` draws it
([availability](../../docs/sources/message-and-pointer-probes.md#src-message-group-availability),
[layers](../../docs/sources/message-and-pointer-probes.md#src-message-group-argument-layers)). A single
up-step past the root, `$#../Store$` from a root-group rule, draws the same class; which Kernel step
produces it is not separated. The
value suffix's two classes are measured on the A12 route
([checkpoint](../../docs/sources/message-and-pointer-probes.md#src-message-parameter-surface-and-iteration-gates)). The two
coordinate specifiers remain **source-derived and unwitnessed**: they are old-world spellings whose
grammar productions this project's A12-only route does not reach.

This module carries no rendered message text, by the licensing boundary in [`CLAUDE.md`](../../CLAUDE.md).
-/

namespace A12Kernel

/-- The two old-world form coordinates a specifier may pin. -/
inductive FormCoordinate where
  /-- The running-number coordinate, the outer form position. -/
  | serial
  /-- The line coordinate, the inner one. -/
  | line
  deriving Repr, DecidableEq

/-- Each coordinate reports its own class for the identical failure. -/
def FormCoordinate.refusal : FormCoordinate → KernelStaticDiagnostic
  | .serial => .serialCoordinateInvalid
  | .line => .lineCoordinateInvalid

/-- What the parameter wrote in the coordinate position. The three cases are distinguished by
**spelling**, because the Kernel's special case is a string comparison. -/
inductive CoordinateSpecifier where
  /-- Exactly the literal `1`. -/
  | one
  /-- A numeral that is not that literal, carrying its parsed value — `01` is here, not above. -/
  | numeral (value : Nat)
  /-- A specifier that is not numeric at all. -/
  | symbolic
  deriving Repr, DecidableEq

/-- **The shared coordinate test.** The literal escapes both checks; every other spelling meets the
maximum-of-one check, and only a numeral additionally meets the bound. -/
def coordinateRefusal (coordinate : FormCoordinate) (declaredMax : Nat) :
    CoordinateSpecifier → Option KernelStaticDiagnostic
  | .one => none
  | .numeral value =>
      if declaredMax == 1 then some coordinate.refusal
      else if value > declaredMax then some coordinate.refusal
      else none
  | .symbolic => if declaredMax == 1 then some coordinate.refusal else none

/-- What the value suffix needs to know about the field it names. -/
structure ValueAccess where
  /-- The condition reaches the field somewhere without a star. -/
  referencedWithoutStar : Bool := true
  /-- The field's declared type is String, the precondition of the flag below. -/
  fieldIsString : Bool := false
  /-- That String declaration skips value validation. -/
  noValueValidation : Bool := false
  deriving Repr, DecidableEq

/-- **The value suffix's two gates**, first match wins. The star gate consults the model kind; the
declaration gate does not, but is reachable only on a String field. -/
def valueAccessRefusal (kind : ModelKind) (access : ValueAccess) : Option KernelStaticDiagnostic :=
  if kind == .a12 && !access.referencedWithoutStar then
    some .valueParameterOnStarredReference
  else if access.fieldIsString && access.noValueValidation then
    some .valueParameterNoValueValidation
  else none

/-- **The relative-path gate.** Refuses exactly when the written climb passes the root group. Compared as
operands rather than by subtracting, because truncated natural subtraction never goes negative and would
make this gate unreachable. -/
def relativeUpRefusal (ruleGroupLevel upCount : Nat) : Option KernelStaticDiagnostic :=
  if ruleGroupLevel < upCount then some .parameterTooManyParentGroups else none

end A12Kernel
