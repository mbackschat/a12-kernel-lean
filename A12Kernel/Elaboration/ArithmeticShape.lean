import A12Kernel.Elaboration.StaticDiagnostic

/-! # What shape an arithmetic expression may take, before anything is evaluated

Four static gates constrain the *form* of a calculation rather than its value: how many divisions one
multiplicative region may hold, whether a power may sit directly on another's left, what scale an
exponent may have, and how many constants a field-list operator's operand list may carry. Each is a
readability or old-parser-compatibility rule rather than a soundness one, which is why none of them is
derivable from the arithmetic itself.

**The division limit is scoped, and the scope boundaries are the surprise.** At most one *open* division
is allowed per multiplication/division region — but grouping, addition, subtraction and power each start
a **fresh** region. So `a / b / c` is refused while `a / b + c / d` is admitted, and the Kernel's own
source records that `a / {b / c}` is deliberately accepted because the previous parser did not detect it
and its test corpus depends on that. This is a compatibility behaviour, not an oversight, and a
reimplementation that counts divisions globally refuses models the Kernel accepts.

**The power gate reads only the left operand, so grouping *enables* what it appears to forbid.** A power
whose left operand is directly another power is refused; wrapping that left operand in braces admits it.
Measured both ways — the ungrouped chain refuses and the left-grouped form is admitted — so the rule is
about the ungrouped chain rather than about nesting.

**The exponent gate reads a derived scale, not a syntactic shape.** An exponent must have a known scale of
zero. A fractional literal, a field declared with fractional digits, and a division — whose scale is
unknown — are each refused, while a *compound* exponent built from whole-scale operands is admitted. So
this module takes the derived scale as an input: computing it belongs to the numeric family that already
owns scale, and duplicating it here would be a second account of one fact.

**The constant limit counts the whole operand list.** A field-list calculation operator admits at most one
constant among its operands, whatever the list's length.

**Evidence.** All four classes are **measured** against the real Kernel, with admitted controls for each
([checkpoint](../../docs/SOURCES.md#src-arithmetic-shape-gates)). The division scope is separated at four
boundaries, the power gate both ways, the exponent gate across literal, declared-field, unknown-scale and
compound exponents, and the constant limit at two list lengths.

This module carries no rendered message text, by the licensing boundary in [`CLAUDE.md`](../../CLAUDE.md).
-/

namespace A12Kernel

/-- An arithmetic expression's shape. Operands carry no scale here: the exponent gate takes its scale as
a separate input, because deriving it is the numeric family's responsibility. -/
inductive CalcExpr where
  /-- A field, literal, aggregate, or anything else the shape gates do not look inside. -/
  | operand
  /-- Multiplication, which combines its children's open divisions. -/
  | multiply (left right : CalcExpr)
  /-- Division, which combines its children's and adds one. -/
  | divide (left right : CalcExpr)
  /-- Addition or subtraction; the two behave identically for every gate here. -/
  | addSub (left right : CalcExpr)
  /-- A brace group. -/
  | grouped (inner : CalcExpr)
  /-- Exponentiation. -/
  | power (base exponent : CalcExpr)
  deriving Repr, DecidableEq

/-- **The division walk.** Returns the open divisions this expression contributes to its *enclosing*
region, together with whether some already-closed region held more than one. A boundary constructor
closes its children's regions — checking them — and contributes nothing upward. -/
def divisionScan : CalcExpr → Nat × Bool
  | .operand => (0, false)
  | .multiply left right =>
      let (openLeft, badLeft) := divisionScan left
      let (openRight, badRight) := divisionScan right
      (openLeft + openRight, badLeft || badRight)
  | .divide left right =>
      let (openLeft, badLeft) := divisionScan left
      let (openRight, badRight) := divisionScan right
      (openLeft + openRight + 1, badLeft || badRight)
  | .addSub left right =>
      let (openLeft, badLeft) := divisionScan left
      let (openRight, badRight) := divisionScan right
      (0, badLeft || badRight || openLeft > 1 || openRight > 1)
  | .grouped inner =>
      let (openInner, badInner) := divisionScan inner
      (0, badInner || openInner > 1)
  | .power base exponent =>
      let (openBase, badBase) := divisionScan base
      let (openExponent, badExponent) := divisionScan exponent
      (0, badBase || badExponent || openBase > 1 || openExponent > 1)

/-- The division gate, closing the outermost region too. -/
def divisionRefusal (expression : CalcExpr) : Option KernelStaticDiagnostic :=
  let (open', bad) := divisionScan expression
  if bad || open' > 1 then some .tooManyDivisionsInRegion else none

/-- Whether an expression is *directly* a power. The power gate reads exactly this of its left operand,
so the predicate is the gate's own vocabulary rather than a proof convenience. -/
def CalcExpr.isDirectPower : CalcExpr → Bool
  | .power _ _ => true
  | _ => false

/-- **The power gate.** Only a power sitting *directly* on another power's left is refused; a group
between them defeats it. -/
def powerRefusal : CalcExpr → Option KernelStaticDiagnostic
  | .power base exponent =>
      match base with
      | .power _ _ => some .nestedPowerOnLeft
      | _ => (powerRefusal base).or (powerRefusal exponent)
  | .multiply left right | .divide left right | .addSub left right =>
      (powerRefusal left).or (powerRefusal right)
  | .grouped inner => powerRefusal inner
  | .operand => none

/-- **The exponent gate**, over the scale the numeric family derives. `none` is an unknown scale, which a
division produces and which is refused exactly as a positive scale is. -/
def exponentRefusal (derivedScale : Option Nat) : Option KernelStaticDiagnostic :=
  match derivedScale with
  | none => some .exponentScaleNotWhole
  | some 0 => none
  | some _ => some .exponentScaleNotWhole

/-- **The constant limit** over a field-list operator's operand list. -/
def constantListRefusal (operandIsConstant : List Bool) : Option KernelStaticDiagnostic :=
  if (operandIsConstant.filter id).length ≥ 2 then some .tooManyConstantsInOperandList else none

end A12Kernel
