/-! # A temporal constructor's operand gate is per position, and its two refusal classes say *why*

`Date`, `Time`, and `DateTime` each have ordered operands, and the Kernel checks every position
separately. This module owns the gate for the operand shape that has no other owner — an **extraction
operator call** such as `DayFromDate(D)` — together with the slot table the gate reads.

**The slots.** The canonical `Date` component positions are day, month and year. Its year can instead be omitted under a declared Base Year or split into century and short year. `Time` admits zero to three components; `DateTime` takes two whole values ([spec/05 §3](../../spec/05-dates-and-time.md#3-constructing-dates-and-checking-validity)). The component-slot table governs extractor placement; the separate count gate governs these authored forms.

**A component slot admits exactly the extractor whose component it is**, and the two ways of being
wrong are *different classes*:

- the operator belongs to the constructor's own component family but sits at another family member's
  position — `MonthFromDate` where the day belongs — reports the **wrong-position** class;
- the operator belongs to the other family, or owns no slot anywhere, reports the **not-allowed**
  class. `QuarterFromDate` is the second kind while being a date operator: it is legal in an ordinary
  expression and admitted at no constructor position at all.

Both were measured across the full seven-operator by eight-position grid with an accepted control for
every constructor, so the split is read off the table rather than inferred from one example. It is
also the distinction the Kernel's own BA documentation blurs, filing an example whose message names
the wrong-position class under the not-allowed class's heading.

**`DateTime` is not a component constructor, and that is why its class differs.** Its slots take
*values*, so an extraction call there is a kind error rather than a position error and both slots
report the same date-kind class — including the time slot, where a time class might be expected.
Nesting a whole `Date(...)` or `Time(...)` there is admitted, which is what shows the refusal is about
the operand's result kind and not about extraction operators being excluded.

**A wrong-kind *field* at that same slot reports a different class again.** A bare `Time` field where
`DateTime` wants a date draws the declared-format class that
[`TemporalFormat`](../Semantics/TemporalFormat.lean) already owns, not the date-kind class. So one
position has two refusal vocabularies selected by whether the operand is a field or a call, and a
consumer that normalises both to "wrong operand type" loses the distinction the Kernel makes.

**The extractor's own source is a separate gate with its own classes** and is not restated here: a
`DATETIME` field feeds both families, a `TIME` field at a date extractor draws the declared-format
class, and a non-temporal field draws the no-date class. This module ends where that one begins.

This module carries no rendered message text, by the licensing boundary in [`CLAUDE.md`](../../CLAUDE.md).
-/

namespace A12Kernel

/-- The temporal component an operator extracts, or that a constructor slot expects. The two families
are kept apart because family membership is exactly what selects the refusal class. -/
inductive TemporalComponent where
  | day | month | year
  | hours | minutes | seconds
  /-- A date component with no constructor slot. Legal in an expression, admitted at no position. -/
  | quarter
  deriving Repr, DecidableEq

namespace TemporalComponent

/-- Whether the component belongs to the date family. `quarter` does, which is why it cannot be told
from the admitted date components by family alone. -/
def isDateFamily : TemporalComponent → Bool
  | .day | .month | .year | .quarter => true
  | .hours | .minutes | .seconds => false

/-- The extraction operator that yields this component. -/
def extractor : TemporalComponent → String
  | .day => "DayFromDate"
  | .month => "MonthFromDate"
  | .year => "YearFromDate"
  | .quarter => "QuarterFromDate"
  | .hours => "HoursFromTime"
  | .minutes => "MinutesFromTime"
  | .seconds => "SecondsFromTime"

/-- Every extraction operator the condition language offers. -/
def all : List TemporalComponent :=
  [.day, .month, .year, .quarter, .hours, .minutes, .seconds]

end TemporalComponent

/-- The three temporal constructors, by the operand list they take. -/
inductive TemporalConstructor where
  /-- Canonical day, month and year slots, with omitted-year and split-year alternatives. -/
  | date
  /-- Hours, minutes, seconds — any prefix, including the empty one. -/
  | time
  /-- A date value and a time value, both required. Not a component constructor. -/
  | dateTime
  deriving Repr, DecidableEq

namespace TemporalConstructor

/-- The component each position expects, outermost first. Empty for `dateTime`, whose positions take
whole values rather than components — the emptiness is the model of that difference, not a gap. -/
def componentSlots : TemporalConstructor → List TemporalComponent
  | .date => [.day, .month, .year]
  | .time => [.hours, .minutes, .seconds]
  | .dateTime => []

/-- Whether the canonical component list admits every prefix. Date has separate year forms. -/
def admitsPrefix : TemporalConstructor → Bool
  | .time => true
  | .date | .dateTime => false

/-- Number of canonical slots; the split-year Date form has one additional position. -/
def arity : TemporalConstructor → Nat
  | .date => 3
  | .time => 3
  | .dateTime => 2

end TemporalConstructor

/-- A class the operand gate can report. -/
inductive ConstructorOperandRefusal where
  /-- The extractor belongs to this constructor's component family but to another position. -/
  | extractOpWrongPosition
  /-- The extractor belongs to the other family, or owns no slot at all. -/
  | extractOpNotAllowed
  /-- A non-value expression where `DateTime` wants a date. -/
  | invalidDateForOp
  deriving Repr, DecidableEq

namespace ConstructorOperandRefusal

/-- The exact catalog key. -/
def catalogKey : ConstructorOperandRefusal → String
  | .extractOpWrongPosition => "MVK_INVALID_DATE_OR_TIME_EXTRACT_OP"
  | .extractOpNotAllowed => "MVK_DATE_OR_TIME_EXTRACT_OP_NOT_ALLOWED"
  | .invalidDateForOp => "MVK_INVALID_DATE_FOR_OP"

/-- Every class of the family. -/
def all : List ConstructorOperandRefusal :=
  [.extractOpWrongPosition, .extractOpNotAllowed, .invalidDateForOp]

end ConstructorOperandRefusal

/-- A component with no constructor slot of its own. It shares the date family with `Date`'s three
components, so the family test alone would call it a wrong-position case — and the measured answer is
the not-allowed class at every position. Handled before the family test for exactly that reason: there
is no position it would have been right at. -/
def slotlessComponent : TemporalComponent → Bool
  | .quarter => true
  | _ => false

/-- **The gate for an extraction-operator operand at one constructor position.**

`position` is zero-based. A constructor with no component slots takes whole values, so an extraction
call anywhere in it is a kind error rather than a position error — which is why `dateTime`'s empty slot
table produces the date-kind class in both of its positions rather than needing an arm of its own. -/
def constructorOperandRefusal (constructor : TemporalConstructor) (position : Nat)
    (operand : TemporalComponent) : Option ConstructorOperandRefusal :=
  match constructor.componentSlots[position]? with
  | none => some .invalidDateForOp
  | some expected =>
      if operand == expected then none
      else if slotlessComponent operand then some .extractOpNotAllowed
      else if operand.isDateFamily == expected.isDateFamily then some .extractOpWrongPosition
      else some .extractOpNotAllowed

/-- Authored constructor arity. The omitted Date year requires a model Base Year;
Time's omitted suffix, including every component, is filled with zero (spec/05 §3). -/
def operandCountAdmitted (constructor : TemporalConstructor) (supplied : Nat)
    (hasBaseYear : Bool := false) : Bool :=
  match constructor with
  | .date => supplied == 3 || supplied == 4 || (supplied == 2 && hasBaseYear)
  | .time => supplied ≤ 3
  | .dateTime => supplied == 2

end A12Kernel
