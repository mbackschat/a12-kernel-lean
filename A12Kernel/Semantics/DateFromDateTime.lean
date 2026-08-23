import A12Kernel.Semantics.ModelZone

/-! # `DateFromDateTime`

The Date-valued DateTime component extractor, and the exact sibling of `TimeFromDateTime`: where that
one keeps the wall clock and discards the date, this one keeps the wall date and discards the clock.

**It reads the label, not the instant.** Measured at kernel 30.8.1 on both codegen strategies, a stored
label of `2024-06-15T00:30:00` extracts to `2024-06-15`; converting the retained instant to UTC first
would have produced `2024-06-14` under the `+0200` zone the probe recorded, and the Kernel refused that
reading. So the date components come straight off the value's own wall label, and nothing here can shift
a day.

**The result's own instant is a choice this project makes, not a measured fact.** Validation output
carries no instant. An extracted Date is constructed the way every other stored Date in this theory is,
as its date's **midnight in the model zone**, so a comparison cannot distinguish it from a stored Date
carrying the same text. That is why the midnight is resolved freshly rather than reused from the source:
the offset at midnight may differ from the offset at the source instant, which is the same separation
[`ModelZone.resolve?`](ModelZone.lean) already documents for `Today`.

Static admission belongs to the elaboration layer. What is settled there, measured: the result is a Date
comparable to a Date field, to `Today`, and to another extraction, and admitted as a Date-addition
operand; `Now` and a `TimeFromDateTime` result are refused; and a degenerate time-only DateTime source or
a plain Date source is refused at the operator itself. -/

namespace A12Kernel

/-- Extract the Date a complete DateTime value carries, or `none` when the payload is not a DateTime or
its own wall date has no resolvable midnight in this profile.

The second failure is reachable only for a forged payload, because a checked DateTime cell resolves its
label at classification. It is kept rather than defaulted so an impossible value cannot acquire a
fabricated date. -/
def dateFromDateTime? (profile : ModelZone.ConcreteProfile) :
    TemporalValue → Option DateValue
  | .dateTime _ parts _ basis => do
      let civil ← CivilDate.ofParts? parts
      let full ← FullDate.ofCivil? civil
      let midnightLabel ← LocalDateTime.ofDateHms? full 0 0 0
      let midnight ← profile.resolveLocal? midnightLabel
      pure { instant := midnight, parts := full.civil.parts, basis }
  | .date _ | .time _ _ => none

end A12Kernel
