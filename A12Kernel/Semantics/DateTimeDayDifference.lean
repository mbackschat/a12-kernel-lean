import A12Kernel.Semantics.ModelZone

/-! # Model-zone calendar-day differences

This capsule implements kernel 31.1.1's `DifferenceInDays` core for the concrete UTC and Europe/Berlin profiles: whole days between the two operands' model-zone wall clocks, truncated toward zero (spec/05 §2.5). Each operand is decoded from its exact instant, so a gap label that resolved one gap later counts from where it landed, and the millisecond takes part in the truncation.

Parsing, Date-versus-DateTime admission, empty and malformed operands, numeric result storage and validation polarity remain with their consumers.
-/

namespace A12Kernel.ModelZone.ConcreteProfile

/-- The wall clock an exact instant shows in the model zone, in milliseconds counted as if it were UTC. -/
def wallMillisAt? (profile : ConcreteProfile) (instant : Instant) : Option Int := do
  (← profile.calendarLabel? instant).wallMillis? (instant.epochMillis % 1000)

/-- Signed whole wall-clock days from the first resolved instant to the second. `none` only when an instant decodes to no proleptic label of the profile. -/
def differenceResolvedInDays? (profile : ConcreteProfile) (first second : Instant) : Option Int := do
  pure (((← profile.wallMillisAt? second) - (← profile.wallMillisAt? first)).tdiv 86400000)

/-- Resolve two fresh labels, then count wall-clock days between where they landed. -/
def differenceInDays? (profile : ConcreteProfile) (first second : LocalDateTime) : Option Int := do
  profile.differenceResolvedInDays? (← profile.resolveLocal? first) (← profile.resolveLocal? second)

end A12Kernel.ModelZone.ConcreteProfile

namespace A12Kernel.ModelZone

/-- String dispatch for the concrete model-zone profiles. Unselected ids return `none`; Berlin behavior is never extrapolated to them. -/
def concreteDifferenceInDays? (zoneId : String) (first second : LocalDateTime) : Option Int :=
  (ConcreteProfile.ofId? zoneId).bind (·.differenceInDays? first second)

end A12Kernel.ModelZone
