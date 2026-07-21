import A12Kernel.Semantics.DateTime

/-! # Finite Berlin 2024 calendar-day differences

This capsule implements the resolved `DifferenceInDays` core only for the consecutive spring slice declared by `Berlin2024Profile`. It counts stateful calendar-day landings in authored operand order. The profile bound makes three steps sufficient and rejects every operand pair outside that exact domain.

Parsing, Date-versus-DateTime admission, empty and malformed operands, calendar identity outside this profile, numeric result storage, validation polarity, and general model-zone dispatch remain separate.
-/

namespace A12Kernel.Berlin2024Profile

/-- Count consecutive profile landings that do not pass the later instant. Three is the exact diameter of the supported spring slice. -/
private def countLandings : Nat → LocalDateTime → Instant → Nat
  | 0, _, _ => 0
  | fuel + 1, current, later =>
      match nextCalendarDay? current with
      | none => 0
      | some next =>
          match resolveLocal? next with
          | none => 0
          | some landing =>
              if landing.epochSecond ≤ later.epochSecond then
                1 + countLandings fuel next later
              else
                0

/-- Signed stateful calendar-day count after both fresh labels resolve inside the finite spring profile. -/
def differenceInDays? (first second : LocalDateTime) : Option Int :=
  if SpringSupported first ∧ SpringSupported second then
    do
      let firstInstant ← resolveLocal? first
      let secondInstant ← resolveLocal? second
      if firstInstant.epochSecond < secondInstant.epochSecond then
        pure (countLandings 3 first secondInstant : Int)
      else if secondInstant.epochSecond < firstInstant.epochSecond then
        pure (-(countLandings 3 second firstInstant : Int))
      else
        pure 0
  else
    none

end A12Kernel.Berlin2024Profile
