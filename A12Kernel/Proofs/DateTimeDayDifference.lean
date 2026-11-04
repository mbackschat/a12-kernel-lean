import A12Kernel.Semantics.DateTimeDayDifference

/-! # Model-zone calendar-day difference laws

These laws hold for both concrete profiles because the day count is a truncated difference of decoded wall clocks. The nearest non-law: a day count is not the elapsed-instant quotient, since 24 instant hours across an autumn overlap count 0; the conformance module witnesses it.
-/

namespace A12Kernel.ModelZone.ConcreteProfile

/-- A decodable instant is zero days from itself. -/
theorem differenceResolvedInDays_self (profile : ConcreteProfile) (instant : Instant) :
    profile.differenceResolvedInDays? instant instant =
      (profile.wallMillisAt? instant).map fun _ => 0 := by
  cases wall : profile.wallMillisAt? instant <;> simp [differenceResolvedInDays?, wall]

/-- Swapping the operands negates the count, because truncation toward zero is odd. -/
theorem differenceResolvedInDays_swap (profile : ConcreteProfile) (first second : Instant) :
    (profile.differenceResolvedInDays? first second).map (-·) =
      profile.differenceResolvedInDays? second first := by
  cases firstWall : profile.wallMillisAt? first <;>
    cases secondWall : profile.wallMillisAt? second <;>
    simp [differenceResolvedInDays?, firstWall, secondWall]
  rename_i firstMillis secondMillis
  rw [← Int.neg_tdiv]
  congr 1
  omega

end A12Kernel.ModelZone.ConcreteProfile
