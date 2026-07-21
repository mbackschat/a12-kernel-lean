import A12Kernel.Semantics.DateTime

/-! # Versioned Europe/Berlin legacy timezone profile

This module implements the exact `europe-berlin-java-util-timezone-jdk21-tzdb2026a-v1` transition profile from `spec/05` §5.1. It owns UTC offset selection and fresh local-label resolution only. Model-zone dispatch, parsing, formal-cell projection, rendering, chained wall-day landing, and public protocol exposure remain separate.
-/

namespace A12Kernel.EuropeBerlinLegacyProfile

/-- Stable identity of the pinned legacy timezone account. -/
def version : String :=
  "europe-berlin-java-util-timezone-jdk21-tzdb2026a-v1"

/-- One UTC transition label and the offset taking effect at that instant. -/
structure Transition where
  year : Int
  month : Nat
  day : Nat
  hour : Nat
  offsetSecondsAfter : Int
  deriving Repr, DecidableEq

private def transition (year : Int) (month day hour : Nat)
    (offsetSecondsAfter : Int) : Transition :=
  { year, month, day, hour, offsetSecondsAfter }

/-- The complete ordered legacy transition table through 1997. -/
def transitions : List Transition :=
  [ transition 1916 4 30 22 7200
  , transition 1916 9 30 23 3600
  , transition 1917 4 16 1 7200
  , transition 1917 9 17 1 3600
  , transition 1918 4 15 1 7200
  , transition 1918 9 16 1 3600
  , transition 1940 4 1 1 7200
  , transition 1942 11 2 1 3600
  , transition 1943 3 29 1 7200
  , transition 1943 10 4 1 3600
  , transition 1944 4 3 1 7200
  , transition 1944 10 2 1 3600
  , transition 1945 4 2 1 7200
  , transition 1945 5 24 0 10800
  , transition 1945 9 24 0 7200
  , transition 1945 11 18 1 3600
  , transition 1946 4 14 1 7200
  , transition 1946 10 7 1 3600
  , transition 1947 4 6 2 7200
  , transition 1947 5 11 1 10800
  , transition 1947 6 29 0 7200
  , transition 1947 10 5 1 3600
  , transition 1948 4 18 1 7200
  , transition 1948 10 3 1 3600
  , transition 1949 4 10 1 7200
  , transition 1949 10 2 1 3600
  , transition 1980 4 6 1 7200
  , transition 1980 9 28 1 3600
  , transition 1981 3 29 1 7200
  , transition 1981 9 27 1 3600
  , transition 1982 3 28 1 7200
  , transition 1982 9 26 1 3600
  , transition 1983 3 27 1 7200
  , transition 1983 9 25 1 3600
  , transition 1984 3 25 1 7200
  , transition 1984 9 30 1 3600
  , transition 1985 3 31 1 7200
  , transition 1985 9 29 1 3600
  , transition 1986 3 30 1 7200
  , transition 1986 9 28 1 3600
  , transition 1987 3 29 1 7200
  , transition 1987 9 27 1 3600
  , transition 1988 3 27 1 7200
  , transition 1988 9 25 1 3600
  , transition 1989 3 26 1 7200
  , transition 1989 9 24 1 3600
  , transition 1990 3 25 1 7200
  , transition 1990 9 30 1 3600
  , transition 1991 3 31 1 7200
  , transition 1991 9 29 1 3600
  , transition 1992 3 29 1 7200
  , transition 1992 9 27 1 3600
  , transition 1993 3 28 1 7200
  , transition 1993 9 26 1 3600
  , transition 1994 3 27 1 7200
  , transition 1994 9 25 1 3600
  , transition 1995 3 26 1 7200
  , transition 1995 9 24 1 3600
  , transition 1996 3 31 1 7200
  , transition 1996 10 27 1 3600
  , transition 1997 3 30 1 7200
  , transition 1997 10 26 1 3600
  ]

/-- UTC epoch second of a checked transition label. -/
def Transition.epochSecond? (item : Transition) : Option Int :=
  (CivilDate.ofYmd? item.year item.month item.day).map fun date =>
    date.unixEpochDay * 86400 + (item.hour : Int) * 3600

private def historicalOffsetSecondsAt? :
    List Transition → Int → Int → Option Int
  | [], _, current => some current
  | item :: rest, epochSecond, current =>
      match item.epochSecond? with
      | none => none
      | some boundary =>
          if epochSecond < boundary then some current
          else historicalOffsetSecondsAt? rest epochSecond
            item.offsetSecondsAfter

/-- Last Sunday in a Gregorian month, used by the post-1997 EU recurrence. -/
private def lastSunday? (year : Int) (month : Nat) : Option CivilDate := do
  let lastDay ← DateParts.daysInMonth? year month
  let monthEnd ← CivilDate.ofYmd? year month lastDay
  let weekday := Int.toNat ((monthEnd.unixEpochDay + 4) % 7)
  CivilDate.ofYmd? year month (lastDay - weekday)

private def recurringOffsetSecondsAt? (year epochSecond : Int) : Option Int := do
  let spring ← lastSunday? year 3
  let autumn ← lastSunday? year 10
  let springBoundary := spring.unixEpochDay * 86400 + 3600
  let autumnBoundary := autumn.unixEpochDay * 86400 + 3600
  pure (if springBoundary ≤ epochSecond ∧ epochSecond < autumnBoundary then
    7200 else 3600)

/-- Offset in seconds at an exact UTC instant. The transition table applies through 1997; the recurring EU rule applies from 1998 onward. -/
def offsetSecondsAt? (instant : Instant) : Option Int :=
  let epochSecond := instant.epochMillis / 1000
  match CivilDate.ofUnixEpochDay? (epochSecond / 86400) with
  | none => none
  | some utcDate =>
      if utcDate.parts.year < 1998 then
        historicalOffsetSecondsAt? transitions epochSecond 3600
      else
        recurringOffsetSecondsAt? utcDate.parts.year epochSecond

/-- Every offset appearing in the pinned profile, ordered for overlap selection. -/
def candidateOffsets : List Int := [3600, 7200, 10800]

/-- Instant obtained by interpreting a wall label under one candidate offset. -/
def candidateInstant (dateTime : LocalDateTime)
    (offsetSeconds : Int) : Instant :=
  { epochMillis :=
      dateTime.resolveUtc.epochMillis + (-offsetSeconds * 1000) }

/-- Smallest valid offset for a fresh local label. Ascending candidates implement the legacy smaller/after-offset overlap policy. -/
def selectedOffset? (dateTime : LocalDateTime) : Option Int :=
  candidateOffsets.find? fun offsetSeconds =>
    offsetSecondsAt? (candidateInstant dateTime offsetSeconds) ==
      some offsetSeconds

/-- Resolve a fresh Berlin wall label. Gaps have no matching candidate; overlaps select the smaller offset. -/
def resolveLocal? (dateTime : LocalDateTime) : Option Instant :=
  (selectedOffset? dateTime).map (candidateInstant dateTime)

end A12Kernel.EuropeBerlinLegacyProfile
