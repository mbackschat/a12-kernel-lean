import A12Kernel.Semantics.DateTime

/-! # Versioned Europe/Berlin timezone profile

This module implements the exact `europe-berlin-java-time-jdk21-tzdb2026a-v1` profile from `spec/05` §5.1: local mean time until 1893, the transition table through 1997, and the EU recurrence after it. It owns UTC offset selection and local-label resolution with an optional preferred offset, the rule kernel 31.1.1 applies through `java.time` (spec/05 §5): a gap label resolves one gap later, an overlap label to the preferred offset when valid and otherwise to the earlier instant. Model-zone dispatch, parsing, formal-cell projection, rendering and public protocol exposure remain separate.
-/

namespace A12Kernel.EuropeBerlinLegacyProfile

/-- Stable identity of the pinned timezone account. -/
def version : String :=
  "europe-berlin-java-time-jdk21-tzdb2026a-v1"

/-- One UTC transition label and the offset taking effect at that instant. -/
structure Transition where
  year : Int
  month : Nat
  day : Nat
  hour : Nat
  minute : Nat := 0
  second : Nat := 0
  offsetSecondsAfter : Int
  deriving Repr, DecidableEq

private def transition (year : Int) (month day hour : Nat)
    (offsetSecondsAfter : Int) : Transition :=
  { year, month, day, hour, offsetSecondsAfter }

/-- Local mean time, `+00:53:28`, the offset before the first table entry. -/
def localMeanTimeOffsetSeconds : Int := 3208

/-- The complete ordered transition table through 1997. Its first entry ends local mean time at the local midnight beginning 1 April 1893. -/
def transitions : List Transition :=
  [ { year := 1893, month := 3, day := 31, hour := 23, minute := 6, second := 32,
      offsetSecondsAfter := 3600 }
  , transition 1916 4 30 22 7200
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
    date.unixEpochDay * 86400 + (item.hour : Int) * 3600 + (item.minute : Int) * 60 +
      (item.second : Int)

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
        historicalOffsetSecondsAt? transitions epochSecond localMeanTimeOffsetSeconds
      else
        recurringOffsetSecondsAt? utcDate.parts.year epochSecond

/-- Every offset appearing in the pinned profile. -/
def candidateOffsets : List Int := [localMeanTimeOffsetSeconds, 3600, 7200, 10800]

/-- Instant obtained by reading a wall clock under one candidate offset. The wall clock is given as `wallMillis`, the label's milliseconds counted as if it were UTC. -/
def candidateInstant (wallMillis offsetSeconds : Int) : Instant :=
  { epochMillis := wallMillis - offsetSeconds * 1000 }

/-- The offsets under which a wall clock names an instant carrying that same offset: none in a gap, two in an overlap. -/
def validOffsets (wallMillis : Int) : List Int :=
  candidateOffsets.filter fun offsetSeconds =>
    offsetSecondsAt? (candidateInstant wallMillis offsetSeconds) == some offsetSeconds

/-- Resolve a wall clock preferring an offset, as `java.time`'s `ZonedDateTime.ofLocal` does. A single valid offset decides. In an overlap the preferred offset decides when valid there, and otherwise the earlier instant, which is the larger offset. A gap is read at the offset in force before it, so the label lands one gap later. Every candidate in a gap lands on one side of the transition, and a gap only ever raises the offset, so the offset before it is the smallest offset the candidates land on; transitions in this profile are weeks apart, beyond the candidates' two-hour spread. -/
def resolveWall? (wallMillis : Int) (preferred : Option Int) : Option Instant :=
  match validOffsets wallMillis with
  | [] =>
      (candidateOffsets.filterMap fun offsetSeconds =>
          offsetSecondsAt? (candidateInstant wallMillis offsetSeconds)).min?.map
        (candidateInstant wallMillis)
  | [offsetSeconds] => some (candidateInstant wallMillis offsetSeconds)
  | offsets =>
      match preferred with
      | some offsetSeconds =>
          if offsets.contains offsetSeconds then some (candidateInstant wallMillis offsetSeconds)
          else offsets.max?.map (candidateInstant wallMillis)
      | none => offsets.max?.map (candidateInstant wallMillis)

/-- Resolve a wall label preferring an offset; see `resolveWall?`. -/
def resolvePreferring? (dateTime : LocalDateTime) (preferred : Option Int) : Option Instant :=
  resolveWall? dateTime.resolveUtc.epochMillis preferred

/-- Resolve a fresh Berlin wall label: a gap one gap later, an overlap at its earlier instant. -/
def resolveLocal? (dateTime : LocalDateTime) : Option Instant :=
  resolvePreferring? dateTime none

end A12Kernel.EuropeBerlinLegacyProfile
