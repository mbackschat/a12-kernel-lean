import A12Kernel.Semantics.FullDate

/-! # Resolved Date-range overlap

This capsule starts after both endpoints have been decoded and admitted as full Date values. It deliberately keeps inverted ranges representable because the overlap predicate treats them as non-overlapping rather than assuming ordered input. Field observation, skipped-cell derivation, authored operand grouping, filtering, polarity, and scalar-versus-list assembly belong to later consuming capsules.
-/

namespace A12Kernel

/-- Two resolved full-Date endpoints before the overlap predicate applies its ordering guard. -/
structure ResolvedDateRange where
  start : FullDate
  finish : FullDate
  deriving Repr, DecidableEq

/-- The resolved endpoint order kept explicit so inversion cannot be silently normalized. -/
inductive DateRangeDirection where
  | ordered
  | inverted
  deriving Repr, DecidableEq

namespace ResolvedDateRange

/-- Classify the supplied endpoint order. Equal endpoints form an ordered one-day range. -/
def direction (range : ResolvedDateRange) : DateRangeDirection :=
  if range.finish.before range.start then .inverted else .ordered

/-- Closed-interval overlap with the kernel's explicit invalid-range guard. -/
def overlaps (left right : ResolvedDateRange) : Bool :=
  match left.direction, right.direction with
  | .ordered, .ordered =>
      !left.finish.before right.start &&
        !right.finish.before left.start
  | _, _ => false

end ResolvedDateRange

/-- Whether any two distinct occurrences in one ordered resolved stream overlap. Equal range values at two positions remain two occurrences. -/
def anyPairDateRangesOverlap : List ResolvedDateRange → Bool
  | [] => false
  | current :: rest =>
      rest.any current.overlaps || anyPairDateRangesOverlap rest

end A12Kernel
