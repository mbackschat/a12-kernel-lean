import A12Kernel.Cell

/-! # Resolved `Time(...)` construction

This capsule starts after static component checking and Java `BigDecimal.intValue` conversion. The grammar admits zero through three leading components; code generation supplies zero for every omitted trailing component. Static checking excludes fractional, negative, and out-of-range constants and requires field/extractor shapes that produce bounded integers, while the runtime still distinguishes a missing component from a fully present impossible clock.

The result retains that distinction for later DateTime composition. Formal unavailability dominates missingness in authored order, missingness dominates calendar reality, and only three present components reach the whole-second `TimeOfDay` constructor. Component authoring, model-relative field-policy admission, extraction, and repeatable reads remain outside this resolved boundary.
-/

namespace A12Kernel

/-- The four grammar shapes of `Time(...)`; each name identifies the last explicitly supplied component. -/
inductive TimeConstructionArity where
  | zero
  | hour
  | minute
  | second
  deriving Repr, DecidableEq

/-- One already checked and integer-converted Time component. -/
inductive TimeConstructionComponent where
  | value (amount : Int)
  | empty
  | nonRelevant
  | unavailable (cause : FormalCause)
  deriving Repr, DecidableEq

/-- The reason-bearing result of resolved `Time(...)` construction. -/
inductive TimeConstructionResult where
  | value (time : TimeOfDay)
  | incomplete
  | unreal
  | nonRelevant
  | unavailable (cause : FormalCause)
  deriving Repr, DecidableEq

private def timeOfIntHms? (hour minute second : Int) : Option TimeOfDay :=
  if hour < 0 || minute < 0 || second < 0 then
    none
  else
    TimeOfDay.ofHms? hour.toNat minute.toNat second.toNat

private def evaluateTimeComponents :
    TimeConstructionComponent → TimeConstructionComponent →
      TimeConstructionComponent → TimeConstructionResult
  | .unavailable cause, _, _ => .unavailable cause
  | _, .unavailable cause, _ => .unavailable cause
  | _, _, .unavailable cause => .unavailable cause
  | .nonRelevant, _, _ | _, .nonRelevant, _ | _, _, .nonRelevant =>
      .nonRelevant
  | .empty, _, _ | _, .empty, _ | _, _, .empty => .incomplete
  | .value hour, .value minute, .value second =>
      match timeOfIntHms? hour minute second with
      | some time => .value time
      | none => .unreal

namespace TimeConstructionArity

/-- Evaluate the authored prefix and supply fixed zeroes for every omitted trailing component. Inputs outside the prefix are deliberately not observed. -/
def evaluate (arity : TimeConstructionArity)
    (hour minute second : TimeConstructionComponent) :
    TimeConstructionResult :=
  match arity with
  | .zero =>
      evaluateTimeComponents (.value 0) (.value 0) (.value 0)
  | .hour =>
      evaluateTimeComponents hour (.value 0) (.value 0)
  | .minute =>
      evaluateTimeComponents hour minute (.value 0)
  | .second =>
      evaluateTimeComponents hour minute second

end TimeConstructionArity

end A12Kernel
