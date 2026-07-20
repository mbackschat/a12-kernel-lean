import A12Kernel.Semantics.DateConstruction

/-! # Resolved three-part Date classification executable locks

These cases start after component checking and after a separate calendar resolver has classified an all-present triple. They separate component availability and reality before checking the distinct `Valid` and `Invalid` verdicts; they make no calendar-zone or cutover claim.
-/

namespace A12Kernel.Conformance.DateConstruction

open A12Kernel

private def realParts : DateParts :=
  { year := 2024, month := 6, day := 15 }

/- Three present components retain supplied calendar reality and make only `Valid` fire. -/
example :
    classifyDateConstruction3 .present .present .present (.real realParts) =
      .real realParts := by
  native_decide

example :
    (classifyDateConstruction3 .present .present .present (.real realParts)).validVerdict =
      .fired .value ∧
    (classifyDateConstruction3 .present .present .present (.real realParts)).invalidVerdict =
      .notFired := by
  native_decide

/- A supplied present-but-unreal classification makes `Invalid` fire as VALUE. -/
example :
    (classifyDateConstruction3 .present .present .present .unreal).validVerdict =
      .notFired ∧
    (classifyDateConstruction3 .present .present .present .unreal).invalidVerdict =
      .fired .value := by
  native_decide

/- Every empty position yields the same incomplete reason. -/
example :
    classifyDateConstruction3 .empty .present .present (.real realParts) =
      .incomplete ∧
    classifyDateConstruction3 .present .empty .present (.real realParts) =
      .incomplete ∧
    classifyDateConstruction3 .present .present .empty (.real realParts) =
      .incomplete := by
  native_decide

/- Incomplete input makes `Invalid` OMISSION-typed, not VALUE-typed. -/
example :
    (classifyDateConstruction3 .empty .present .present (.real realParts)).validVerdict =
      .notFired ∧
    (classifyDateConstruction3 .empty .present .present (.real realParts)).invalidVerdict =
      .fired .omission := by
  native_decide

/- An empty component prevents even an unreal all-present classification from being observed. -/
example :
    classifyDateConstruction3 .present .present .empty .unreal =
      .incomplete ∧
    (classifyDateConstruction3 .present .present .empty .unreal).invalidVerdict =
      .fired .omission := by
  native_decide

/- Once the independent row gate admits `Invalid(Date(...))`, all-empty components produce OMISSION. -/
example :
    (classifyDateConstruction3 .empty .empty .empty .unreal).invalidVerdict =
      .fired .omission := by
  native_decide

/- Formal unavailability dominates emptiness and makes both predicates UNKNOWN. -/
example :
    classifyDateConstruction3 .empty .unknown .present .unreal =
      .unknown ∧
    (classifyDateConstruction3 .empty .unknown .present .unreal).validVerdict =
      .unknown ∧
    (classifyDateConstruction3 .empty .unknown .present .unreal).invalidVerdict =
      .unknown := by
  native_decide

end A12Kernel.Conformance.DateConstruction
