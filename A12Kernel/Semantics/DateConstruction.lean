import A12Kernel.Core
import A12Kernel.Semantics.FullDate

/-! # A12Kernel.Semantics.DateConstruction — resolved three-part Date validity

This capsule implements the reason and verdict boundary of [`spec/05-dates-and-time.md` §3](../../spec/05-dates-and-time.md#3-constructing-dates-and-checking-validity). Component authoring and checking have completed, and a separate calendar resolver supplies the reality of an all-present triple. This layer decides only how formal unavailability, emptiness, and that resolved reality combine.

Calendar resolution is deliberately an input. Kernel 30.8.1 uses a model-zone-sensitive hybrid `GregorianCalendar`, while the reusable `CivilDate` account is zone-free and proleptic; using it here would silently disagree for legal dates around zone discontinuities and the historical cutover.

The two-argument Base Year form, four-argument century form, textual component decoding, exact formal causes, row orchestration, concrete calendar resolution, and the stored/computed Date floor remain separate. [`DateConstructionNumeric.lean`](DateConstructionNumeric.lean) owns the direct numeric extractor projection; date differences, reason-bearing DateTime composition, direct Date `Min`/`Max`, shifts, and legacy-calendar month/year operations remain consumer-specific follow-up boundaries. Every consumer must retain this classification rather than collapse it to an optional value.
-/

namespace A12Kernel

/-- Availability of one already-checked Date component. Its numeric value is consumed by the separate calendar resolver only when all three components are present. -/
inductive DateComponentAvailability where
  | present
  | empty
  | unknown
  deriving Repr, DecidableEq

/-- Calendar reality supplied for an all-present component triple. -/
inductive PresentDateReality where
  | real (parts : DateParts)
  | unreal
  deriving Repr, DecidableEq

/-- The reason-bearing result of a resolved three-part Date construction. -/
inductive DateConstructionResult where
  | real (parts : DateParts)
  | incomplete
  | unreal
  | unknown
  deriving Repr, DecidableEq

/-- Combine checked component availability with separately resolved all-present calendar reality. Formal unavailability dominates emptiness; otherwise emptiness prevents the supplied reality from being observed. -/
def classifyDateConstruction3
    (day month year : DateComponentAvailability)
    (reality : PresentDateReality) : DateConstructionResult :=
  match day, month, year with
  | .unknown, _, _ => .unknown
  | _, .unknown, _ => .unknown
  | _, _, .unknown => .unknown
  | .empty, _, _ => .incomplete
  | _, .empty, _ => .incomplete
  | _, _, .empty => .incomplete
  | .present, .present, .present =>
      match reality with
      | .real date => .real date
      | .unreal => .unreal

namespace DateConstructionResult

/-- `Valid(Date(...))` fires as VALUE exactly for a complete real construction. -/
def validVerdict : DateConstructionResult → Verdict
  | .real _ => .fired .value
  | .incomplete | .unreal => .notFired
  | .unknown => .unknown

/-- `Invalid(Date(...))` distinguishes fillable incompleteness from a present-but-unreal value. -/
def invalidVerdict : DateConstructionResult → Verdict
  | .real _ => .notFired
  | .incomplete => .fired .omission
  | .unreal => .fired .value
  | .unknown => .unknown

end DateConstructionResult

end A12Kernel
