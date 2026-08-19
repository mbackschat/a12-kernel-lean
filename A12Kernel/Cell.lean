/- # A12Kernel.Cell — the phase-sensitive cell model

Implements `spec/13`'s phase-sensitive cell boundary as two levels: an invariant
`CheckedCell` (raw placement + optional typed semantic value + formal findings), and a
*phase-indexed* read producing a `CellObservation`, where the same formal invalidity
surfaces as `unknown` in validation but `poison` in computation.

Crucially, **empty-substitution does not happen in the read** — the consuming operator
decides what an empty operand means (number→`0` in `<`, but skipped by `Max`/`Min`;
string→`""` in concat, but ignored by `==`). See [`docs/ARCHITECTURE.md`](../docs/ARCHITECTURE.md). -/
import A12Kernel.Core

namespace A12Kernel

/-- The exact consumer-owned failure returned by a registered custom field validator. This is distinct from the fixed declarative predefined-type fallback. -/
structure RegisteredCustomRejection where
  projectCode : String
  messageTemplate : Option String := none
  deriving Repr, DecidableEq

/-- Why a checked cell is unavailable. The ordinary constructors are formal-invalidity sources routed through `formalCheck`; `computedDependency` is the cause-blind transient marker placed only in a computation overlay after an earlier computed target became invalid. -/
inductive FormalCause where
  | malformed                -- not well-formed for the field's type (bad date/number/…)
  | dateFormat               -- stored Date text does not match its declaration or a real calendar day
  | dateTooEarly             -- stored Date is below the universal floor or enabled pre-1900 boundary
  | dateRangeSeparator       -- the stored DateRange omits its declared range separator
  | dateRangeFormat          -- one stored DateRange endpoint is lexically or calendrically malformed
  | dateRangeInvalid         -- both endpoints are valid, but start is after finish
  | dateRangeTooEarly        -- the ordered range starts before the universal Gregorian floor
  | booleanToken             -- stored Boolean token outside exact lowercase `true` / `false`
  | confirmToken             -- stored Confirm token outside exact lowercase `true`
  | declaredConstraint       -- pattern / length / range / scale violation
  | unsupportedCharacter     -- outside the legal charset (default BMP)
  | leadingOrTrailingSpace
  | required                 -- required-and-empty
  | duplicateIndex           -- index field not unique across its column
  | overRepetition           -- rows beyond declared repeatability
  | customValidation         -- fixed declarative predefined-type fallback
  | registeredCustomValidation (rejection : RegisteredCustomRejection)
  | computedDependency       -- invalid computed target; carries no producer error or message
  deriving Repr, DecidableEq

/-- The evaluation phase; the *same* formal invalidity reads differently per phase. -/
inductive Phase where
  | validation
  | computation
  deriving Repr, DecidableEq

/-- The invariant classification of a raw cell, before any phase reads it. `parsed` is
    `some` exactly when the placement supplies a checked semantic value; a clean
    present-empty placement carries neither a parsed value nor a finding. -/
structure CheckedCell (α : Type := Value) where
  /-- Whether the field has a physical placement. A present-empty cell keeps this true
      while carrying no parsed value. -/
  rawPresent : Bool
  parsed     : Option α
  findings   : List FormalCause
  deriving Repr, DecidableEq

/-- A phase read of a cell. `unknown` / `poison` are the validation / computation faces of
    formal invalidity; there is **no** empty-substitution here — the operator applies it. -/
inductive CellObservation (α : Type := Value) where
  | empty
  | value   (v : α)
  | unknown (cause : FormalCause)   -- validation face of a formal error
  | poison  (cause : FormalCause)   -- computation face: aborts the computing instance
  deriving Repr, DecidableEq

-- Implemented in `A12Kernel.Semantics.Observation` as the total functions
--   formalCheck : FieldPolicy → RawCell → CheckedCell
--   observeCell : Phase → CheckedCell α → CellObservation α
-- neither of which may collapse the three states into `Option`.

end A12Kernel
