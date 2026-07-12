/- # A12Kernel.Cell — the phase-sensitive cell model

Refines `spec/13`'s three-state `CellState` (empty ≠ invalid) into two levels: an
invariant `CheckedCell` (raw presence + parsed value + formal findings), and a
*phase-indexed* read producing a `CellObservation`, where the same formal invalidity
surfaces as `unknown` in validation but `poison` in computation.

Crucially, **empty-substitution does not happen in the read** — the consuming operator
decides what an empty operand means (number→`0` in `<`, but skipped by `Max`/`Min`;
string→`""` in concat, but ignored by `==`). See [`docs/ARCHITECTURE.md`](../docs/ARCHITECTURE.md). -/
import A12Kernel.Core

namespace A12Kernel

/-- Why a cell is formally invalid (the "five+ invalidity sources" of `spec/02` §3, routed
    through a single `formalCheck`). Puts the cell in the not-check-relevant state, uses a
    fixed non-authorable message, and blocks the field from all author rules. -/
inductive FormalCause where
  | malformed                -- not well-formed for the field's type (bad date/number/…)
  | declaredConstraint       -- pattern / length / range / scale violation
  | unsupportedCharacter     -- outside the legal charset (default BMP)
  | leadingOrTrailingSpace
  | required                 -- required-and-empty
  | duplicateIndex           -- index field not unique across its column
  | overRepetition           -- rows beyond declared repeatability
  | customValidation         -- a registered custom field-type validator rejected it
  deriving Repr, DecidableEq

/-- The evaluation phase; the *same* formal invalidity reads differently per phase. -/
inductive Phase where
  | validation
  | computation
  deriving Repr, DecidableEq

/-- The invariant classification of a raw cell, before any phase reads it. `parsed` is
    `some` iff the raw content is well-formed for the field's type. -/
structure CheckedCell where
  rawPresent : Bool
  parsed     : Option Value
  findings   : List FormalCause
  deriving Repr, DecidableEq

/-- A phase read of a cell. `unknown` / `poison` are the validation / computation faces of
    formal invalidity; there is **no** empty-substitution here — the operator applies it. -/
inductive CellObservation where
  | empty
  | value   (v : Value)
  | unknown (cause : FormalCause)   -- validation face of a formal error
  | poison  (cause : FormalCause)   -- computation face: aborts the computing instance
  deriving Repr, DecidableEq

-- Next (Semantics stage): the total functions
--   formalCheck : FieldPolicy → RawCell     → CheckedCell
--   observeCell : Phase → FieldPolicy → CheckedCell → CellObservation
-- neither of which may collapse the three states into `Option`.

end A12Kernel
