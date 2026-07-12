/-! # A12Kernel.Core — the core types that carry the semantics

Straight from `spec/13-lean-encoding-guide.md` §1 ("The core types") and
`spec/SEMANTICS-MAP.md` §6. These few types are the skeleton every operator
clause will hang off; the staged build order (encoding guide §3) fills them in
bottom-up. Get these right and the rest is careful per-operator work.

Nothing here transcribes engine source — it is the language-neutral *shape* the
spec prescribes. See `CLAUDE.md` for the clean-room / source-of-truth rules. -/

namespace A12Kernel

/-- A Number field's **scale** is a STATIC field property, not a runtime datum: it
    gates `==`/`!=` at parse time, while ordering is scale-exempt. Do not attach it
    to the runtime value. (`spec/04-numbers-and-decimals.md`, §5) -/
structure NumField where
  /-- max fractional digits (always bounded; a missing scale ⇒ `0`). -/
  scale  : Nat
  /-- `positivesOnly = false`; drives directional fillability, *not* a min bound. -/
  signed : Bool
  deriving Repr, DecidableEq

/-- **Kleene truth.** The third value (`unknown`) arises *only* from a read of a
    formally-invalid cell — the connectives themselves are two-valued and use the
    strong-Kleene tables. There is deliberately **no negation combinator**: the
    language has no generic `Not`. (`spec/02-logic-and-formal-errors.md`, §1/§3) -/
inductive K where
  | tru
  | fls
  | unknown
  deriving Repr, DecidableEq

namespace K

/-- Strong-Kleene conjunction: `fls` dominates; the result is `unknown` only when no
    operand is `fls` and they are not both `tru`. -/
def and : K → K → K
  | .fls, _    => .fls
  | _,    .fls => .fls
  | .tru, .tru => .tru
  | _,    _    => .unknown

/-- Strong-Kleene disjunction: `tru` dominates; the result is `unknown` only when no
    operand is `tru` and they are not both `fls`. -/
def or : K → K → K
  | .tru, _    => .tru
  | _,    .tru => .tru
  | .fls, .fls => .fls
  | _,    _    => .unknown

end K

/-- The **value domain** (sketch — expanded per kind in later stages). Numbers are
    exact rationals; rescale is applied *explicitly* at the `spec/04` points, never
    carried implicitly. Dates/times/fragments/ranges/custom land in later stages.
    (`spec/13-lean-encoding-guide.md` §1(c)) -/
inductive Value where
  | num  (d : Rat)          -- exact; the field's `scale` lives in `NumField`, not here
  | str  (s : String)
  | bool (b : Bool)
  | conf (b : Bool)         -- Confirm: an empty Confirm reads `False` (unlike Boolean)
  | enum (stored : String)  -- compared by the stored token, never the display text
  deriving Repr, DecidableEq

/-- The **three cell states** — `empty ≠ invalid`, and this is non-negotiable: a
    two-state `Option Value` cannot express the language. Every read resolves to
    exactly one of these (via a single `formalCheck`, added in the next stage)
    before anything else looks at it. (`spec/02-logic-and-formal-errors.md`, §3) -/
inductive CellState where
  | empty                    -- not specified
  | filled (v : Value)       -- a well-formed value of the field's type
  | notCheckRelevant         -- present but formally invalid ⇒ "unknown"
  deriving Repr, DecidableEq

/-- A fired message's **polarity** — the second lattice, computed alongside truth.
    `value` = "what you entered is wrong" (no fill helps); `omission` = "something is
    missing" (a fill could clear it). Under `And`, omission wins; under `Or`, value
    wins. Derived from directional fillability. (`spec/10-validation-and-polarity.md`, §12) -/
inductive Polarity where
  | value
  | omission
  deriving Repr, DecidableEq

/-- The **firing outcome** = truth × polarity folded into one 3-way lattice; what
    evaluating a rule against a row yields. (`spec/13-lean-encoding-guide.md` §1(e)) -/
inductive Outcome where
  | firedValue
  | firedOmission
  | notFired
  deriving Repr, DecidableEq

/-- A repeatable level in the model tree (placeholder identity; refined when the
    iteration environment lands — `spec/07-repetition-and-iteration.md`, §9). -/
abbrev RepeatableLevel := String

/-- The **iteration environment**: a binding of each enclosing repeatable level to a
    chosen row index. Evaluation always happens *at* such a context; iteration
    produces a set of them. Model it explicitly rather than threading positions
    implicitly. (`spec/07-repetition-and-iteration.md`, §9 / `spec/08-paths-and-references.md`, §10) -/
abbrev Env := List (RepeatableLevel × Nat)

/-! ## Sanity checks — the strong-Kleene tables (double as regression guards). -/

example : K.and .fls .unknown = .fls     := rfl
example : K.and .tru .unknown = .unknown := rfl
example : K.and .tru .tru     = .tru     := rfl
example : K.or  .tru .unknown = .tru     := rfl
example : K.or  .fls .unknown = .unknown := rfl
example : K.or  .fls .fls     = .fls     := rfl

end A12Kernel
