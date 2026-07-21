/-! # A12Kernel.Core — the truth/polarity algebra and the value domain

The foundational types every operator clause hangs off. Refines
`spec/13-lean-encoding-guide.md` §1 and `spec/SEMANTICS-MAP.md` §6, taking the verdict
algebra in the unified 4-state form (rationale + the full decision record in
[`docs/ARCHITECTURE.md`](../docs/ARCHITECTURE.md)).

Nothing here transcribes engine source — see `CLAUDE.md` for the clean-room rule. -/

namespace A12Kernel

/-! ## Kleene truth -/

/-- **Kleene truth.** `unknown` arises from an unavailable validation operand, including
    a formally invalid cell or a partial-validation reference outside the relevant set.
    The binary `And`/`Or` connectives use the strong-Kleene tables. There is deliberately
    **no negation combinator** — the language has no generic `Not`. (`spec/02`, §1/§3;
    `spec/10`, §5) -/
inductive K where
  | tru
  | fls
  | unknown
  deriving Repr, DecidableEq

namespace K

/-- Strong-Kleene conjunction: `fls` dominates; `unknown` only when no operand is `fls`
    and they are not both `tru`. -/
def and : K → K → K
  | .fls, _    => .fls
  | _,    .fls => .fls
  | .tru, .tru => .tru
  | _,    _    => .unknown

/-- Strong-Kleene disjunction: `tru` dominates; `unknown` only when no operand is `tru`
    and they are not both `fls`. -/
def or : K → K → K
  | .tru, _    => .tru
  | _,    .tru => .tru
  | .fls, .fls => .fls
  | _,    _    => .unknown

end K

/-! ## Message polarity and the verdict algebra -/

/-- A fired message's **polarity** (the kernel's message *type*): `value` = "what you
    entered is wrong" (no fill helps); `omission` = "something is missing" (a fill could
    clear it). Derived from directional fillability. (`spec/10`, §12) -/
inductive Polarity where
  | value
  | omission
  deriving Repr, DecidableEq

/-- A condition's **verdict** — truth and polarity in one lattice. `fired p` is the
    Kleene-`tru` case tagged with the polarity a fired message carries; `notFired` is
    `fls`; `unknown` is the suppressed/invalid case. Unified deliberately: a condition
    result always has a defined truth, so `unknown` *must* be representable — which a bare
    `firedValue | firedOmission | notFired` outcome cannot express. -/
inductive Verdict where
  | notFired
  | fired (p : Polarity)
  | unknown
  deriving Repr, DecidableEq

namespace Verdict

/-- Conjunction (`And`): strong-Kleene on truth, and **omission wins** among fired
    operands. `notFired` (Kleene-false) dominates; `fired ∧ unknown = unknown`. -/
def conj : Verdict → Verdict → Verdict
  | .notFired,       _              => .notFired
  | _,               .notFired      => .notFired
  | .unknown,        _              => .unknown
  | _,               .unknown       => .unknown
  | .fired .omission, _             => .fired .omission
  | _,               .fired .omission => .fired .omission
  | .fired .value,   .fired .value  => .fired .value

/-- Disjunction (`Or`): strong-Kleene on truth, and **value wins** among fired operands.
    `fired` (Kleene-true) dominates; `notFired ∨ unknown = unknown`. -/
def disj : Verdict → Verdict → Verdict
  | .fired .value,   _              => .fired .value
  | _,               .fired .value  => .fired .value
  | .fired .omission, _             => .fired .omission
  | _,               .fired .omission => .fired .omission
  | .unknown,        _              => .unknown
  | _,               .unknown       => .unknown
  | .notFired,       .notFired      => .notFired

end Verdict

/-! ## Number scale and the value domain -/

/-- The statically derived decimal scale of a numeric expression. Exact scales are signed because stripping trailing zeros from an integer constant can produce a negative scale; runtime values do not carry this authoring summary. (`spec/04`) -/
inductive ScaleInfo where
  | exact (digits : Int)
  | unknown
  deriving Repr, DecidableEq

/-- A Number *field*'s static configuration. `scale` gates `==`/`!=` at parse time (ordering
    is scale-exempt); `signed` drives fillability, not a min bound. (`spec/04`) -/
structure NumField where
  scale  : Nat
  signed : Bool
  deriving Repr, DecidableEq

/-- Exact runtime instant identity in epoch milliseconds. Authored Date, Time, and DateTime values are whole-second, but the injected `Now` clock may retain a sub-second remainder. Calendar and zone resolution live in the temporal semantics. -/
structure Instant where
  epochMillis : Int
  deriving Repr, DecidableEq

namespace Instant

/-- Embed a whole-second temporal value into the exact runtime coordinate. -/
def ofEpochSecond (epochSecond : Int) : Instant :=
  { epochMillis := epochSecond * 1000 }

end Instant

/-- The **value domain** (expanded per kind in later stages). Numbers are exact rationals;
    the field's `scale` lives in `NumField`, and *stored-form / representation* equality
    (`7` vs `7.00`) is a separate rendered-string concern, not carried here. Arithmetic
    applies explicit rounding (scale-19 `HALF_UP` for compares, `MathContext(50)` for
    intermediates) at the `spec/04` points, so exactness never silently diverges from the
    engine. (`spec/13` §1) -/
inductive Value where
  | num  (d : Rat)
  | str  (s : String)
  | bool (b : Bool)
  | conf (b : Bool)         -- Stored Confirm values are `true`; `false` is comparison-local substitution.
  | enum (stored : String)  -- compared by the stored token, never the display text
  deriving Repr, DecidableEq

/-! ## Sanity checks (double as regression guards) -/

-- strong-Kleene
example : K.and .fls .unknown = .fls     := rfl
example : K.and .tru .unknown = .unknown := rfl
example : K.or  .tru .unknown = .tru     := rfl
example : K.or  .fls .unknown = .unknown := rfl

-- verdict algebra — the spec's `healthy Or / And broken` cases
example : Verdict.disj (.fired .value) .unknown = .fired .value := rfl  -- fired Or unknown fires
example : Verdict.conj .notFired       .unknown = .notFired     := rfl  -- notFired And unknown suppressed
example : Verdict.conj (.fired .value) .unknown = .unknown      := rfl  -- fired And unknown = unknown
example : Verdict.disj .notFired       .unknown = .unknown      := rfl
-- polarity precedence
example : Verdict.conj (.fired .value) (.fired .omission) = .fired .omission := rfl  -- omission wins under And
example : Verdict.disj (.fired .value) (.fired .omission) = .fired .value    := rfl  -- value wins under Or

end A12Kernel
