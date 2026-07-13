/- # A12Kernel.Document — addressing and the document instance

The document must represent **instantiated rows independently of cell values**: a
blank-but-instantiated repeat row is observable content, so `GroupFilled`, requiredness,
the row-gate, and repeatable-group quantifiers all misbehave if row existence is inferred
from non-empty cells. (`spec/01`, `spec/07`; see [`docs/ARCHITECTURE.md`](../docs/ARCHITECTURE.md).) -/
import A12Kernel.Core

namespace A12Kernel

abbrev GroupId := Nat
abbrev FieldId := Nat

/-- A repeatable level, identified by its group. -/
abbrev RepeatableLevel := GroupId

/-- Address of one instantiated repeatable row: its group plus the repetition indices of
    the enclosing repeatable levels (never an ordinal into storage — rows are addressed by
    semantic key, `spec/08`). -/
structure RowAddr where
  group : GroupId
  path  : List Nat
  deriving Repr, DecidableEq

/-- Address of one cell: a field at a repetition path. -/
structure CellAddr where
  field : FieldId
  path  : List Nat
  deriving Repr, DecidableEq

/-- A document instance. `instantiatedRows` is kept **separate** from `rawCells`; a `List`
    (not `Finset`) because ordering is observable (`FirstFilledValue`, computation
    scheduling, poison reads) and to stay dependency-free / `#eval`-able. `rawCells` yields
    a cell's raw text when present.

    String length/pattern semantics still to pin: the kernel counts Java `String.length`
    (UTF-16 code units), not Lean USVs — but the default BMP legal charset makes any
    non-BMP input a formal error, so the two counts agree by default (cross-check
    the a12-dmkits interpreter under `../a12-rulekit/interpreter/` when the string stage lands). -/
structure Document where
  instantiatedRows : List RowAddr
  rawCells         : CellAddr → Option String

/-- The **iteration environment**: each enclosing repeatable level bound to a chosen row
    index. Evaluation happens *at* such a context; iteration produces a set of them.
    (`spec/07` §9 / `spec/08` §10) -/
abbrev Env := List (RepeatableLevel × Nat)

/-- An injected instant (placeholder epoch value; a real calendar lands in the dates stage). -/
abbrev Instant := Int

/-- The evaluation **world** — everything `Today` / `Now` / custom hooks would otherwise
    read from ambient state, kept as explicit input so `eval` / `compute` stay pure (no
    `IO`; determinism given a clock). Timezone semantics (with DST spring-gap / autumn-fold
    and a pinned tz-rule version — the one still-open a12-dmkits divergence (IG62 in `../a12-rulekit/`)),
    the custom-condition / validator oracles, and the label provider join here with the
    dates / custom stages. -/
structure World where
  now      : Instant
  baseYear : Option Int
  deriving Repr, DecidableEq

end A12Kernel
