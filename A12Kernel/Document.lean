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

    `rawCells` assigns no universal String-empty or length policy. The narrow checked
    `Length` consumer counts UTF-16 code units; patterns, coercions, and the remaining
    String consumers stay outside the current document semantics. -/
structure Document where
  instantiatedRows : List RowAddr
  rawCells         : CellAddr → Option String

/-- The **iteration environment**: each enclosing repeatable level bound to a chosen row
    index. Evaluation happens *at* such a context; iteration produces a set of them.
    (`spec/07` §9 / `spec/08` §10) -/
abbrev Env := List (RepeatableLevel × Nat)

/-- A model-zone `Today` oracle maps the checked model's exact zone id and injected clock instant to midnight on that zone's local civil date. A complete kernel consumer supplies every model-legal legacy zone; a narrower consumer fails closed with `none` for every unsupported id. -/
abbrev ModelZoneTodayOracle := String → Instant → Option Instant

/-- The evaluation **world** — everything `Today` / `Now` / custom hooks would otherwise read from ambient state, kept as explicit input so `eval` / `compute` stay pure. The model-zone oracle is function-valued because the canonical legal zone-id domain is wider than this repository's concrete UTC/Berlin profiles. Custom-condition / validator oracles and the label provider likewise belong to later custom stages. -/
structure World where
  now      : Instant
  baseYear : Option Int
  modelZoneToday? : ModelZoneTodayOracle := fun _ _ => none

/-- Resolve `Today` through the explicit profile selected for the checked model. -/
def World.today? (world : World) (zoneId : String) : Option Instant :=
  world.modelZoneToday? zoneId world.now

end A12Kernel
