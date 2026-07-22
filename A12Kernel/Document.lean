/- # A12Kernel.Document — addressing and the document instance

The document must represent **instantiated rows independently of cell values**: a
blank-but-instantiated repeat row is observable content, so `GroupFilled`, requiredness,
the row-gate, and repeatable-group quantifiers all misbehave if row existence is inferred
from non-empty cells. (`spec/01`, `spec/07`; see [`docs/ARCHITECTURE.md`](../docs/ARCHITECTURE.md).) -/
import A12Kernel.Cell

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

/-- Capability projection of one versioned legacy model-zone account. `Today` clears the local clock at an exact instant; local-label resolution supports stored values, Base Year, and later calendar consumers. A complete kernel consumer supplies every model-legal id; a narrower consumer returns `none` for every unsupported id. -/
structure ModelZoneRules where
  today? : String → Instant → Option Instant
  resolveLocal? : String → Int → Nat → Nat → Nat → Nat → Nat → Option Instant

def ModelZoneRules.unavailable : ModelZoneRules where
  today? := fun _ _ => none
  resolveLocal? := fun _ _ _ _ _ _ _ => none

/-- Exact arguments supplied to one registered custom field-type validator. Bounds are already defaulted by the checked declaration consumer. -/
structure CustomFieldValidationContext where
  locale : String
  minLength : Nat
  maxLength : Nat
  isDisplayValue : Bool
  deriving Repr, DecidableEq

/-- A pure registered custom field validator. Acceptance is `none`; rejection retains the consumer-owned project payload. -/
abbrev RegisteredCustomFieldValidator :=
  String → CustomFieldValidationContext → Option RegisteredCustomRejection

/-- The evaluation **world** — everything `Today` / `Now` / custom hooks would otherwise read from ambient state, kept as explicit input so `eval` / `compute` stay pure. The model-zone oracle is function-valued because the canonical legal zone-id domain is wider than this repository's concrete UTC/Berlin profiles. Custom-condition / validator oracles and the label provider likewise belong to later custom stages. -/
structure World where
  now      : Instant
  modelZoneRules : ModelZoneRules := ModelZoneRules.unavailable
  customFieldValidator? : String → Option RegisteredCustomFieldValidator := fun _ => none

/-- Resolve `Today` through the explicit profile selected for the checked model. -/
def World.today? (world : World) (zoneId : String) : Option Instant :=
  world.modelZoneRules.today? zoneId world.now

/-- Resolve one complete local wall label through the same model-zone account used by `Today`. -/
def World.resolveLocal? (world : World) (zoneId : String)
    (year : Int) (month day hour minute second : Nat) : Option Instant :=
  world.modelZoneRules.resolveLocal? zoneId year month day hour minute second

/-- Resolve a registered validator by the exact authored custom type name. -/
def World.resolveCustomFieldValidator? (world : World) (name : String) :
    Option RegisteredCustomFieldValidator :=
  world.customFieldValidator? name

end A12Kernel
