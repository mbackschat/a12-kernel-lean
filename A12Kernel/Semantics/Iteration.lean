import A12Kernel.Semantics.FlatValidation
import A12Kernel.Semantics.NumericAggregate

/-! # A12Kernel.Semantics.Iteration — single-level star and uncorrelated Having

The first repetition capsule is intentionally narrow: one repeatable group, an ordered
list of explicitly instantiated rows, validation reads, an optional row-local `Having`
condition, and a numeric starred `Sum` used to observe selection. It does not represent
`$`, nested repetition, general aggregate elaboration, computation, partial validation,
or filtered-result polarity.
-/

namespace A12Kernel

abbrev RowIndex := Nat

/-- The validation view of one repeatable group. Candidates are explicit instantiated rows in semantic repetition order; they are not inferred from filled cells and do not include a declared-but-uninstantiated tail. Checked constructors must establish that order—the finite one-level boundary requires the exact `1 … n` prefix, while general nested construction is owned by `StarAddressing`. Every candidate is an instantiated repeat row, so its row-local `Having` condition passes the full-validation content gate. -/
structure SingleGroupValidationContext where
  group : RepeatableLevel
  candidates : List RowIndex
  read : RowIndex → FieldId → CheckedCell

def RowIndex.firstDuplicate? : List RowIndex → Option RowIndex
  | [] => none
  | row :: rest => if rest.contains row then some row else RowIndex.firstDuplicate? rest

def RowIndex.hasDuplicates (rows : List RowIndex) : Bool :=
  (RowIndex.firstDuplicate? rows).isSome

/-- Kernel-correspondence boundary for the explicit row list. Repetition indices are
    1-based and each instantiated row occurs once; the list itself carries document
    order. The low-level evaluator remains total outside this predicate. -/
def SingleGroupValidationContext.WellFormed
    (context : SingleGroupValidationContext) : Prop :=
  RowIndex.hasDuplicates context.candidates = false ∧
    context.candidates.all (0 < ·) = true

instance (context : SingleGroupValidationContext) : Decidable context.WellFormed := by
  unfold SingleGroupValidationContext.WellFormed
  infer_instance

def SingleGroupValidationContext.atRow (context : SingleGroupValidationContext)
    (row : RowIndex) : FlatContext :=
  { read := context.read row }

def SingleGroupValidationContext.envAt (context : SingleGroupValidationContext)
    (row : RowIndex) : Env :=
  [(context.group, row)]

/-- A numeric starred selection in the admitted one-group fragment. `none` is the
    unfiltered control; `some condition` is an uncorrelated, row-local `Having`. -/
structure SingleStar where
  valueField : FlatNumberField
  having : Option FlatCondition
  deriving Repr, DecidableEq

/-- A `Having` row is kept exactly when its condition is true. Polarity is irrelevant to
    selection; false and validation-unknown both drop the row. -/
def Verdict.keepsHaving : Verdict → Bool
  | .fired _ => true
  | .notFired | .unknown => false

def SingleStar.keeps (star : SingleStar) (context : SingleGroupValidationContext)
    (row : RowIndex) : Bool :=
  match star.having with
  | none => true
  | some condition =>
      (condition.evalFull (context.atRow row) true).keepsHaving

/-- Declarative row-keep predicate. This is intentionally stated without referring to
    the executable `Bool`: an unfiltered row is kept, while a filtered row is kept when
    its condition has a fired verdict of either polarity. -/
def SingleStar.KeepsRow (star : SingleStar) (context : SingleGroupValidationContext)
    (row : RowIndex) : Prop :=
  match star.having with
  | none => True
  | some condition => ∃ polarity, condition.evalFull (context.atRow row) true = .fired polarity

/-- Independent ordered selection relation over the candidate list. It exposes exactly
    which input row is kept or dropped and preserves input order in the output. -/
inductive SelectRows (star : SingleStar) (context : SingleGroupValidationContext) :
    List RowIndex → List RowIndex → Prop where
  | nil : SelectRows star context [] []
  | keep (kept : star.KeepsRow context row)
      (tail : SelectRows star context rows selected) :
      SelectRows star context (row :: rows) (row :: selected)
  | drop (dropped : ¬star.KeepsRow context row)
      (tail : SelectRows star context rows selected) :
      SelectRows star context (row :: rows) selected

/-- Select rows before any aggregate operand is observed. `List.filter` preserves the candidates' checked semantic order and multiplicity. -/
def SingleStar.select (star : SingleStar)
    (context : SingleGroupValidationContext) : List RowIndex :=
  context.candidates.filter (star.keeps context)

/-- Result of the narrow validation-only numeric fold. Empty selected cells are skipped;
    an empty kept selection therefore has sum zero. A formally invalid selected cell (or
    a defensive wrong-kind value) makes the aggregate unknown and retains the first
    observed cause. -/
inductive NumberFold where
  | value (sum : Rat)
  | unknown (cause : FormalCause)
  deriving Repr, DecidableEq

/-- Classify one selected checked-row read for the shared resolved Number aggregate scan. -/
def NumberFold.classifyRow (context : SingleGroupValidationContext)
    (field : FlatNumberField) (row : RowIndex) : ValueListCell .number :=
  field.valueListCell (context.atRow row)

/-- Project the shared encounter-ordered precision-50 Number sum to the older amount-or-cause result used by the one-group iteration boundary. -/
def NumberFold.sumRows (context : SingleGroupValidationContext)
    (field : FlatNumberField) (rows : List RowIndex) : NumberFold :=
  match scanNumericSumCells (rows.map (NumberFold.classifyRow context field)) with
  | .ok total => .value (total.getD 0)
  | .error cause => .unknown cause

/-- Filter first, then fold only the selected rows' numeric cells. -/
def SingleStar.sumSelected (star : SingleStar)
    (context : SingleGroupValidationContext) : NumberFold :=
  NumberFold.sumRows context star.valueField (star.select context)

private def equalityHolds (op : EqualityOp) (left right : Rat) : Bool :=
  match op with
  | .equal => NumericComparisonOp.equal.holds left right
  | .notEqual => NumericComparisonOp.notEqual.holds left right

/-- Truth-only comparison used by the first external selection witnesses. Filtered-star
    polarity is intentionally deferred until directional fillability is modeled. -/
def SingleStar.evalSumEquality (star : SingleStar)
    (context : SingleGroupValidationContext) (op : EqualityOp) (expected : Rat) : K :=
  match star.sumSelected context with
  | .value actual => if equalityHolds op actual expected then .tru else .fls
  | .unknown _ => .unknown

end A12Kernel
