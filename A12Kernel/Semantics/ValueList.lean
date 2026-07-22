import A12Kernel.Semantics.NumericComparison

/-! # A12Kernel.Semantics.ValueList — resolved value-list quantifiers

This capsule starts after both operands have been expanded per cell and filtered by any `Having` clause. It models only the Number and canonical stored-token kinds selected for this resolved capsule. The three operators remain separate because their UNKNOWN and polarity clauses are intentionally asymmetric.
-/

namespace A12Kernel

/-- The two comparable runtime domains admitted by this resolved capsule. String and Enumeration values share the token domain only after a checked layer has established their comparability and canonicalized the stored value. -/
inductive ValueListKind where
  | number
  | token
  deriving Repr, DecidableEq

/-- Type-indexed atoms make a mixed Number/token value list unrepresentable at this boundary. -/
abbrev ValueListAtom : ValueListKind → Type
  | .number => Rat
  | .token => String

/-- One expanded operand cell after validation-phase observation. Empty is not substituted, and UNKNOWN remains distinct from an absent cell. -/
inductive ValueListCell (kind : ValueListKind) where
  | present (value : ValueListAtom kind)
  | empty
  | unknown (cause : FormalCause)

/-- One already-expanded and already-filtered operand side. An uninstantiated declared tail is tracked separately because it contributes no cell but can still make a firing omission-typed. -/
structure ResolvedValueListSide (kind : ValueListKind) where
  cells : List (ValueListCell kind)
  hasUninstantiatedTail : Bool
  hasHaving : Bool

namespace ValueListCell

def isEmpty : ValueListCell kind → Bool
  | .empty => true
  | _ => false

def isUnknown : ValueListCell kind → Bool
  | .unknown _ => true
  | _ => false

/-- Scan already-classified cells from left to right, skipping empty cells and stopping at the first unavailable cell. The caller supplies the accumulator meaning; use this only for consumers whose own semantics have exactly this branch structure. -/
def scanPresent (step : state → ValueListAtom kind → state) :
    List (ValueListCell kind) → state → Except FormalCause state
  | [], accumulator => .ok accumulator
  | .empty :: cells, accumulator => scanPresent step cells accumulator
  | .unknown cause :: _, _ => .error cause
  | .present value :: cells, accumulator =>
      scanPresent step cells (step accumulator value)

end ValueListCell

namespace ValueListAtom

/-- Number membership uses the ordinary scale-19 comparison boundary; canonical tokens use exact equality. -/
def equal : {kind : ValueListKind} →
    ValueListAtom kind → ValueListAtom kind → Bool
  | .number, left, right => NumericComparisonOp.equal.holds left right
  | .token, left, right => left == right

end ValueListAtom

namespace ResolvedValueListSide

def hasEmpty (side : ResolvedValueListSide kind) : Bool :=
  side.cells.any ValueListCell.isEmpty

def hasUnknown (side : ResolvedValueListSide kind) : Bool :=
  side.cells.any ValueListCell.isUnknown

def hasPresent (side : ResolvedValueListSide kind) : Bool :=
  side.cells.any fun cell =>
    match cell with
    | .present _ => true
    | .empty | .unknown _ => false

/-- Whether later instantiation or filling can add a value to this resolved operand side. -/
def hasMissingPotential (side : ResolvedValueListSide kind) : Bool :=
  side.hasEmpty || side.hasUninstantiatedTail

def contains (side : ResolvedValueListSide kind)
    (candidate : ValueListAtom kind) : Bool :=
  side.cells.any fun cell =>
    match cell with
    | .present member => ValueListAtom.equal candidate member
    | .empty | .unknown _ => false

def anyMatches (fields values : ResolvedValueListSide kind) : Bool :=
  fields.cells.any fun cell =>
    match cell with
    | .present value => values.contains value
    | .empty | .unknown _ => false

def anyOutside (fields values : ResolvedValueListSide kind) : Bool :=
  fields.cells.any fun cell =>
    match cell with
    | .present value => !values.contains value
    | .empty | .unknown _ => false

end ResolvedValueListSide

/-- The quantifier-specific view of one resolved side. Partial validation removes nonrelevant cells before classification but retains their existence because `No` and values-side `NotAll` treat them as UNKNOWN. The ordinary resolved side remains unchanged for aggregates and other consumers. -/
structure ResolvedValueListQuantifierSide (kind : ValueListKind) where
  side : ResolvedValueListSide kind
  hasNonRelevant : Bool := false

namespace ResolvedValueListQuantifierSide

def ofResolved (side : ResolvedValueListSide kind) :
    ResolvedValueListQuantifierSide kind :=
  { side }

def hasUnknown (side : ResolvedValueListQuantifierSide kind) : Bool :=
  side.side.hasUnknown || side.hasNonRelevant

def hasPresent (side : ResolvedValueListQuantifierSide kind) : Bool :=
  side.side.hasPresent

def anyMatches (fields values : ResolvedValueListQuantifierSide kind) : Bool :=
  fields.side.anyMatches values.side

def anyOutside (fields values : ResolvedValueListQuantifierSide kind) : Bool :=
  fields.side.anyOutside values.side

@[simp]
theorem ofResolved_side (side : ResolvedValueListSide kind) :
    (ofResolved side).side = side := by
  rfl

@[simp]
theorem ofResolved_hasNonRelevant (side : ResolvedValueListSide kind) :
    (ofResolved side).hasNonRelevant = false := by
  rfl

@[simp]
theorem ofResolved_hasUnknown (side : ResolvedValueListSide kind) :
    (ofResolved side).hasUnknown = side.hasUnknown := by
  simp [ofResolved, hasUnknown]

@[simp]
theorem ofResolved_hasPresent (side : ResolvedValueListSide kind) :
    (ofResolved side).hasPresent = side.hasPresent := by
  rfl

@[simp]
theorem ofResolved_anyMatches (fields values : ResolvedValueListSide kind) :
    (ofResolved fields).anyMatches (ofResolved values) =
      fields.anyMatches values := by
  rfl

@[simp]
theorem ofResolved_anyOutside (fields values : ResolvedValueListSide kind) :
    (ofResolved fields).anyOutside (ofResolved values) =
      fields.anyOutside values := by
  rfl

end ResolvedValueListQuantifierSide

/-- Shared `AtLeastOne` core: empty, formally unavailable, and nonrelevant cells on both sides are absent from the present-value search. -/
def evalClassifiedValueListAtLeastOne
    (fields values : ResolvedValueListQuantifierSide kind) : Verdict :=
  if fields.anyMatches values then
    .fired (if fields.side.hasHaving || values.side.hasHaving then .omission else .value)
  else
    .notFired

/-- Shared `No` core: formal unavailability or partial nonrelevance on either side poisons the absence claim. -/
def evalClassifiedValueListNo
    (fields values : ResolvedValueListQuantifierSide kind) : Verdict :=
  if fields.hasUnknown || values.hasUnknown then
    .unknown
  else if fields.anyMatches values then
    .notFired
  else
    .fired
      (if fields.side.hasHaving || values.side.hasHaving ||
          fields.side.hasMissingPotential || values.side.hasMissingPotential then
        .omission
      else
        .value)

/-- Shared `NotAll` core: fields-side unavailability is skipped, values-side unavailability poisons after a present subject exists. -/
def evalClassifiedValueListNotAll
    (fields values : ResolvedValueListQuantifierSide kind) : Verdict :=
  if !fields.hasPresent then
    .notFired
  else if values.hasUnknown then
    .unknown
  else if fields.anyOutside values then
    .fired
      (if fields.side.hasHaving || values.side.hasHaving ||
          values.side.hasMissingPotential then
        .omission
      else
        .value)
  else
    .notFired

/-- `AtLeastOne` over an ordinary resolved side is the full-relevance specialization of the shared classified core. -/
def evalValueListAtLeastOne
    (fields values : ResolvedValueListSide kind) : Verdict :=
  evalClassifiedValueListAtLeastOne (.ofResolved fields) (.ofResolved values)

/-- `No` over an ordinary resolved side is the full-relevance specialization of the shared classified core. -/
def evalValueListNo
    (fields values : ResolvedValueListSide kind) : Verdict :=
  evalClassifiedValueListNo (.ofResolved fields) (.ofResolved values)

/-- `NotAll` over an ordinary resolved side is the full-relevance specialization of the shared classified core. -/
def evalValueListNotAll
    (fields values : ResolvedValueListSide kind) : Verdict :=
  evalClassifiedValueListNotAll (.ofResolved fields) (.ofResolved values)

inductive ValueListQuantifier where
  | atLeastOne
  | no
  | notAll
  deriving Repr, DecidableEq

/-- The scalar membership pair specializes the resolved list quantifiers without introducing boolean negation. -/
inductive ValueListMembershipOp where
  | included
  | notIncluded
  deriving Repr, DecidableEq

/-- Literal-only scalar Included is one-field `AtLeastOne`; NotIncluded is one-field `NotAll`, preserving the shared empty/UNKNOWN no-fire behavior. -/
def ValueListMembershipOp.quantifier : ValueListMembershipOp → ValueListQuantifier
  | .included => .atLeastOne
  | .notIncluded => .notAll

/-- Only `No` can fire when expansion yields no present field cells. -/
def ValueListQuantifier.canFireOnEmpty : ValueListQuantifier → Bool
  | .no => true
  | .atLeastOne | .notAll => false

/-- Closed dispatch after phase-specific relevance has been classified. This is the sole quantifier evaluator used by both full and partial routes. -/
def ValueListQuantifier.evalClassified (quantifier : ValueListQuantifier)
    (fields values : ResolvedValueListQuantifierSide kind) : Verdict :=
  match quantifier with
  | .atLeastOne => evalClassifiedValueListAtLeastOne fields values
  | .no => evalClassifiedValueListNo fields values
  | .notAll => evalClassifiedValueListNotAll fields values

/-- Closed dispatch over the three value-list quantifiers. Each arm delegates to its own semantic clause rather than a generic quantifier fold. -/
def ValueListQuantifier.eval (quantifier : ValueListQuantifier)
    (fields values : ResolvedValueListSide kind) : Verdict :=
  quantifier.evalClassified (.ofResolved fields) (.ofResolved values)

end A12Kernel
