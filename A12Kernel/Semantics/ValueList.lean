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

/-- `AtLeastOne` skips empty and UNKNOWN cells on both sides and fires only on a present match. -/
def evalValueListAtLeastOne
    (fields values : ResolvedValueListSide kind) : Verdict :=
  if fields.anyMatches values then
    .fired (if fields.hasHaving || values.hasHaving then .omission else .value)
  else
    .notFired

/-- `No` is poisoned by UNKNOWN on either side; otherwise it fires exactly when no present field matches. -/
def evalValueListNo
    (fields values : ResolvedValueListSide kind) : Verdict :=
  if fields.hasUnknown || values.hasUnknown then
    .unknown
  else if fields.anyMatches values then
    .notFired
  else
    .fired
      (if fields.hasHaving || values.hasHaving ||
          fields.hasMissingPotential || values.hasMissingPotential then
        .omission
      else
        .value)

/-- `NotAll` ignores UNKNOWN fields but is poisoned by an UNKNOWN values member. It needs a present field outside the present member set. -/
def evalValueListNotAll
    (fields values : ResolvedValueListSide kind) : Verdict :=
  if !fields.hasPresent then
    .notFired
  else if values.hasUnknown then
    .unknown
  else if fields.anyOutside values then
    .fired
      (if fields.hasHaving || values.hasHaving ||
          values.hasMissingPotential then
        .omission
      else
        .value)
  else
    .notFired

inductive ValueListQuantifier where
  | atLeastOne
  | no
  | notAll
  deriving Repr, DecidableEq

/-- Only `No` can fire when expansion yields no present field cells. -/
def ValueListQuantifier.canFireOnEmpty : ValueListQuantifier → Bool
  | .no => true
  | .atLeastOne | .notAll => false

/-- Closed dispatch over the three value-list quantifiers. Each arm delegates to its own semantic clause rather than a generic quantifier fold. -/
def ValueListQuantifier.eval (quantifier : ValueListQuantifier)
    (fields values : ResolvedValueListSide kind) : Verdict :=
  match quantifier with
  | .atLeastOne => evalValueListAtLeastOne fields values
  | .no => evalValueListNo fields values
  | .notAll => evalValueListNotAll fields values

end A12Kernel
