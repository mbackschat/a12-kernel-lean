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

/-- Partial all-rows aggregate evaluation distinguishes the kernel's rule-level filtered skip, a relevance failure, and an evaluated numeric result. Nonrelevance is not forged into a formal cell cause. -/
inductive PartialValidationAggregateResult where
  | skippedHaving
  | nonRelevant
  | evaluated (operand : NumericOperand)
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

/-- One already-expanded and already-filtered authored operand. An uninstantiated declared tail is tracked separately because it contributes no cell but can still make a firing omission-typed. Partial nonrelevance stays on this exact operand so an ordered consumer can distinguish an earlier decision from a later unavailable extent. -/
structure ResolvedValueListSide (kind : ValueListKind) where
  cells : List (ValueListCell kind)
  hasUninstantiatedTail : Bool
  hasHaving : Bool
  hasNonRelevant : Bool := false

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

/-- Concatenate two already-resolved occurrences while preserving every source's tail and filter uncertainty. Authored operand order remains cell order. -/
def append (left right : ResolvedValueListSide kind) :
    ResolvedValueListSide kind :=
  { cells := left.cells ++ right.cells
    hasUninstantiatedTail :=
      left.hasUninstantiatedTail || right.hasUninstantiatedTail
    hasHaving := left.hasHaving || right.hasHaving
    hasNonRelevant := left.hasNonRelevant || right.hasNonRelevant }

/-- Check whether every reached cell is available, stopping at the first formal cause. -/
def available (side : ResolvedValueListSide kind) : Except FormalCause Unit :=
  ValueListCell.scanPresent (fun _ _ => ()) side.cells ()

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

def presentValues (side : ResolvedValueListSide kind) :
    List (ValueListAtom kind) :=
  side.cells.filterMap fun
    | .present value => some value
    | .empty | .unknown _ => none

end ResolvedValueListSide

/-- Resolve authored operands lazily from left to right. A consumer-selected terminal result or the first unavailable resolved cell stops before any later operand is resolved. The caller supplies the accumulator update because some consumers retain declaration metadata in addition to the common value side. -/
def scanResolvedValueListOperands {operand state terminal error : Type}
    {kind : ValueListKind}
    (resolve : operand → Except error (Sum (ResolvedValueListSide kind) terminal))
    (onUnavailable : FormalCause → terminal)
    (append : state → operand → ResolvedValueListSide kind → state) :
    List operand → state → Except error (Sum state terminal)
  | [], accumulated => pure (.inl accumulated)
  | operand :: remaining, accumulated => do
      match ← resolve operand with
      | .inr result => pure (.inr result)
      | .inl side =>
          match side.available with
          | .error cause => pure (.inr (onUnavailable cause))
          | .ok () =>
              scanResolvedValueListOperands resolve onUnavailable append remaining
                (append accumulated operand side)

/-- Compatibility view for established single-operand partial routes. New ordered routes retain nonrelevance on each `ResolvedValueListSide`; this wrapper remains the pre-existing scalar/one-star API until those callers are widened. -/
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

/-- The observable stop of the fields-side `No` scan. A match and an unavailable cell are distinct terminals; exhaustion retains omission polarity. -/
inductive ValueListNoFieldsResult where
  | matched
  | unknown
  | exhausted (omission : Bool)

def valueListMembersContain (members : List (ValueListAtom kind))
    (candidate : ValueListAtom kind) : Bool :=
  members.any (ValueListAtom.equal candidate)

/-- Scan fields-side `No` cells in encounter order. A match wins over every later cell; an unavailable cell wins over every later match. -/
def scanValueListNoCells (members : List (ValueListAtom kind)) :
    List (ValueListCell kind) → Bool → ValueListNoFieldsResult
  | [], omission => .exhausted omission
  | .present value :: remaining, omission =>
      if valueListMembersContain members value then
        .matched
      else
        scanValueListNoCells members remaining omission
  | .empty :: remaining, _ =>
      scanValueListNoCells members remaining true
  | .unknown _ :: _, _ => .unknown

/-- Shared `No` core: the values side is poison-checked before fields, while a fields-side match terminates before a later formal failure. Partial extent/nonrelevance remains a side-wide prerequisite because the older classified side does not retain its cell position. -/
def evalClassifiedValueListNo
    (fields values : ResolvedValueListQuantifierSide kind) : Verdict :=
  if values.hasUnknown || fields.hasNonRelevant then
    .unknown
  else
    match scanValueListNoCells values.side.presentValues fields.side.cells
        (fields.side.hasHaving || values.side.hasHaving ||
          fields.side.hasUninstantiatedTail ||
          values.side.hasMissingPotential) with
    | .matched => .notFired
    | .unknown => .unknown
    | .exhausted omission =>
        .fired (if omission then .omission else .value)

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

/-- Resolve both authored sides in the same operator-specific order as the ordered evaluator. Thunks preserve the structural short circuit: a failure on the first side prevents resolving the second. -/
def ValueListQuantifier.resolveSidesOrdered
    {fields values error : Type}
    (quantifier : ValueListQuantifier)
    (resolveFields : Unit → Except error fields)
    (resolveValues : Unit → Except error values) :
    Except error (fields × values) :=
  match quantifier with
  | .notAll => do
      let fields ← resolveFields ()
      let values ← resolveValues ()
      pure (fields, values)
  | .atLeastOne | .no => do
      let values ← resolveValues ()
      let fields ← resolveFields ()
      pure (fields, values)

private def collectAtLeastOneValueListMembers :
    List (ResolvedValueListSide kind) → List (ValueListAtom kind) × Bool
  | [] => ([], false)
  | side :: remaining =>
      let (members, filteredPresent) :=
        collectAtLeastOneValueListMembers remaining
      (side.presentValues ++ members,
        (side.hasHaving && side.hasPresent) || filteredPresent)

private inductive PoisoningValueListMembers (kind : ValueListKind) where
  | unknown
  | known (members : List (ValueListAtom kind)) (omission : Bool)

private def collectPoisoningValueListMembers :
    List (ResolvedValueListSide kind) → PoisoningValueListMembers kind
  | [] => .known [] false
  | side :: remaining =>
      if side.hasUnknown || side.hasNonRelevant then
        .unknown
      else
        match collectPoisoningValueListMembers remaining with
        | .unknown => .unknown
        | .known members omission =>
            .known (side.presentValues ++ members)
              (side.hasHaving || side.hasMissingPotential || omission)

private def scanValueListAtLeastOneFields
    (members : List (ValueListAtom kind)) (filteredPresent : Bool) :
    List (ResolvedValueListSide kind) → Verdict
  | [] => .notFired
  | side :: remaining =>
      if side.presentValues.any (valueListMembersContain members) then
        .fired (if side.hasHaving || filteredPresent then .omission else .value)
      else
        scanValueListAtLeastOneFields members filteredPresent remaining

private def scanValueListNoFields
    (members : List (ValueListAtom kind)) :
    List (ResolvedValueListSide kind) → Bool → Verdict
  | [], omission => .fired (if omission then .omission else .value)
  | side :: remaining, omission =>
      if side.hasNonRelevant then
        .unknown
      else
        match scanValueListNoCells members side.cells
            (omission || side.hasHaving || side.hasUninstantiatedTail) with
        | .matched => .notFired
        | .unknown => .unknown
        | .exhausted nextOmission =>
            scanValueListNoFields members remaining nextOmission

private def orderedValueListFieldsHavePresent :
    List (ResolvedValueListSide kind) → Bool
  | [] => false
  | side :: remaining =>
      side.hasPresent || orderedValueListFieldsHavePresent remaining

private def scanValueListNotAllFields
    (members : List (ValueListAtom kind)) (valuesOmission : Bool) :
    List (ResolvedValueListSide kind) → Verdict
  | [] => .notFired
  | side :: remaining =>
      if side.presentValues.any fun value =>
          !valueListMembersContain members value then
        .fired (if valuesOmission || side.hasHaving then .omission else .value)
      else
        scanValueListNotAllFields members valuesOmission remaining

/-- Evaluate full-validation value-list operands without erasing authored operand boundaries. Values are resolved before fields for `AtLeastOne` and `No`; `NotAll` first checks for any present field, then resolves values, then restarts its fields scan. Filter polarity follows the matching/outside fields operand, while `AtLeastOne` retains a values-side filter only when that operand selected a present member. -/
def ValueListQuantifier.evalOrdered (quantifier : ValueListQuantifier)
    (fields values : List (ResolvedValueListSide kind)) : Verdict :=
  match quantifier with
  | .atLeastOne =>
      let (members, filteredPresent) :=
        collectAtLeastOneValueListMembers values
      if members.isEmpty then
        .notFired
      else
        scanValueListAtLeastOneFields members filteredPresent fields
  | .no =>
      match collectPoisoningValueListMembers values with
      | .unknown => .unknown
      | .known members omission =>
          scanValueListNoFields members fields omission
  | .notAll =>
      if orderedValueListFieldsHavePresent fields then
        match collectPoisoningValueListMembers values with
        | .unknown => .unknown
        | .known members omission =>
            scanValueListNotAllFields members omission fields
      else
        .notFired

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

/-- Compatibility dispatch for one classified operand per side. Wider multi-operand routes use `evalOrdered` directly so operand-local nonrelevance is not flattened into this single-side view. -/
def ValueListQuantifier.evalClassified (quantifier : ValueListQuantifier)
    (fields values : ResolvedValueListQuantifierSide kind) : Verdict :=
  match quantifier with
  | .atLeastOne => evalClassifiedValueListAtLeastOne fields values
  | .no => evalClassifiedValueListNo fields values
  | .notAll => evalClassifiedValueListNotAll fields values

/-- Closed dispatch over one resolved operand per side. -/
def ValueListQuantifier.eval (quantifier : ValueListQuantifier)
    (fields values : ResolvedValueListSide kind) : Verdict :=
  quantifier.evalClassified (.ofResolved fields) (.ofResolved values)

end A12Kernel
