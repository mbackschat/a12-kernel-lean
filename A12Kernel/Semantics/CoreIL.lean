import A12Kernel.Semantics.ValueList
import A12Kernel.Semantics.NumericArithmetic
import A12Kernel.Semantics.NumericComparison

/-!
# A semantic core IL — first slice, value-list quantifiers

The object an independent consumer implements *instead of* A12: the smallest set of constructs
into which a checked surface family lowers without losing a kernel-observable distinction.

This slice covers the value-list quantifier family only. Its purpose is to test one claim —
that surface operators collapse onto fewer independent decision points than they present — so
the core deliberately carries no construct that exists only to name a surface operator. The
adequacy argument is [`Proofs/CoreIL.lean`](../Proofs/CoreIL.lean); an unprovable preservation
theorem is how an over-flattened core is meant to be detected.

Scope, obligations, exclusions, and the recorded success criteria live in
[`docs/SEMANTIC-CORE-IL-PROPOSAL.md`](../../docs/SEMANTIC-CORE-IL-PROPOSAL.md).
-/

namespace A12Kernel

/-- Whether a witness is a present value **inside** or **outside** the collected member set.
This is the only difference between the two firing quantifiers. -/
inductive CoreMemberTest where
  | inside
  | outside
  deriving Repr, DecidableEq

/-- Whether an unavailable member poisons the collected set. `AtLeastOne` collects present
values only; `No` and `NotAll` stop at the first unavailable or non-relevant operand. -/
inductive CoreCollect where
  | presentOnly
  | poisoning
  deriving Repr, DecidableEq

/-- The two ordered folds over a fields stream.

`findWitness` is operand-granular and fires at the first operand holding a witness.
`scanUntilMatch` is cell-granular, unavailability-sensitive, and inverted — a match makes it
*not* fire and an exhausted scan fires. The split is the `No`-versus-`NotAll` asymmetry
(`spec/06` §B.3), not a naming of two operators. -/
inductive CoreFold where
  | findWitness (test : CoreMemberTest)
  | scanUntilMatch
  deriving Repr, DecidableEq

/-- A core term. `guardPresent` makes an ordering constraint structural: its guarded stream is
consulted before the body's, so `NotAll`'s fields-before-values order is visible in the term
rather than asserted in prose. -/
inductive CoreTerm where
  | read (slot : Nat)
  | collect (policy : CoreCollect) (src : CoreTerm)
  | fold (f : CoreFold) (members source : CoreTerm)
  | guardPresent (guard : CoreTerm) (body : CoreTerm)
  -- E2 (numeric stressor). Each operator is a *parameter* of a shared node rather than a
  -- construct of its own, which is the property E2 exists to test.
  | amountLit (amount : Rat)
  | numArith (op : NumericArithmeticOp) (left right : CoreTerm)
  | numRound (mode : DecimalRoundingMode) (places : RoundingPlaces) (source : CoreTerm)
  | numCompare (op : NumericComparisonOp) (left right : CoreTerm)
  deriving Repr

/-- A core result. Three constructors because the core must keep member collection, poisoning,
and verdicts distinct; collapsing `poisoned` into `verdict .unknown` would erase the reason a
result is unknown before any consumer chooses to project it. -/
inductive CoreValue (kind : ValueListKind) where
  | stream (sides : List (ResolvedValueListSide kind))
  | members (atoms : List (ValueListAtom kind)) (omission : Bool)
  | poisoned
  | verdict (v : Verdict)
  -- E2 adds two result domains. Numeric evaluation is not verdict-valued until a comparison
  -- projects it, so collapsing these into `verdict` would erase the staging the kernel has.
  | numeric (operand : NumericOperand)
  | amount (value : Rat)

/-- The evaluation environment: one addressed slot space, read by `CoreTerm.read`.

This is the E2 correction. `eval` previously took one positional argument per family — two
operand streams, then a numeric operand list — which is a union of per-family environments
rather than an abstraction over them, and grows with every family added. A single slot space
keeps `eval`'s signature and every preservation theorem's shape stable: a new family contributes
a *lowering* and a slot layout, not a new parameter. A consumer implements one `read`.

Slot layouts are named below rather than left as bare indices at each call site, so the layout a
lowering assumes is stated once and pinned by that family's preservation theorem. -/
structure CoreEnv (kind : ValueListKind) where
  slots : List (CoreValue kind)

namespace CoreEnv

/-- Value-list layout: the fields stream is slot 0 and the values stream is slot 1. -/
def ofValueList (fields values : List (ResolvedValueListSide kind)) : CoreEnv kind :=
  ⟨[.stream fields, .stream values]⟩

/-- Numeric layout: two already-classified comparison operands. -/
def ofNumericPair (left right : NumericOperand) : CoreEnv kind :=
  ⟨[.numeric left, .numeric right]⟩

/-- An environment with no readable slot, for terms that read none. -/
def empty : CoreEnv kind := ⟨[]⟩

end CoreEnv

namespace CoreTerm

/-- Collect present members in operand order, tracking whether a filtered operand selected a
present member. No operand can poison this policy. -/
def collectPresentOnly :
    List (ResolvedValueListSide kind) → List (ValueListAtom kind) × Bool
  | [] => ([], false)
  | operand :: remaining =>
      let (members, filtered) := collectPresentOnly remaining
      (operand.presentValues ++ members,
        (operand.hasHaving && operand.hasPresent) || filtered)

/-- Collect present members in operand order, stopping at the first unavailable or
non-relevant operand. Accumulates omission potential from filters, empties, and omitted tails. -/
def collectPoisoning :
    List (ResolvedValueListSide kind) → CoreValue kind
  | [] => .members [] false
  | operand :: remaining =>
      if operand.hasUnknown || operand.hasNonRelevant then
        .poisoned
      else
        match collectPoisoning remaining with
        | .members atoms omission =>
            .members (operand.presentValues ++ atoms)
              (operand.hasHaving || operand.hasMissingPotential || omission)
        | other => other

/-- Fire at the first operand holding a present value that satisfies `test`. Polarity is
`omission` when the deciding operand is filtered or the member set carries omission potential —
one formula for both firing quantifiers. -/
def runFindWitness (test : CoreMemberTest) (members : List (ValueListAtom kind))
    (omission : Bool) : List (ResolvedValueListSide kind) → Verdict
  | [] => .notFired
  | operand :: remaining =>
      let witness := operand.presentValues.any fun value =>
        match test with
        | .inside => valueListMembersContain members value
        | .outside => !valueListMembersContain members value
      if witness then
        .fired (if omission || operand.hasHaving then .omission else .value)
      else
        runFindWitness test members omission remaining

/-- Scan operands in order, delegating each operand's cells to the family's existing cell scan.
A match terminates non-firing before any later cell; a reached unavailable cell suppresses. -/
def runScanUntilMatch (members : List (ValueListAtom kind)) :
    List (ResolvedValueListSide kind) → Bool → Verdict
  | [], omission => .fired (if omission then .omission else .value)
  | operand :: remaining, omission =>
      if operand.hasNonRelevant then
        .unknown
      else
        match scanValueListNoCells members operand.cells
            (omission || operand.hasHaving || operand.hasUninstantiatedTail) with
        | .matched => .notFired
        | .unknown => .unknown
        | .exhausted next => runScanUntilMatch members remaining next

/-- Evaluate a core term against the two operand streams. A malformed term — one whose operand
shapes do not fit its constructor — yields `poisoned` rather than a fabricated verdict; the
lowering never produces one, which `lowerValueListQuantifier_wellFormed` records. -/
def eval (env : CoreEnv kind) : CoreTerm → CoreValue kind
  | .read slot =>
      match env.slots[slot]? with
      | some value => value
      | none => .poisoned
  | .collect policy src =>
      match eval env src with
      | .stream sides =>
          match policy with
          | .presentOnly =>
              let (atoms, filtered) := collectPresentOnly sides
              .members atoms filtered
          | .poisoning => collectPoisoning sides
      | _ => .poisoned
  | .fold f members source =>
      match eval env members, eval env source with
      | .members atoms omission, .stream sides =>
          match f with
          | .findWitness test => .verdict (runFindWitness test atoms omission sides)
          | .scanUntilMatch => .verdict (runScanUntilMatch atoms sides omission)
      | .poisoned, _ => .verdict .unknown
      | _, _ => .poisoned
  | .guardPresent guard body =>
      match eval env guard with
      | .stream sides =>
          if sides.any ResolvedValueListSide.hasPresent then
            eval env body
          else
            .verdict .notFired
      | _ => .poisoned
  -- E2 fragment. Each case delegates to the family's own primitive rather than restating it,
  -- so preservation is about the *shape* of the lowering, not about re-deriving arithmetic.
  | .amountLit value => .amount value
  | .numArith op left right =>
      match eval env left, eval env right with
      | .amount a, .amount b => .amount (op.eval a b)
      | _, _ => .poisoned
  | .numRound mode places source =>
      match eval env source with
      | .amount a => .amount (roundDecimal mode a places)
      | _ => .poisoned
  | .numCompare op left right =>
      match eval env left, eval env right with
      | .numeric a, .numeric b => .verdict (op.eval a b)
      | _, _ => .poisoned

end CoreTerm

/-- Lower the three value-list quantifiers into the core.

Total on the checked type, so coverage of the family is type-checked rather than asserted. The
three operators use **two** folds: `AtLeastOne` and `NotAll` share `findWitness` and differ only
in membership direction, while `No` needs the inverted unavailability-sensitive scan. `NotAll`'s
fields-presence guard is structural here — removing it would return UNKNOWN where the contract
requires non-firing, which is exactly [`LF72`](../../docs/LEAN-FINDINGS.md). -/
def lowerValueListQuantifier : ValueListQuantifier → CoreTerm
  | .atLeastOne =>
      .fold (.findWitness .inside)
        (.collect .presentOnly (.read 1)) (.read 0)
  | .no =>
      .fold .scanUntilMatch
        (.collect .poisoning (.read 1)) (.read 0)
  | .notAll =>
      .guardPresent (.read 0)
        (.fold (.findWitness .outside)
          (.collect .poisoning (.read 1)) (.read 0))


/-- Lower a direct numeric comparison between two classified operand slots. -/
def lowerDirectNumericComparison (op : NumericComparisonOp) : CoreTerm :=
  .numCompare op (.read 0) (.read 1)

/-- Lower one rounded binary arithmetic stage over two literal amounts. The rounding mode and
places are term data, so the exact-decimal invariant is syntactic rather than a convention. -/
def lowerRoundedArithmetic (op : NumericArithmeticOp) (mode : DecimalRoundingMode)
    (places : RoundingPlaces) (left right : Rat) : CoreTerm :=
  .numRound mode places (.numArith op (.amountLit left) (.amountLit right))

end A12Kernel
