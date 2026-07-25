import A12Kernel.Semantics.ValueList

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

/-- Which operand stream a core term reads. The streams are evaluation-time input, so a core
term is a program over them rather than a container for them. -/
inductive CoreSide where
  | fields
  | values
  deriving Repr, DecidableEq

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
  | side (s : CoreSide)
  | collect (policy : CoreCollect) (src : CoreTerm)
  | fold (f : CoreFold) (members source : CoreTerm)
  | guardPresent (guard : CoreTerm) (body : CoreTerm)
  deriving Repr

/-- A core result. Three constructors because the core must keep member collection, poisoning,
and verdicts distinct; collapsing `poisoned` into `verdict .unknown` would erase the reason a
result is unknown before any consumer chooses to project it. -/
inductive CoreValue (kind : ValueListKind) where
  | stream (sides : List (ResolvedValueListSide kind))
  | members (atoms : List (ValueListAtom kind)) (omission : Bool)
  | poisoned
  | verdict (v : Verdict)

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
def eval (fields values : List (ResolvedValueListSide kind)) :
    CoreTerm → CoreValue kind
  | .side .fields => .stream fields
  | .side .values => .stream values
  | .collect policy src =>
      match eval fields values src with
      | .stream sides =>
          match policy with
          | .presentOnly =>
              let (atoms, filtered) := collectPresentOnly sides
              .members atoms filtered
          | .poisoning => collectPoisoning sides
      | _ => .poisoned
  | .fold f members source =>
      match eval fields values members, eval fields values source with
      | .members atoms omission, .stream sides =>
          match f with
          | .findWitness test => .verdict (runFindWitness test atoms omission sides)
          | .scanUntilMatch => .verdict (runScanUntilMatch atoms sides omission)
      | .poisoned, _ => .verdict .unknown
      | _, _ => .poisoned
  | .guardPresent guard body =>
      match eval fields values guard with
      | .stream sides =>
          if sides.any ResolvedValueListSide.hasPresent then
            eval fields values body
          else
            .verdict .notFired
      | _ => .poisoned

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
        (.collect .presentOnly (.side .values)) (.side .fields)
  | .no =>
      .fold .scanUntilMatch
        (.collect .poisoning (.side .values)) (.side .fields)
  | .notAll =>
      .guardPresent (.side .fields)
        (.fold (.findWitness .outside)
          (.collect .poisoning (.side .values)) (.side .fields))

end A12Kernel
