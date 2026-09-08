import A12Kernel.Elaboration.StaticDiagnostic

/-! # A validation rule read backwards as a repeatability declaration

The Kernel scans a model's rules for one shape — a **count of repetitions compared against a numeric
constant** — and reads it backwards as a *restriction* on how many repetitions that carrier may have.
This is the third place the Kernel treats an ordinary validation rule as a declaration in disguise,
after the dynamic-enumeration derivation and the auto-generated formal rules, and like those it has
its own vocabulary of refusals that reaches a consumer through no other route.

**One mechanism, two carriers.** The form serial counts root-group repetitions, a group counts its
own contexts; the bound derivation, the three-way outcome and the aggregation are shared, and the two
differ only in which class they report and whether the message names a path.

**The bound depends on strictness, and the constant may sit on either side.** A rule fires on the
*violation*, so `count > K` declares a maximum of `K` while `count ≥ K` declares `K - 1`. Writing the
constant first mirrors the operator without changing the meaning, so four spellings collapse onto two
bounds — and the same numeral therefore means different things in the strict and non-strict forms.

**The outcome is three-way and the middle is the refusal, which makes it non-monotone.** A derived
maximum of two or more is accepted; a maximum of exactly **one** is refused, because restricting a
carrier to a single repetition this way is not allowed; and a maximum **below** one is *silently
ignored* — the rule simply does not count as a restriction. So a consumer guarding "the maximum must
be at least two" reports on a bound of zero, which the Kernel does not.

**Aggregation is by minimum, and a refused rule contributes nothing.** Several rules may restrict one
carrier and the smallest bound wins. The refusal is decided per rule before any aggregation, so one
rule deriving a maximum of one refuses even when another would have restricted the same carrier to
five, and an ignored rule is absent from the minimum rather than contributing an unbounded value.

**The group side additionally gates the operand's shape**, six ways: the operator must be the
filled-group count, over exactly one entity, with no semantic index, no filter condition, a wildcard
at the lowest level and no wildcard above it. An operand failing any of these is not a restriction at
all — not a refusal, just an ordinary rule.

**Evidence.** Source-derived, with a measured negative that bounds the claim honestly. A rule
matching every precondition above and deriving a maximum of exactly one — the refusing case — is
**admitted** by the candidate-rule gate, persists, and leaves the model valid under the whole-model
gate ([checkpoint](../../docs/SOURCES.md#src-repeatability-restriction)). So the rule shape is legal
and the restriction pass is simply not part of either gate; it belongs to a rule-collection
meta-information pass that no route this project has reaches. Neither class has a witness, and both
are stated here as the total function the Kernel computes.

This module carries no rendered message text, by the licensing boundary in [`CLAUDE.md`](../../CLAUDE.md).
-/

namespace A12Kernel

/-- Which repetition count a restricting rule reads. -/
inductive RepetitionCarrier where
  /-- Root-group repetitions — the form serial number. -/
  | formSerial
  /-- A named repeatable group's own contexts. -/
  | groupContext
  deriving Repr, DecidableEq

/-- The class each carrier reports when the derived maximum is one. -/
def RepetitionCarrier.restrictionToOne : RepetitionCarrier → KernelStaticDiagnostic
  | .formSerial => .maxLfdNrRestrictionToOne
  | .groupContext => .maxGroupRestrictionToOne

/-- The four admitted comparison spellings. The count may stand on either side, with the operator
mirrored; what survives that mirroring is only whether the comparison is strict. -/
inductive RestrictionComparison where
  /-- `count > K` -/
  | countGreaterThan
  /-- `count ≥ K` -/
  | countAtLeast
  /-- `K < count` -/
  | constantLessThan
  /-- `K ≤ count` -/
  | constantAtMost
  deriving Repr, DecidableEq

/-- Whether the comparison is strict. This is the whole of what the spelling contributes. -/
def RestrictionComparison.isStrict : RestrictionComparison → Bool
  | .countGreaterThan | .constantLessThan => true
  | .countAtLeast | .constantAtMost => false

/-- **The declared maximum.** The rule fires on the violation, so a strict comparison admits the
constant itself and a non-strict one admits one fewer. -/
def declaredMaximum (comparison : RestrictionComparison) (constant : Int) : Int :=
  if comparison.isStrict then constant else constant - 1

/-- What one candidate rule amounts to. -/
inductive RestrictionOutcome where
  /-- The rule restricts the carrier to this maximum, which is always at least two. -/
  | restricts (maximum : Int)
  /-- The derived maximum is exactly one and the rule is refused. -/
  | refused (diagnostic : KernelStaticDiagnostic)
  /-- The derived maximum is below one; the rule is neither a restriction nor an error. -/
  | ignored
  deriving Repr, DecidableEq

/-- **The three-way outcome for one rule**, decided before any aggregation. -/
def restrictionOutcome (carrier : RepetitionCarrier) (comparison : RestrictionComparison)
    (constant : Int) : RestrictionOutcome :=
  let maximum := declaredMaximum comparison constant
  if maximum == 1 then .refused carrier.restrictionToOne
  else if maximum < 1 then .ignored
  else .restricts maximum

/-- The maximum a rule contributes to aggregation, if any. A refused rule contributes nothing, and so
does an ignored one — for different reasons that the outcome keeps apart. -/
def RestrictionOutcome.contributedMaximum : RestrictionOutcome → Option Int
  | .restricts maximum => some maximum
  | _ => none

/-- **Aggregation across a carrier's rules: the smallest bound wins.** `none` means no rule restricts
the carrier, which leaves its declared repeatability standing. -/
def effectiveMaximum (outcomes : List RestrictionOutcome) : Option Int :=
  outcomes.filterMap RestrictionOutcome.contributedMaximum |>.foldl
    (fun best maximum => some (match best with | none => maximum | some current => min current maximum))
    none

/-- Every class the rules of one carrier report, in rule order. -/
def restrictionRefusals (carrier : RepetitionCarrier)
    (rules : List (RestrictionComparison × Int)) : List KernelStaticDiagnostic :=
  rules.filterMap fun rule =>
    match restrictionOutcome carrier rule.1 rule.2 with
    | .refused diagnostic => some diagnostic
    | _ => none

/-- The group side's operand shape, whose six conditions must all hold for the rule to be read as a
restriction at all. An operand failing any of them makes the rule ordinary rather than refused. -/
structure GroupCountOperand where
  /-- The operator is the filled-group count. -/
  isFilledGroupCount : Bool := true
  /-- Exactly one entity in the list. -/
  singleEntity : Bool := true
  /-- No semantic index on that entity. -/
  noSemanticIndex : Bool := true
  /-- No filter condition on that entity. -/
  noFilterCondition : Bool := true
  /-- The lowest index is a wildcard. -/
  wildcardAtLowestLevel : Bool := true
  /-- No index above the lowest is a wildcard. -/
  noWildcardAbove : Bool := true
  deriving Repr, DecidableEq

/-- Whether the operand is read as a group-repetition count. -/
def GroupCountOperand.isRestrictionShape (operand : GroupCountOperand) : Bool :=
  operand.isFilledGroupCount && operand.singleEntity && operand.noSemanticIndex &&
    operand.noFilterCondition && operand.wildcardAtLowestLevel && operand.noWildcardAbove

/-- The group side's outcome, shape gate first. A rule whose operand is not the restriction shape is
an ordinary rule and is ignored here, never refused. -/
def groupRestrictionOutcome (operand : GroupCountOperand) (comparison : RestrictionComparison)
    (constant : Int) : RestrictionOutcome :=
  if operand.isRestrictionShape then restrictionOutcome .groupContext comparison constant
  else .ignored

end A12Kernel
