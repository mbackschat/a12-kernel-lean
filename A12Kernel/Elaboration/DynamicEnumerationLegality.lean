/-! # When a rule is a dynamic enumeration, and the twelve ways it fails to be one

A **dynamic enumeration** lets a validation rule double as the declaration of a field's allowed values: the Kernel reads the rule's canonical form backwards and extracts the constants the target field may hold. The derivation that does this runs its own legality check with its own twelve-class vocabulary, and that vocabulary reaches a consumer through no other route — the model-consistency gate never reports one of these classes however the model is shaped.

**The fact a consumer gets wrong first: these diagnostics are not defects.** The derivation is offered the model's whole rule collection and asks of *every* rule "is this a dynamic enumeration in form?", so an ordinary single-leaf rule answers `gateForm` and an ordinary conjunction answers `calcOpForm`. On a model of ordinary rules the collection-wide call returns roughly one refusal per rule and not one of them is a problem. A consumer that surfaces them as model errors rejects almost every real model. The refusal means *not a dynamic enumeration*; only the accepted rules contribute values.

The check is **first-match-wins across four ordered stages**, and a rule is checked in isolation, so the order is observable per rule rather than only in aggregate:

1. **Rule parameters** — the model's world, then the target field's declared type, then whether the target is its group's index field. These run before the condition is even parsed, so a rule whose condition is nonsense still answers with its parameter defect.
2. **The condition, globally** — parallel iteration and `RepetitionNotUnique` are rejected outright, before any structural reading. Both are legal validation constructs; they are excluded here because the derivation has to enumerate the target's values statically.
3. **The canonical form** — the gate `FieldFilled(<target>) And …`, optionally behind one safe guard joined by `Or`. Every structural mismatch collapses onto one code, which is why `gateForm` carries no information about *which* part of the shape was wrong.
4. **The value calculations** — each conjunct is a comparison of the target against a calculation function, and the target reference itself is re-checked here against the gate's.

**The consumers this is shaped for** are [Analyze](../../docs/USE-CASES.md#5-analyze) — deciding "is this rule a dynamic enumeration, and if not, at which stage does it stop being one?", which needs the stage order and not merely the class — and [Explain](../../docs/USE-CASES.md#9-explain), which needs the "not a defect" reading and the two many-to-one codes below in order to say honestly what a class does and does not identify.

**Two traps.**

`gateForm` is many-to-one over a dozen distinct structural checks, and `targetIteration` is many-to-one over two: a semantic index on the target reference and an iteration depth that disagrees with the gate's produce the same code. A consumer cannot recover the cause from the code, and a repair tool that guesses one will be wrong on the other.

The target-type rule is not "a string field is fine". A *plain* String is admitted only with no declared maximum length, no declared minimum length, no pattern, and value validation on; a Number only with no bounds, no fractional digits either way, and leading zeros off; an Enumeration always. An **extensible-enum String is refused**, which is the trap, because the Kernel's own field-utility treats plain String, Enumeration, and extensible enum as three disjoint classes and only the first two have a branch here.

**Evidence.** Eleven of the twelve classes are measured against the real Kernel through the `dynamicEnumerations` probe route, each isolated to a single witness rule so the attribution is the rule and not the model, alongside an accepted control whose values the derivation actually extracted ([checkpoint](../../docs/SOURCES.md#src-dynamic-enumeration-legality)). The twelfth, `hModel`, guards a branch reached only by a non-A12 model; no witness is known through this route, and the clause below states its arm unconditionally regardless, because a reimplementer needs the total function either way.

This vocabulary carries **no** rendered message text, by the licensing boundary in [`CLAUDE.md`](../../CLAUDE.md).
-/

namespace A12Kernel

/-- Which of the derivation's four ordered stages owns a refusal. The stage is what a consumer needs
to know *when* a class can arrive: a stage-1 class says nothing about the condition, because the
condition was not read yet. -/
inductive DynEnumStage where
  /-- The model's world and the target field's declaration, before the condition is parsed. -/
  | ruleParameters
  /-- Whole-condition constructs rejected before any structural reading. -/
  | conditionGlobal
  /-- The gate and safe-guard shape. -/
  | canonicalForm
  /-- The individual value calculations and the target references inside them. -/
  | valueCalculation
  deriving Repr, DecidableEq

namespace DynEnumStage

/-- Position in the run order, so a consumer can ask which of two stages decides first. -/
def order : DynEnumStage → Nat
  | .ruleParameters => 0
  | .conditionGlobal => 1
  | .canonicalForm => 2
  | .valueCalculation => 3

end DynEnumStage

/-- A reason a rule is not a well-formed dynamic enumeration. Constructor names are local; `catalogKey` carries the exact identity a consumer compares against. -/
inductive DynEnumRefusal where
  /-- The model is not an A12 model. -/
  | hModel
  /-- The target field's declared type is outside the admissible set — see `targetTypeAdmits`. -/
  | targetType
  /-- The target is its own group's index field, whose values the repetition key already owns. -/
  | targetIsIndexField
  /-- The condition iterates two repeatable groups neither of which contains the other. -/
  | parallelIteration
  /-- The condition uses `RepetitionNotUnique`. -/
  | repetitionNotUnique
  /-- The condition does not have the canonical gate shape. Many-to-one over a dozen structural
  checks, so it identifies no particular defect. -/
  | gateForm
  /-- A value calculation compares a field other than the gate's target. -/
  | wrongTargetField
  /-- The target reference reaches through an enumeration category. -/
  | targetCategoryAccess
  /-- The target reference carries a semantic index, or an iteration depth disagreeing with the
  gate's. Many-to-one over those two. -/
  | targetIteration
  /-- A value calculation is not a comparison of the target against a calculation function. -/
  | calcOpForm
  /-- The comparison uses an operator other than the two the canonical form allows. -/
  | calcOpComparison
  /-- A precondition or calculation function reads an operand the safe guard does not check. -/
  | unguardedOperand
  deriving Repr, DecidableEq

namespace DynEnumRefusal

/-- The catalog key, which is also the code the probe route surfaces. -/
def catalogKey : DynEnumRefusal → String
  | .hModel => "MVK_DYNENUM_OLD_WORLD"
  | .targetType => "MVK_DYNENUM_INVALID_TYPE"
  | .targetIsIndexField => "MVK_DYNENUM_INDEX_FIELD"
  | .parallelIteration => "MVK_DYNENUM_PARALLEL_ITERATION"
  | .repetitionNotUnique => "MVK_DYNENUM_REPETITION_NOT_UNIQUE"
  | .gateForm => "MVK_DYNENUM_INVALID_GATE"
  | .wrongTargetField => "MVK_ERROR_WRONG_DYNENUM_FIELD"
  | .targetCategoryAccess => "MVK_ERROR_DYNENUM_FIELD_WITH_CATEGORY"
  | .targetIteration => "MVK_INVALID_ITERATION"
  | .calcOpForm => "MVK_DYNENUM_INVALID_CALCOP"
  | .calcOpComparison => "MVK_DYNENUM_INVALID_CALCOP_OP"
  | .unguardedOperand => "MVK_DYNENUM_INVALID_FIELD_REFERENCE"

/-- The stage that owns this refusal. -/
def stage : DynEnumRefusal → DynEnumStage
  | .hModel | .targetType | .targetIsIndexField => .ruleParameters
  | .parallelIteration | .repetitionNotUnique => .conditionGlobal
  | .gateForm => .canonicalForm
  | .wrongTargetField | .targetCategoryAccess | .targetIteration
  | .calcOpForm | .calcOpComparison | .unguardedOperand => .valueCalculation

/-- Every class, in the order the derivation can first report them. -/
def all : List DynEnumRefusal :=
  [.hModel, .targetType, .targetIsIndexField,
   .parallelIteration, .repetitionNotUnique,
   .gateForm,
   .wrongTargetField, .targetCategoryAccess, .targetIteration,
   .calcOpForm, .calcOpComparison, .unguardedOperand]

end DynEnumRefusal

/-- The six classes the value-calculation stage can report, as their own type.

The stage partition is a real property and not a labelling convenience: a candidate whose
value-calculation stage claimed `targetType` would be ill-formed rather than merely unusual, and
keeping the earlier stages' classes out of that slot is what lets a consumer conclude, from a
value-calculation class alone, that every earlier stage passed. -/
inductive DynEnumValueCalcRefusal where
  | wrongTargetField
  | targetCategoryAccess
  | targetIteration
  | calcOpForm
  | calcOpComparison
  | unguardedOperand
  deriving Repr, DecidableEq

namespace DynEnumValueCalcRefusal

/-- The injection into the full vocabulary. -/
def toRefusal : DynEnumValueCalcRefusal → DynEnumRefusal
  | .wrongTargetField => .wrongTargetField
  | .targetCategoryAccess => .targetCategoryAccess
  | .targetIteration => .targetIteration
  | .calcOpForm => .calcOpForm
  | .calcOpComparison => .calcOpComparison
  | .unguardedOperand => .unguardedOperand

/-- Every class this stage can report. -/
def all : List DynEnumValueCalcRefusal :=
  [.wrongTargetField, .targetCategoryAccess, .targetIteration,
   .calcOpForm, .calcOpComparison, .unguardedOperand]

end DynEnumValueCalcRefusal

/-- A plain String declaration's constraints, as the derivation reads them. Lengths are the Kernel's
own signed encoding: an absent maximum is `0` and an absent minimum is `-1`, and the two are tested
differently, so a declared minimum of `0` refuses where a declared maximum of `0` does not. -/
structure DynEnumStringTarget where
  /-- An extensible enum is a String declaration carrying a value list. It has no branch in the
  type check and therefore falls through to the refusal. -/
  extensibleEnum : Bool := false
  maxLength : Int := 0
  minLength : Int := -1
  /-- The empty pattern is the absent pattern: the check is emptiness, not nullity. -/
  pattern : String := ""
  noValueValidation : Bool := false
  deriving Repr, DecidableEq

/-- A Number declaration's constraints. -/
structure DynEnumNumberTarget where
  leadingZerosAllowed : Bool := false
  maxFractionalDigits : Int := 0
  minFractionalDigits : Int := 0
  /-- Whether a maximum is declared at all; its value never matters here. -/
  hasMaxValue : Bool := false
  hasMinValue : Bool := false
  deriving Repr, DecidableEq

/-- What the rule's error entity is. A rule whose error entity is a group, or a field of any kind
the three branches do not name, is refused by the same class as a badly constrained String. -/
inductive DynEnumTarget where
  | group
  | string (shape : DynEnumStringTarget)
  | enumeration
  | number (shape : DynEnumNumberTarget)
  | otherKind
  deriving Repr, DecidableEq

/-- Whether the target's declared type admits a dynamic enumeration.

The Enumeration arm is unconditional and the other two are conjunctions of "nothing declared". A
reimplementer's likely error is admitting a String with a declared `maxLength`, since a length bound
looks unrelated to a value list; the Kernel refuses it, because a value list plus a length bound
would be two constraints on the same field with no defined interaction. -/
def targetTypeAdmits : DynEnumTarget → Bool
  | .group => false
  | .string s =>
      !s.extensibleEnum && s.maxLength ≤ 0 && s.minLength == -1
        && s.pattern.isEmpty && !s.noValueValidation
  | .enumeration => true
  | .number n =>
      !n.leadingZerosAllowed && n.maxFractionalDigits ≤ 0 && n.minFractionalDigits ≤ 0
        && !n.hasMaxValue && !n.hasMinValue
  | .otherKind => false

/-- How one value calculation's target reference relates to the gate's. Its own cascade is ordered,
and its last two arms share one code. -/
structure DynEnumTargetReference where
  /-- Whether the compared field is the gate's target, by full name. -/
  matchesGateField : Bool := true
  hasCategoryAccess : Bool := false
  hasSemanticIndex : Bool := false
  /-- Whether the reference's repetition indices agree with the gate's, level for level. -/
  indicesMatchGate : Bool := true
  deriving Repr, DecidableEq

/-- The target reference's own ordered cascade. The last two arms collapse onto `targetIteration`,
which is the many-to-one a repair tool must not try to invert. -/
def targetReferenceRefusal (r : DynEnumTargetReference) : Option DynEnumValueCalcRefusal :=
  if !r.matchesGateField then some .wrongTargetField
  else if r.hasCategoryAccess then some .targetCategoryAccess
  else if r.hasSemanticIndex then some .targetIteration
  else if !r.indicesMatchGate then some .targetIteration
  else none

/-- One rule, reduced to the findings the four stages test. The condition-shaped fields are
caller-supplied classifications rather than a parse tree: this clause owns the *order* the stages
run in and the vocabulary they draw from, and deliberately does not re-derive the canonical-form
parser. -/
structure DynEnumCandidate where
  /-- Whether the surrounding model is a non-A12 model. -/
  hModel : Bool := false
  target : DynEnumTarget
  targetIsIndexField : Bool := false
  usesParallelIteration : Bool := false
  usesRepetitionNotUnique : Bool := false
  gateCanonical : Bool := true
  /-- The first refusal the value-calculation stage produced, if any — typically from
  `targetReferenceRefusal`. -/
  valueCalculation : Option DynEnumValueCalcRefusal := none

/-- Whether this rule is a dynamic enumeration, and if not, the single class the derivation reports.
`none` is the accepted case: only then does the rule contribute values.

First-match-wins across the four stages, so an earlier defect completely hides every later one — a
rule with both an inadmissible target type and a broken gate reports the type. -/
def dynEnumLegality (c : DynEnumCandidate) : Option DynEnumRefusal :=
  if c.hModel then some .hModel
  else if !targetTypeAdmits c.target then some .targetType
  else if c.targetIsIndexField then some .targetIsIndexField
  else if c.usesParallelIteration then some .parallelIteration
  else if c.usesRepetitionNotUnique then some .repetitionNotUnique
  else if !c.gateCanonical then some .gateForm
  else c.valueCalculation.map (·.toRefusal)

/-- Every stage condition this candidate violates, in stage order. Written independently of
`dynEnumLegality` so that the pipeline's first-match-wins behaviour is a theorem relating two
definitions rather than a restatement of one. -/
def dynEnumViolations (c : DynEnumCandidate) : List DynEnumRefusal :=
  (if c.hModel then [DynEnumRefusal.hModel] else [])
    ++ (if targetTypeAdmits c.target then [] else [DynEnumRefusal.targetType])
    ++ (if c.targetIsIndexField then [DynEnumRefusal.targetIsIndexField] else [])
    ++ (if c.usesParallelIteration then [DynEnumRefusal.parallelIteration] else [])
    ++ (if c.usesRepetitionNotUnique then [DynEnumRefusal.repetitionNotUnique] else [])
    ++ (if c.gateCanonical then [] else [DynEnumRefusal.gateForm])
    ++ (c.valueCalculation.map (·.toRefusal)).toList

end A12Kernel
