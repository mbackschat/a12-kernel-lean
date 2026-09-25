/-! # A computation's normalized condition is generated, and the generator satisfies its own checker

The Kernel checks a calculation rule by parsing one **normalized condition**: a gate naming the computed field, then an optional common precondition, then one comparison per alternative between that field and the alternative's operation, joined by `And` inside and `Or` across. Twelve catalog classes report the ways that condition can be wrong.

**An A12 document model never writes that condition.** It declares a computation *structurally* — a computed field, an optional common precondition, a rounding mode, and a list of alternatives each carrying an operation, an optional precondition, and an optional tolerance range — and the model layer joins those into the normalized condition itself. The gate template, the conjunction and disjunction, the parenthesisation, and the comparison operator are all emitted by the joiner from the structure.

So the shape half of the checker tests properties the generator guarantees, and this module states that as a theorem rather than as a remark: **every condition the joiner emits passes the shape checks.** A reimplementer who accepts a structured computation and produces its own condition needs exactly this property, and it is the reason those classes never reach an A12 consumer while remaining live for a model that authors its condition directly.

**What the generator does *not* settle** is as important, and splits four ways.

*Content, not shape.* The enumeration-compatibility arm reads the operation's own text against the computed field's declared value set, which the joiner copies through untouched. It is live.

*A different, earlier gate.* The invalid-field-name arm fires on a computed field whose name contains a dot or a colon. No A12 model reaches it, because the model layer refuses such a name when the field is declared — an earlier refusal with its own class, measured rather than inferred.

*Model kind.* The unchecked-iteration arm is guarded by an H-model test, with the Kernel's own comment recording why: for an A12 model the iteration-check precondition is supplied implicitly.

*A declared member beside the structure.* **The rounding-mode arm is live, and it judges a pair.** A computation declares its rounding mode once — `Exact`, which an absent mode means, `RoundUp` or `RoundDown` — while each alternative declares its own tolerance range. The check fires when an alternative's emitted comparison is `!=`, which is exactly when that alternative declares no range, while the mode is anything but exact. So the class is owed per alternative: one alternative without a range refuses a rounding computation whatever the others declare, and the same mode against ranges only is admitted. Deriving the mode from the range instead makes the two conditions complementary and the class unreachable, which is the tempting wrong account ([inbound](../../docs/SOURCES.md#inbound-2026-09-25c-calculation-stages)).

**Evidence.** The admissions are measured: eighteen structured computations, including an `Or` common precondition, an `Or` alternative precondition, a tolerance range, a repeatable-row target, a starred aggregate operation, and a starred gate, are all accepted ([checkpoint](../../docs/SOURCES.md#src-computation-normal-form-generation)). The dotted and colon'd field names are measured refused at declaration. The remaining unreachability statements are mechanism claims resting on the joiner being the sole generator, discharged by reading it, and are marked as such in the coverage record.

This module carries no rendered message text, by the licensing boundary in [`CLAUDE.md`](../../CLAUDE.md).
-/

namespace A12Kernel

/-- A class the calculation-rule check can report. -/
inductive CalculationRefusal where
  /-- The rule's severity is not `ERROR`. -/
  | calcInvalidActionType
  /-- The declared computed field is not the rule's error entity. -/
  | wrongCalculatedField
  /-- The computed field's name carries a dot or a colon. -/
  | invalidFieldName
  /-- The rule carries an iteration restriction. -/
  | restrictedCalculationRule
  /-- The condition is not a conjunction gated on the computed field. -/
  | invalidFieldGate
  /-- The condition uses a construct calculations exclude. -/
  | invalidLanguageFeature
  /-- An alternative's own conjunction is a disjunction instead. -/
  | comparisonWithOr
  /-- An alternative is not a comparison of the computed field against an operation. -/
  | invalidComparison
  /-- The comparison is `!=` while the rounding mode is not exact. -/
  | wrongRoundingMode
  /-- The operation cannot produce a value the computed enumeration admits. -/
  | invalidEnumCalculation
  /-- An iterating alternative has no iteration-check precondition. -/
  | iterationUnchecked
  /-- The computations form a dependency cycle. -/
  | calcCycle
  deriving Repr, DecidableEq

namespace CalculationRefusal

/-- The exact catalog key. -/
def catalogKey : CalculationRefusal → String
  | .calcInvalidActionType => "MVK_CALC_INVALID_ACTION_TYPE"
  | .wrongCalculatedField => "MVK_ERROR_WRONG_CALCULATED_FIELD"
  | .invalidFieldName => "MVK_ERROR_INVALID_FIELDNAME"
  | .restrictedCalculationRule => "MVK_ERROR_RESTRICTED_CALCULATION_RULE"
  | .invalidFieldGate => "MVK_ERROR_INVALID_FIELD_GATE"
  | .invalidLanguageFeature => "MVK_ERROR_INVALID_LANGUAGE_FEATURE"
  | .comparisonWithOr => "MVK_ERROR_COMPARISON_WITH_OR"
  | .invalidComparison => "MVK_ERROR_INVALID_COMPARISON"
  | .wrongRoundingMode => "MVK_ERROR_WRONG_ROUNDING_MODE"
  | .invalidEnumCalculation => "MVK_ERROR_INVALID_ENUM_CALCULATION"
  | .iterationUnchecked => "MVK_ERROR_ITERATION_UNCHECKED"
  | .calcCycle => "MVK_ERROR_CALC_CYCLE"

/-- Every class of the family. -/
def all : List CalculationRefusal :=
  [.calcInvalidActionType, .wrongCalculatedField, .invalidFieldName, .restrictedCalculationRule,
   .invalidFieldGate, .invalidLanguageFeature, .comparisonWithOr, .invalidComparison,
   .wrongRoundingMode, .invalidEnumCalculation, .iterationUnchecked, .calcCycle]

end CalculationRefusal

/-- The tolerance ranges an alternative may declare. Declaring one changes the emitted comparison,
which is what the rounding-mode check reads beside the computation's declared mode. -/
inductive ToleranceRange where
  | one | two | five | ten
  deriving Repr, DecidableEq

/-- The comparison operator the joiner emits. -/
inductive ComparisonSpelling where
  /-- `!=`, emitted when the alternative declares no tolerance range. -/
  | notEqual
  /-- The tolerance-range operator for the declared range. -/
  | differsWithTolerance (range : ToleranceRange)
  deriving Repr, DecidableEq

/-- The rounding mode a computation declares, once for all its alternatives. An absent mode is
`exact`. -/
inductive ComputationRoundingMode where
  | exact | roundUp | roundDown
  deriving Repr, DecidableEq

/-- One declared alternative of a structured computation.

Distinct from [`ComputationCondition.lean`](../Semantics/ComputationCondition.lean)'s
`ComputationAlternative`, which is the evaluation-time alternative carrying a checked precondition
and a typed operation. This one is the authoring-time declaration: its precondition and operation are
condition *text* the joiner copies through without reading, and the two meet only after parsing. -/
structure DeclaredComputationAlternative where
  /-- Opaque to this clause: the joiner copies it through and the shape checks do not read it. -/
  precondition : Option String := none
  operation : String
  toleranceRange : Option ToleranceRange := none
  deriving Repr, DecidableEq

/-- A computation as an A12 document model declares it — structurally, never as a condition. -/
structure StructuredComputation where
  computedField : String
  commonPrecondition : Option String := none
  roundingMode : ComputationRoundingMode := .exact
  alternatives : List DeclaredComputationAlternative
  deriving Repr, DecidableEq

/-- One branch of the normalized condition: an alternative's optional precondition together with
its comparison. Modelled as a record rather than as a general tree because the joiner emits exactly
this shape, and a tree deep enough to express anything else would be expressing nothing the Kernel
can receive from an A12 model. -/
structure NormalizedBranch where
  precondition : Option String := none
  field : String
  spelling : ComparisonSpelling
  operation : String
  deriving Repr, DecidableEq

/-- A member of the top-level conjunction after the gate. -/
inductive NormalizedMember where
  /-- The common precondition, opaque to the shape checks. -/
  | precondition (text : String)
  /-- The sole alternative's branch. -/
  | branch (only : NormalizedBranch)
  /-- Several alternatives, joined by `Or`. -/
  | alternation (branches : List NormalizedBranch)
  /-- A second gate where a member belongs — expressible so the checker has something to reject,
  and never emitted. -/
  | strayGate (field : String)
  deriving Repr, DecidableEq

/-- The normalized condition, as structure rather than as text: reproducing the Kernel's emitted
sentence would serve nothing this clause needs, and every check reads shape. An absent gate field
is a condition that is not a gated conjunction at all. -/
structure NormalizedCondition where
  gateField : Option String
  members : List NormalizedMember
  deriving Repr, DecidableEq

/-- The comparison the joiner emits for one alternative: `!=` unless a tolerance range is declared. -/
def emittedSpelling (alternative : DeclaredComputationAlternative) : ComparisonSpelling :=
  match alternative.toleranceRange with
  | none => .notEqual
  | some range => .differsWithTolerance range

/-- One alternative as the joiner emits it. -/
def emitBranch (computedField : String) (alternative : DeclaredComputationAlternative) : NormalizedBranch :=
  { precondition := alternative.precondition, field := computedField,
    spelling := emittedSpelling alternative, operation := alternative.operation }

/-- The joiner: a gate on the computed field, the optional common precondition, then the sole
alternative directly or an alternation of several. An empty alternative list emits nothing at all,
which is the one input for which there is no condition to check. -/
def joinAlternatives (computation : StructuredComputation) : Option NormalizedCondition :=
  let preconditionMembers :=
    (computation.commonPrecondition.map NormalizedMember.precondition).toList
  match computation.alternatives with
  | [] => none
  | [sole] =>
      some { gateField := some computation.computedField,
             members := preconditionMembers ++
               [.branch (emitBranch computation.computedField sole)] }
  | alternatives =>
      some { gateField := some computation.computedField,
             members := preconditionMembers ++
               [.alternation (alternatives.map (emitBranch computation.computedField))] }

/-- A branch is well shaped when it compares the computed field itself. -/
def branchRefusal (computedField : String) (branch : NormalizedBranch) :
    Option CalculationRefusal :=
  if branch.field != computedField then some .invalidComparison else none

/-- A member is well shaped when it is a precondition, or a branch or alternation of branches on the
computed field. A second gate is the shape the checker exists to reject. -/
def memberRefusal (computedField : String) : NormalizedMember → Option CalculationRefusal
  | .precondition _ => none
  | .branch only => branchRefusal computedField only
  | .alternation branches => branches.findSome? (branchRefusal computedField)
  | .strayGate _ => some .invalidComparison

/-- The shape half of the calculation checker: a gated conjunction on the computed field whose
remaining members are well shaped. -/
def normalizedFormRefusal (computedField : String) (condition : NormalizedCondition) :
    Option CalculationRefusal :=
  match condition.gateField with
  | none => some .invalidFieldGate
  | some field =>
      if field != computedField then some .invalidFieldGate
      else condition.members.findSome? (memberRefusal computedField)

/-- The rounding-mode check on one alternative: `!=` beside anything but exact rounding.

`RoundUp` beside `!=` and the modes measured beside a range are measured cells. `RoundDown` beside
`!=` is refused here on the peer's reading of the gate, which asks only whether the mode is exact;
no row measures it. -/
def roundingRefusal (spelling : ComparisonSpelling) (mode : ComputationRoundingMode) :
    Option CalculationRefusal :=
  match spelling, mode with
  | .notEqual, .exact => none
  | .notEqual, .roundUp | .notEqual, .roundDown => some .wrongRoundingMode
  | .differsWithTolerance _, _ => none

/-- The rounding-mode check on a computation: its one declared mode against every alternative's
emitted comparison, so a single alternative without a tolerance range is enough. -/
def roundingModeRefusal (computation : StructuredComputation) : Option CalculationRefusal :=
  computation.alternatives.findSome? fun alternative =>
    roundingRefusal (emittedSpelling alternative) computation.roundingMode

end A12Kernel
