import A12Kernel.Elaboration.DateRangeStoredComparison
import A12Kernel.Elaboration.AtLeastOneDateRangeOverlap
import A12Kernel.Elaboration.DateRangeBoundComparison
import A12Kernel.Elaboration.YearlessDateRangeOverlap
import A12Kernel.Elaboration.DateRangeConstructionComparison

/-! # DateRange conditions read at a rule's iterating row

The DateRange condition carriers differ in what they compare — two stored ranges, one endpoint
against a fixed date, two endpoints, an overlap scan — but they read their operands the same way: at
one reading scope, at the row the enclosing rule is currently evaluating. This module owns that
common shape so the checked condition tree carries one leaf family rather than one per carrier, and
so a new carrier lands as a member here instead of as another set of dispatch arms.

The reading scope is the enclosing rule's own iteration scope. Admission is therefore the measured
locus rule stated positively: an operand is accepted exactly when that scope binds every repeatable
level the operand crosses. Each member's own comparison, component, and emptiness behaviour stays
with its carrier, so this module decides nothing about meaning beyond who reads which cell.
-/

namespace A12Kernel

/-- Project a DateRange read failure into the shared addressing channel a condition leaf carries.
The two payload classes name a stored value that contradicts its own certificate, which no checked
source can produce; they are reported at the offending address rather than dropped, so a leaf and a
standalone consumer give one account of one certificate. The bridge lives here rather than with the
read, because the addressing channel belongs to the condition tree. -/
def DirectDateRangeFault.toAddressing (address : CellAddr) :
    DirectDateRangeFault → CheckedAddressingError
  | .document error => CheckedAddressingError.document error
  | .environment error => CheckedAddressingError.environment error
  | .sourceValueKind _ | .sourceValueProfile _ _ =>
      CheckedAddressingError.operandPayload address

/-- One constructed range compared with one stored range, both read at the enclosing rule's current
row. The two halves keep their own certificates: the construction is the scalar carrier's, whose
endpoints are already scope-aware, and the stored operand is the iterated DateRange source. Only the
cross-operand component invariant is stated here.

The stored half is why this pairing exists rather than reusing the scalar mixed carrier: that
carrier's stored field is the nonrepeatable certificate, and the two DateRange source certificates
are still parallel types rather than one indexed family. -/
structure CheckedIteratedConstructionStoredComparison (model : FlatModel) where
  private mk ::
  construction : CheckedDateRangeConstruction model
  stored : CheckedDateRangeSource model
  position : DateRangeConstructionPosition
  comparison : EqualityOp
  componentsMatch :
    construction.start.format.matchesStoredInput stored.format = true

namespace CheckedIteratedConstructionStoredComparison

/-- Compare one constructed and one stored observation at the authored positions. The comparison is
the scalar mixed carrier's own seam, so the two carriers cannot disagree about identity, emptiness,
or formal unavailability. -/
def verdictOf (checked : CheckedIteratedConstructionStoredComparison model)
    (construction : DateRangeConstructionObservation)
    (stored : CellObservation DateRangeCellValue) : Verdict :=
  match checked.position with
  | .left => checked.comparison.evalDateRangeCellValues
      construction.comparisonOperand stored.asValidationSimpleOperand
  | .right => checked.comparison.evalDateRangeCellValues
      stored.asValidationSimpleOperand construction.comparisonOperand

end CheckedIteratedConstructionStoredComparison

/-- One DateRange condition whose operands are read at the enclosing rule's current row. -/
inductive IteratedDateRangeCondition (model : FlatModel) where
  | storedEquality (comparison : CheckedDateRangeSourceComparison model)
  | boundAgainstFixed (operand : CheckedDateRangeSourceBound model)
      (position : DateRangeBoundComparisonPosition)
      (comparison : TemporalComparisonOp) (expected : FullDate)
  | boundPair (left right : CheckedDateRangeSourceBound model)
      (comparison : TemporalComparisonOp)
  | boundPairYearless (left right : CheckedYearlessDateRangeBound model)
      (comparison : TemporalComparisonOp)
  | overlap (source : CheckedDateRangesOverlapSource model)
  | pluralOverlap (source : CheckedAtLeastOneDateRangeOverlapsSource model)
  | yearlessOverlap (source : CheckedYearlessDateRangesOverlapSource model)
  | yearlessPluralOverlap
      (source : CheckedYearlessAtLeastOneDateRangeOverlapsSource model)
  | constructionAgainstStored
      (comparison : CheckedIteratedConstructionStoredComparison model)

/-- Static refusal while resolving one iterated DateRange condition. -/
inductive IteratedDateRangeConditionElabError where
  | storedEquality (cause : DirectDateRangeComparisonElabError)
  | operand (cause : DirectDateRangeElabError)
  | yearlessOperand (cause : YearlessDateRangeBoundElabError)
  | formatsNotComparable (left right : TemporalComponents)
  | mixedBoundDomains
  | overlap (cause : DateRangesOverlapElabError)
  | pluralOverlap (cause : AtLeastOneDateRangeOverlapsElabError)
  | yearlessOverlap (cause : YearlessDateRangesOverlapElabError)
  | construction (cause : DateRangeConstructionElabError)
  | storedOperand (cause : DirectDateRangeElabError)
  | constructionComponentMismatch (construction : DateRangeEndpointFormat)
      (stored : DateRangeInputFormat)
  deriving Repr, DecidableEq

namespace IteratedDateRangeConditionElabError

/-- Project each member's own established diagnostic. The operand classes are the shared DateRange
source owner's, so a repeatable operand crossing an unbound level reports the Kernel's
missing-wildcard class here exactly as it does on the scalar carriers. -/
def diagnostic? :
    IteratedDateRangeConditionElabError → Option KernelStaticDiagnostic
  | .storedEquality cause => cause.diagnostic?
  | .operand cause => cause.diagnostic?
  | .yearlessOperand cause => cause.diagnostic?
  | .formatsNotComparable _ _ => some .invalidCompareToDate
  | .mixedBoundDomains => none
  | .overlap cause => cause.diagnostic?
  | .pluralOverlap cause => cause.diagnostic?
  | .yearlessOverlap cause => cause.diagnostic?
  | .construction cause => cause.diagnostic?
  | .storedOperand cause => cause.diagnostic?
  | .constructionComponentMismatch _ _ => some .invalidCompareToDateRange

end IteratedDateRangeConditionElabError

namespace IteratedDateRangeCondition

/-- Every operand declaration this condition reads, in authored order. -/
def operandDeclarations : IteratedDateRangeCondition model → List FlatFieldDecl
  | .storedEquality comparison =>
      [comparison.left.declaration, comparison.right.declaration]
  | .boundAgainstFixed operand _ _ _ => [operand.declaration]
  | .boundPair left right _ | .boundPairYearless left right _ =>
      [left.declaration, right.declaration]
  | .overlap source =>
      -- Only the unstarred operands are read at the enclosing row. A starred operand reopens its
      -- own levels, so it is neither bound by the reading scope nor a contributor to it.
      source.shape.operands.filterMap fun operand =>
        match operand with
        | .field declaration _ => some declaration
        | _ => none
  | .pluralOverlap source =>
      -- The distinguished scalar is always read at the row; among the list operands only the
      -- unstarred ones are, for the same reason a star contributes nothing above.
      source.shape.operands.filterMap fun operand =>
        match operand with
        | .field declaration _ => some declaration
        | _ => none
  | .yearlessOverlap source | .yearlessPluralOverlap source =>
      source.shape.operands.filterMap fun operand =>
        match operand with
        | .field declaration _ => some declaration
        | _ => none
  | .constructionAgainstStored comparison =>
      [comparison.construction.start.checked.declaration,
        comparison.construction.finish.checked.declaration,
        comparison.stored.declaration]

/-- The operands that actually cross a repeatable level. These are the declarations the enclosing
rule resolves before evaluation and the levels it derives its iteration from. -/
def repeatableDeclarations (condition : IteratedDateRangeCondition model) :
    List FlatFieldDecl :=
  condition.operandDeclarations.filter fun declaration =>
    !declaration.repeatableScope.isEmpty

/-- Whether every retained declaration is still the model's own and still bound by the reading
group's scope. The checked condition re-establishes this at assembly, so a leaf cannot smuggle a
stale declaration or an unbound level past the locus gate.

A condition with no repeatable operand is admitted, because this leaf is the family's only
rule-level owner: refusing the scalar shape would leave it unreachable from any rule rather than
handing it to a second owner. -/
def wellFormedIn (condition : IteratedDateRangeCondition model)
    (scope : List RepeatableLevel) : Bool :=
  condition.operandDeclarations.all fun declaration =>
      declaration.repetitionBoundBy scope &&
        match model.lookupUniqueId declaration.id with
        | .ok owned => owned == declaration
        | .error _ => false

/-- Produce this condition's verdict at the consuming row. Each member reads its own operands
through the row the enclosing rule is evaluating and reuses its carrier's comparison or scan
unchanged; a read failure projects into the leaf's addressing channel rather than being dropped. -/
def verdictOf (condition : IteratedDateRangeCondition model)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError Verdict :=
  let address (declaration : FlatFieldDecl) : CellAddr :=
    { field := declaration.id, path := [] }
  match condition with
  | .storedEquality comparison => do
      let left ←
        (comparison.left.evaluateAt outer .validation document).mapError
          (DirectDateRangeFault.toAddressing (address comparison.left.declaration))
      let right ←
        (comparison.right.evaluateAt outer .validation document).mapError
          (DirectDateRangeFault.toAddressing
            (address comparison.right.declaration))
      pure (comparison.verdictOf left right)
  | .boundAgainstFixed operand position comparison expected => do
      let selected ←
        (operand.evaluateAt outer .validation document).mapError
          (DirectDateRangeFault.toAddressing (address operand.declaration))
      match CheckedDateRangeBoundPair.exactObservation
          operand.declaration.id selected with
      | Except.ok projected =>
          pure (position.evalAgainstFixed comparison expected projected)
      | Except.error _ =>
          Except.error (.operandPayload (address operand.declaration))
  | .boundPair left right comparison => do
      let leftSelected ←
        (left.evaluateAt outer .validation document).mapError
          (DirectDateRangeFault.toAddressing (address left.declaration))
      let rightSelected ←
        (right.evaluateAt outer .validation document).mapError
          (DirectDateRangeFault.toAddressing (address right.declaration))
      match CheckedDateRangeBoundPair.exactObservation
          left.declaration.id leftSelected,
          CheckedDateRangeBoundPair.exactObservation
            right.declaration.id rightSelected with
      | Except.ok leftDate, Except.ok rightDate =>
          pure (comparison.evalObserved leftDate rightDate)
      | _, _ => Except.error (.operandPayload (address left.declaration))
  | .boundPairYearless left right comparison => do
      let leftSelected ←
        (left.evaluateAt outer .validation document).mapError fun
          | .source cause =>
              DirectDateRangeFault.toAddressing (address left.declaration) cause
          | .sourceValueProfile _ _ =>
              CheckedAddressingError.operandPayload (address left.declaration)
      let rightSelected ←
        (right.evaluateAt outer .validation document).mapError fun
          | .source cause =>
              DirectDateRangeFault.toAddressing (address right.declaration) cause
          | .sourceValueProfile _ _ =>
              CheckedAddressingError.operandPayload (address right.declaration)
      let leftLabel :=
        CheckedDateRangeBoundPair.yearlessObservation left.bound leftSelected
      let rightLabel :=
        CheckedDateRangeBoundPair.yearlessObservation right.bound rightSelected
      pure (evalSymmetricComparison comparison.holdsMonthDay
        leftLabel.asValidationSimpleOperand
        rightLabel.asValidationSimpleOperand)
  | .overlap source => do
      let result ← (source.evaluateCheckedDocument document outer).mapError
        (DateRangesOverlapEvaluationError.toAddressing
          { field := source.first.declaration.id, path := [] })
      pure result.verdict
  | .pluralOverlap source => do
      let result ← (source.evaluateCheckedDocument document outer).mapError
        (DateRangesOverlapEvaluationError.toAddressing
          { field := source.scalar.declaration.id, path := [] })
      pure result.verdict
  | .yearlessOverlap source =>
      -- The fallback address is only reached by the incoherent-extent class, which names no cell;
      -- the first operand's own declaration is the nearest honest coordinate for it.
      (evaluateYearlessDateRangeOverlapOperands source.operands document
        outer).mapError
        (YearlessDateRangesOverlapEvaluationError.toAddressing
          { field := (source.first.source?.map (·.declaration.id)).getD 0
            path := [] })
  | .yearlessPluralOverlap source =>
      (evaluateYearlessAtLeastOneDateRangeOverlapsOperands
        (.direct source.scalar) source.operands document outer).mapError
        (YearlessDateRangesOverlapEvaluationError.toAddressing
          { field := source.scalar.declaration.id, path := [] })
  | .constructionAgainstStored comparison => do
      let readAt (declaration : FlatFieldDecl) :
          Except CheckedAddressingError CheckedCell := do
        let path ← (outer.pathForScope declaration.repeatableScope).mapError
          CheckedAddressingError.environment
        (document.read { field := declaration.id, path }).mapError
          CheckedAddressingError.document
      let start ← readAt comparison.construction.start.checked.declaration
      let finish ← readAt comparison.construction.finish.checked.declaration
      let storedObserved ←
        (comparison.stored.evaluateAt outer .validation document).mapError
          (DirectDateRangeFault.toAddressing
            (address comparison.stored.declaration))
      pure (comparison.verdictOf
        (comparison.construction.observeAt start finish) storedObserved)

end IteratedDateRangeCondition

/-- Resolve one stored-versus-stored equality read at the rule's row. -/
def elaborateIteratedStoredEquality (model : FlatModel)
    (scope : List RepeatableLevel) (left right : FieldId)
    (comparison : EqualityOp) :
    Except IteratedDateRangeConditionElabError
      (IteratedDateRangeCondition model) :=
  (.storedEquality <$>
    elaborateDateRangeSourceComparisonIn model scope left right comparison)
    |>.mapError .storedEquality

/-- Resolve one selected endpoint compared against a fixed complete date. -/
def elaborateIteratedBoundAgainstFixed (model : FlatModel)
    (scope : List RepeatableLevel) (source : FieldId) (bound : DateRangeBound)
    (position : DateRangeBoundComparisonPosition)
    (comparison : TemporalComparisonOp) (expected : FullDate) :
    Except IteratedDateRangeConditionElabError
      (IteratedDateRangeCondition model) := do
  let operand ←
    (elaborateDateRangeBoundIn model scope source bound).mapError .operand
  pure (.boundAgainstFixed operand position comparison expected)

/-- One endpoint operand at a reading scope, from whichever bound owner admits its policy. The
preference order is the scalar carrier's: the exact owner first, the yearless owner only where the
exact one reports an unsupported policy, so a genuine source failure is never replaced. -/
private inductive IteratedBoundOperand (model : FlatModel) where
  | exact (bound : CheckedDateRangeSourceBound model)
  | yearless (bound : CheckedYearlessDateRangeBound model)

private def IteratedBoundOperand.components :
    IteratedBoundOperand model → TemporalComponents
  | .exact bound => bound.format.components
  | .yearless bound => bound.format.components

private def elaborateIteratedBoundOperand (model : FlatModel)
    (scope : List RepeatableLevel) (source : FieldId) (bound : DateRangeBound) :
    Except YearlessDateRangeBoundElabError (IteratedBoundOperand model) :=
  match elaborateDateRangeBoundIn model scope source bound with
  | .ok exact => pure (.exact exact)
  | .error (.unsupportedPolicy _ _ _) =>
      IteratedBoundOperand.yearless <$>
        elaborateYearlessDateRangeBoundIn model scope source bound
  | .error cause => throw (.source cause)

/-- Resolve two selected endpoints compared with each other, in either domain. Comparability is the
ordinary temporal rule over the two declarations' component sets, so this carrier adds no gate of
its own; because that gate admits only a homogeneous pair, the mixed case below is unreachable
rather than a second comparison. -/
def elaborateIteratedBoundPair (model : FlatModel)
    (scope : List RepeatableLevel)
    (leftSource : FieldId) (leftBound : DateRangeBound)
    (rightSource : FieldId) (rightBound : DateRangeBound)
    (comparison : TemporalComparisonOp) :
    Except IteratedDateRangeConditionElabError
      (IteratedDateRangeCondition model) := do
  let left ←
    (elaborateIteratedBoundOperand model scope leftSource leftBound).mapError
      .yearlessOperand
  let right ←
    (elaborateIteratedBoundOperand model scope rightSource rightBound).mapError
      .yearlessOperand
  if comparison.admitsFormats model.baseYear.isSome left.components
      right.components then
    match left, right with
    | .exact left, .exact right => pure (.boundPair left right comparison)
    | .yearless left, .yearless right =>
        pure (.boundPairYearless left right comparison)
    | _, _ => throw .mixedBoundDomains
  else
    throw (.formatsNotComparable left.components right.components)


/-- Resolve one constructed range compared with one stored range, all three operands read at the
rule's row. Every gate is the scalar carriers' — endpoint kind and profile, the construction's own
component pair, and the cross-operand component match — and only the operand locus widens. -/
def elaborateIteratedConstructionStoredComparison (model : FlatModel)
    (scope : List RepeatableLevel)
    (start finish stored : FieldId) (position : DateRangeConstructionPosition)
    (comparison : EqualityOp) :
    Except IteratedDateRangeConditionElabError
      (IteratedDateRangeCondition model) := do
  let construction ←
    (elaborateDateRangeConstructionIn model scope start finish).mapError
      .construction
  let storedSource ←
    (elaborateDateRangeSourceIn model scope stored).mapError .storedOperand
  if hComponents :
      construction.start.format.matchesStoredInput storedSource.format then
    pure (.constructionAgainstStored {
      construction
      stored := storedSource
      position
      comparison
      componentsMatch := hComponents })
  else
    throw (.constructionComponentMismatch construction.start.format
      storedSource.format)

/-- Resolve one unconfigured yearless plural overlap predicate. Both sides may hold an operand the
rule's own iteration crosses, and every gate is the yearless owner's. -/
def elaborateIteratedYearlessPluralOverlap (model : FlatModel)
    (declaringGroup : GroupPath) (scope : List RepeatableLevel)
    (authored : SurfaceAtLeastOneDateRangeOverlapsSource) :
    Except IteratedDateRangeConditionElabError
      (IteratedDateRangeCondition model) :=
  (.yearlessPluralOverlap <$>
    elaborateYearlessAtLeastOneDateRangeOverlapsSourceIn model declaringGroup
      scope authored) |>.mapError .yearlessOverlap

/-- Resolve one unconfigured yearless overlap predicate whose unstarred operands the rule's own
iteration may cross. Every gate is the yearless owner's, including its per-operand yearless
certification and the shared shape rules; only the operand locus widens. -/
def elaborateIteratedYearlessOverlap (model : FlatModel)
    (declaringGroup : GroupPath) (scope : List RepeatableLevel)
    (authored : SurfaceFieldEntitySource) :
    Except IteratedDateRangeConditionElabError
      (IteratedDateRangeCondition model) :=
  (.yearlessOverlap <$>
    elaborateYearlessDateRangesOverlapSourceIn model declaringGroup scope
      authored) |>.mapError .yearlessOverlap

/-- Resolve one plural overlap predicate whose unstarred operands the rule's own iteration may
cross, on either side. The distinguished scalar and the list share the reading scope, and every other
gate — the scalar's own shape rule, the cross-side duplicate and overlap checks, the uniform-year
rule, and the measured Number-pair refusal — is the scalar operator's, unchanged. -/
def elaborateIteratedPluralOverlap (model : FlatModel)
    (declaringGroup : GroupPath) (scope : List RepeatableLevel)
    (authored : SurfaceAtLeastOneDateRangeOverlapsSource) :
    Except IteratedDateRangeConditionElabError
      (IteratedDateRangeCondition model) :=
  (.pluralOverlap <$>
    elaborateAtLeastOneDateRangeOverlapsSourceIn model declaringGroup scope
      authored) |>.mapError .pluralOverlap

/-- Resolve one singular overlap predicate whose unstarred operands the rule's own iteration may
cross. Every gate is the scalar operator's, including the group refusal and the uniform-year rule;
only the operand-locus admission widens. A starred operand keeps its own topology, so a list mixing
a starred and an unstarred occurrence of one field is admitted here exactly as the Kernel admits it,
with the star reopening the level the bare operand reads at the current row. -/
def elaborateIteratedOverlap (model : FlatModel) (declaringGroup : GroupPath)
    (scope : List RepeatableLevel) (authored : SurfaceFieldEntitySource) :
    Except IteratedDateRangeConditionElabError
      (IteratedDateRangeCondition model) :=
  (.overlap <$>
    elaborateDateRangesOverlapSourceIn model declaringGroup scope authored)
    |>.mapError .overlap

end A12Kernel
