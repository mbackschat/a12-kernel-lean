import A12Kernel.Elaboration.DateRangeBoundComparison
import A12Kernel.Elaboration.DateRangeBoundComponent
import A12Kernel.Elaboration.DateRangeOverlap
import A12Kernel.Elaboration.DateRangeStoredComparison
import A12Kernel.Elaboration.SemanticIndex

/-! # A keyed DateRange operand

A semantic index selects one row of a group by its declared index field's value, and the selected
cell may be a DateRange. The measured Kernel rule is that the index field's kind and the selected
target's kind are independent, so this capsule adds only the **target side**: the checked source's
selected declaration is a DateRange, and the keyed read is projected into the same retained
exact-or-fragment identity a direct read produces.

The result domain needs no new outcome class. A no-match row and a matched-but-empty cell both read
empty, and a duplicated key and a formally invalid matched cell both read UNKNOWN, which is exactly
the ordinary phase observation the direct route already uses.

All four measured carriers are wired here, and each consumes the projected observation directly, so
none needs a second read path: the **numeric component of a selected endpoint**, **stored equality**
against a direct range, an **endpoint comparison** against a direct endpoint, and the **overlap
predicate** against a direct range.

The endpoint comparison is the one that needs a runtime **domain** decision, because a selected
endpoint is a resolved Date under a profile the model can complete and a bare label otherwise. The
two direct owners' gates are complementary, so the decision is a total two-way read of the retained
profile rather than a preference, and it is taken here from the certificate instead of from which
owner happened to certify the operand.

The overlap carrier is a **pair**, not the operator's list. The measured authoring is one keyed
operand against one direct range, and the list operator additionally admits starred, filtered, and
group slots whose extent is a stream of rows reached by addressing — a keyed slot inside such a list
would have to thread an index preliminary through that shared resolution, which no observation calls
for. This carrier instead reuses the operator's own two declaration gates, its uniform-year rule, its
slot projection, and its pure any-pair scan, so it adds an operand shape rather than a predicate.

Every local refusal stays **unmapped to a Kernel diagnostic**, including the ones reached through the
shared overlap certifier. Those classes' codes are measured for direct operands; for a keyed one they
are not, and the admission measurement establishes that the operand is accepted rather than which
code its rejections carry.
-/

namespace A12Kernel

inductive SemanticIndexDateRangeElabError where
  | source (error : SemanticIndexElabError)
  /-- The row selected by the key is not a DateRange declaration at all. -/
  | selectedTargetNotDateRange (path : List String)
  /-- The selected DateRange's declared profile does not expose the requested component. -/
  | boundPartNotExposed (path : List String) (part : DateNumericPart)
  /-- The direct operand standing beside the keyed one failed its own resolution. -/
  | directSource (cause : DirectDateRangeElabError)
  /-- The keyed and direct operands expose different date-component sets. -/
  | componentMismatch (keyed direct : DateRangeInputFormat)
  /-- The direct endpoint operand standing beside the keyed one failed its own certification. -/
  | directBound (cause : YearlessDateRangeBoundElabError)
  /-- The two endpoints are not comparable under the ordinary direct temporal admission rule. -/
  | boundsNotComparable (keyed direct : TemporalComponents)
  /-- Either overlap operand failed the operator's own declaration gates. -/
  | overlap (cause : DateRangesOverlapElabError)
  /-- The two overlap operands disagree on year presence under this model. -/
  | overlapMixesYearClass (keyed direct : DateRangeInputFormat)
  deriving Repr, DecidableEq

namespace SemanticIndexDateRangeElabError

/-- Only the shared source classes project. The two local ones are unmeasured for this operand
shape, so mapping them would assert a code rather than report one. -/
def diagnostic? : SemanticIndexDateRangeElabError → Option KernelStaticDiagnostic
  | .source error => error.diagnostic?
  | .directSource cause => cause.diagnostic?
  | .directBound cause => cause.diagnostic?
  -- The overlap certifier's own classes carry measured codes for a *direct* operand. Reporting one
  -- here would assert that code for a keyed operand, which no observation covers.
  | .overlap _ => none
  | .selectedTargetNotDateRange _ | .boundPartNotExposed _ _ |
    .componentMismatch _ _ | .boundsNotComparable _ _ |
    .overlapMixesYearClass _ _ => none

end SemanticIndexDateRangeElabError

/-- A semantic-index source whose selected target declaration is a DateRange, retaining that
declaration's own checked profile. The index field's kind stays unconstrained, which is the measured
independence. The profile is admitted **without** a reading-scope gate: the selected row arrives from
the index column, not from the reading environment, which is exactly what distinguishes this carrier
from every addressed one. -/
structure CheckedDateRangeSemanticIndexSource (model : FlatModel)
    extends CheckedSemanticIndexSource model where
  target : FlatDateRangeField
  policy : DateRangeDeclarationPolicy
  format : DateRangeInputFormat
  targetAdmitted :
    model.dateRangeSourceProfile target =
      some (toCheckedSemanticIndexSource.targetDeclaration, policy, format)

/-- The two failure classes a keyed range read can reach. They stay distinct because a lookup that
could not be resolved at all is a different consumer decision from a selected cell of the wrong
kind. -/
inductive SemanticIndexDateRangeError where
  | context (error : SemanticIndexContextError)
  | payload (fault : DirectDateRangeFault)
  deriving Repr, DecidableEq

namespace CheckedDateRangeSemanticIndexSource

/-- Whether this profile's selected endpoints are resolved Dates under the model, rather than bare
yearless labels. The exact and yearless direct owners gate on complementary conditions, so this is a
total decision: `dateRangeSemanticIndex_domain_total` states that complementarity. -/
def exactDomain (checked : CheckedDateRangeSemanticIndexSource model) : Bool :=
  checked.format.supportsDirectBound model.baseYear

/-- Read the keyed row's selected cell and project it into the retained range identity through the
direct route's own payload rule, so the two cannot disagree about emptiness, kind, or formal
unavailability. -/
def observePreliminaryRange
    (checked : CheckedDateRangeSemanticIndexSource model)
    (preliminary : CheckedIndexPreliminary model)
    (keyRaw : RawFlatContext) (phase : Phase) (outer : Env := []) :
    Except SemanticIndexDateRangeError
      (CellObservation DateRangeCellValue) := do
  let observed ← (checked.lookupPreliminaryValue preliminary keyRaw phase outer)
    |>.mapError .context
  CheckedDateRangeSource.projectRange checked.target.id observed
    |>.mapError .payload

end CheckedDateRangeSemanticIndexSource

/-- One numeric Date component of an endpoint selected from a keyed row. -/
structure CheckedSemanticIndexDateRangeBoundPart (model : FlatModel) where
  source : CheckedDateRangeSemanticIndexSource model
  bound : DateRangeBound
  part : DateNumericPart
  componentExposed : part.admittedBy model.hasBaseYear source.format.components = true

/-- Certify a keyed DateRange source: the shared semantic-index certificate plus this target's kind. -/
def elaborateDateRangeSemanticIndexSource (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceSemanticIndex) :
    Except SemanticIndexDateRangeElabError
      (CheckedDateRangeSemanticIndexSource model) := do
  let checked ← elaborateSemanticIndexSource model declaringGroup authored
    |>.mapError .source
  let target : FlatDateRangeField := { id := checked.targetDeclaration.id }
  match hTarget : model.dateRangeSourceProfile target with
  | some (declaration, policy, format) =>
      if hOwned : declaration = checked.targetDeclaration then
        pure {
          toCheckedSemanticIndexSource := checked
          target, policy, format
          targetAdmitted := by rw [hTarget, hOwned] }
      else
        throw (.selectedTargetNotDateRange checked.targetDeclaration.path)
  | none => throw (.selectedTargetNotDateRange checked.targetDeclaration.path)

/-- Certify the component read. The exposure gate is the selected declaration's own component set
supplemented by the model's Base Year, which is the direct component owner's rule reaching this
source unchanged. -/
def checkSemanticIndexDateRangeBoundPart (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceSemanticIndex)
    (bound : DateRangeBound) (part : DateNumericPart) :
    Except SemanticIndexDateRangeElabError
      (CheckedSemanticIndexDateRangeBoundPart model) := do
  let source ← elaborateDateRangeSemanticIndexSource model declaringGroup
    authored
  if hPart : part.admittedBy model.hasBaseYear source.format.components = true then
    pure { source, bound, part, componentExposed := hPart }
  else
    throw (.boundPartNotExposed source.targetDeclaration.path part)

namespace CheckedSemanticIndexDateRangeBoundPart

/-- Resolve the keyed endpoint component into the shared validation Number operand. A lookup that
could not be resolved keeps its own error, while a selected cell whose kind is not a DateRange
collapses to malformed — the same collapse the direct component read performs, because at this point
the static gate has already admitted the declaration. -/
def resolvePreliminaryNumericOperand
    (operation : CheckedSemanticIndexDateRangeBoundPart model)
    (preliminary : CheckedIndexPreliminary model)
    (keyRaw : RawFlatContext) (outer : Env := []) :
    Except SemanticIndexContextError NumericOperand :=
  match operation.source.observePreliminaryRange preliminary keyRaw .validation
      outer with
  | .error (.context error) => .error error
  | .error (.payload _) => .ok (.unknown .malformed)
  | .ok observed =>
      .ok (operation.part.fromDateRangeBoundObservation operation.bound
        observed)

end CheckedSemanticIndexDateRangeBoundPart

/-- Stored equality between a keyed range and a direct one. The keyed operand is authorable on either
side, and the retained order flag is what lets an Explain consumer reproduce the authored shape from
the certificate alone. The gate is the direct carrier's own declaration-level component-set rule, so
lexical spelling does not enter it and the refusal is symmetric in the authored order. -/
structure CheckedSemanticIndexDateRangeEquality (model : FlatModel) where
  keyed : CheckedDateRangeSemanticIndexSource model
  direct : CheckedDateRangeSource model
  keyedFirst : Bool
  comparison : EqualityOp
  componentsMatch : keyed.format.components = direct.format.components

/-- Certify a keyed operand beside a direct one at the reading scope the rule's locus binds. The
direct operand keeps its own resolution class, so an operand crossing an unbound level is reported as
that failure rather than as a comparability failure. -/
def elaborateSemanticIndexDateRangeEquality (model : FlatModel)
    (declaringGroup : GroupPath) (keyedAuthored : SurfaceSemanticIndex)
    (directScope : List RepeatableLevel) (directSource : FieldId)
    (keyedFirst : Bool) (comparison : EqualityOp) :
    Except SemanticIndexDateRangeElabError
      (CheckedSemanticIndexDateRangeEquality model) := do
  let keyed ← elaborateDateRangeSemanticIndexSource model declaringGroup
    keyedAuthored
  let direct ← elaborateDateRangeSourceIn model directScope directSource
    |>.mapError .directSource
  if hComponents : keyed.format.components = direct.format.components then
    pure {
      keyed, direct, keyedFirst, comparison
      componentsMatch := hComponents }
  else
    throw (.componentMismatch keyed.format direct.format)

namespace CheckedSemanticIndexDateRangeEquality

/-- Read both operands once and compare their retained identity through the direct carrier's own
verdict, so the keyed and direct pairings cannot drift on emptiness, unknown, or identity.

The direct operand reads the preliminary's **base** document rather than a separately supplied one,
which keeps the two operands provably on one document state. Index preliminary defaults apply only to
declared index cells, so a DateRange operand's own cell is the same under either view. -/
def evaluate (operation : CheckedSemanticIndexDateRangeEquality model)
    (preliminary : CheckedIndexPreliminary model) (keyRaw : RawFlatContext)
    (environment : Env := []) :
    Except SemanticIndexDateRangeError DirectDateRangeComparisonResult := do
  let keyedObserved ← operation.keyed.observePreliminaryRange preliminary keyRaw
    .validation environment
  let directObserved ←
    operation.direct.evaluateAt environment .validation preliminary.base
      |>.mapError .payload
  let left := if operation.keyedFirst then keyedObserved else directObserved
  let right := if operation.keyedFirst then directObserved else keyedObserved
  pure {
    left
    right
    verdict := operation.comparison.evalDateRangeCellValues
      left.asValidationSimpleOperand right.asValidationSimpleOperand }

end CheckedSemanticIndexDateRangeEquality

/-- One selected keyed endpoint compared with one direct endpoint, in either authored slot. The
static gate is the ordinary direct temporal admission rule over the two declared component sets, so
it reads year presence and date class rather than requiring identical sets. -/
structure CheckedSemanticIndexDateRangeBoundComparison (model : FlatModel) where
  keyed : CheckedDateRangeSemanticIndexSource model
  keyedBound : DateRangeBound
  direct : CheckedDateRangeBoundOperand model
  keyedFirst : Bool
  comparison : TemporalComparisonOp
  formatsAdmitted :
    comparison.admitsFormats model.baseYear.isSome keyed.format.components
      direct.components = true

/-- Defensive failure while reading one side of a keyed endpoint comparison. -/
inductive SemanticIndexDateRangeBoundComparisonFault where
  | keyed (error : SemanticIndexDateRangeError)
  /-- Either side's endpoint projection, reported through the direct pair's own fault vocabulary so
  the two carriers cannot describe one failure two ways. -/
  | endpoint (fault : DateRangeBoundPairFault)
  deriving Repr, DecidableEq

/-- Certify a keyed endpoint beside a direct one. The direct operand keeps the existing
prefer-exact-then-yearless certification, so a profile the model can complete is never read as a
bare label. -/
def elaborateSemanticIndexDateRangeBoundComparison (model : FlatModel)
    (declaringGroup : GroupPath) (keyedAuthored : SurfaceSemanticIndex)
    (keyedBound : DateRangeBound) (directSource : FieldId)
    (directBound : DateRangeBound) (keyedFirst : Bool)
    (comparison : TemporalComparisonOp) :
    Except SemanticIndexDateRangeElabError
      (CheckedSemanticIndexDateRangeBoundComparison model) := do
  let keyed ← elaborateDateRangeSemanticIndexSource model declaringGroup
    keyedAuthored
  let direct ← elaborateDateRangeBoundOperand model directSource directBound
    |>.mapError .directBound
  if hFormats : comparison.admitsFormats model.baseYear.isSome
      keyed.format.components direct.components = true then
    pure {
      keyed, keyedBound, direct, keyedFirst, comparison
      formatsAdmitted := hFormats }
  else
    throw (.boundsNotComparable keyed.format.components direct.components)

namespace CheckedSemanticIndexDateRangeBoundComparison

/-- Read both endpoints once and compare them in their own domain, reusing the direct pair's
projections and verdicts unchanged. A domain disagreement between the certificate's retained profile
and the direct operand's certifying owner is a defensive fault rather than a comparison, exactly as
it is for two direct endpoints. -/
def evaluate (operation : CheckedSemanticIndexDateRangeBoundComparison model)
    (preliminary : CheckedIndexPreliminary model) (keyRaw : RawFlatContext)
    (environment : Env := []) :
    Except SemanticIndexDateRangeBoundComparisonFault
      DateRangeBoundPairResult := do
  let keyedRange ← operation.keyed.observePreliminaryRange preliminary keyRaw
    .validation environment |>.mapError .keyed
  let source := operation.keyed.target.id
  match operation.direct, operation.keyed.exactDomain with
  | .exact direct, true => do
      -- The fault side follows the authored order, so a consumer reading a fault learns which
      -- authored slot failed rather than which operand shape it was.
      let keyedSide : DateRangeBoundFault → DateRangeBoundPairFault :=
        if operation.keyedFirst then .leftExact else .rightExact
      let directSide : DateRangeBoundFault → DateRangeBoundPairFault :=
        if operation.keyedFirst then .rightExact else .leftExact
      let directObserved ←
        direct.evaluateAt environment .validation preliminary.base
          |>.mapError (.endpoint ∘ directSide)
      let keyedSelected ← CheckedDateRangeSource.selectBound source
        operation.keyedBound keyedRange
        |>.mapError (.endpoint ∘ keyedSide)
      let keyedDate ← CheckedDateRangeBoundPair.exactObservation source
        keyedSelected |>.mapError .endpoint
      let directDate ← CheckedDateRangeBoundPair.exactObservation
        direct.source.id directObserved |>.mapError .endpoint
      let left := if operation.keyedFirst then keyedDate else directDate
      let right := if operation.keyedFirst then directDate else keyedDate
      pure (.exact left right (operation.comparison.evalObserved left right))
  | .yearless direct, false => do
      let keyedSide : YearlessDateRangeBoundFault → DateRangeBoundPairFault :=
        if operation.keyedFirst then .leftYearless else .rightYearless
      let directSide : YearlessDateRangeBoundFault → DateRangeBoundPairFault :=
        if operation.keyedFirst then .rightYearless else .leftYearless
      let directObserved ←
        direct.evaluateAt environment .validation preliminary.base
          |>.mapError (.endpoint ∘ directSide)
      let keyedSelected ←
        CheckedYearlessDateRangeBound.projectYearless source
          operation.keyedBound keyedRange
          |>.mapError (.endpoint ∘ keyedSide)
      let keyedLabel := CheckedDateRangeBoundPair.yearlessObservation
        operation.keyedBound keyedSelected
      let directLabel := CheckedDateRangeBoundPair.yearlessObservation
        direct.bound directObserved
      let left := if operation.keyedFirst then keyedLabel else directLabel
      let right := if operation.keyedFirst then directLabel else keyedLabel
      pure (.yearless left right
        (evalSymmetricComparison operation.comparison.holdsMonthDay
          left.asValidationSimpleOperand right.asValidationSimpleOperand))
  | _, _ => throw (.endpoint .mixedDomains)

end CheckedSemanticIndexDateRangeBoundComparison

/-- One keyed range overlapping one direct range, in either authored order. Both operands carry the
operator's own canonical-policy and year-interpretation certificates, and the pair satisfies its
uniform-year rule; the verdict is the operator's own any-pair scan over two single-slot operands. -/
structure CheckedSemanticIndexDateRangeOverlap (model : FlatModel) where
  keyed : CheckedDateRangeSemanticIndexSource model
  keyedCanonical : CheckedCanonicalDateRangeField
  direct : CheckedDateRangeSource model
  directCanonical : CheckedCanonicalDateRangeField
  keyedFirst : Bool
  yearClassUniform :
    dateRangeProfileIncludesYear model keyed.format =
      dateRangeProfileIncludesYear model direct.format

/-- Defensive failure while reading one overlap operand. -/
inductive SemanticIndexDateRangeOverlapFault where
  | keyed (error : SemanticIndexDateRangeError)
  | direct (fault : DirectDateRangeFault)
  /-- Either slot's projection, reported through the operator's own evaluation vocabulary. -/
  | slot (error : DateRangesOverlapEvaluationError)
  deriving Repr, DecidableEq

/-- Certify a keyed overlap operand beside a direct one. The two declaration gates and the
uniform-year rule are the operator's own, applied to the keyed target's declaration exactly as they
are to a direct one, so a keyed operand cannot reach a profile the operator refuses elsewhere. -/
def elaborateSemanticIndexDateRangeOverlap (model : FlatModel)
    (declaringGroup : GroupPath) (keyedAuthored : SurfaceSemanticIndex)
    (directScope : List RepeatableLevel) (directSource : FieldId)
    (keyedFirst : Bool) :
    Except SemanticIndexDateRangeElabError
      (CheckedSemanticIndexDateRangeOverlap model) := do
  let keyed ← elaborateDateRangeSemanticIndexSource model declaringGroup
    keyedAuthored
  let direct ← elaborateDateRangeSourceIn model directScope directSource
    |>.mapError .directSource
  let keyedCanonical ←
    certifyDateRangesOverlapField keyed.targetDeclaration |>.mapError .overlap
  let directCanonical ←
    certifyDateRangesOverlapField direct.declaration |>.mapError .overlap
  if hYear : dateRangeProfileIncludesYear model keyed.format =
      dateRangeProfileIncludesYear model direct.format then
    pure {
      keyed, keyedCanonical, direct, directCanonical, keyedFirst
      yearClassUniform := hYear }
  else
    throw (.overlapMixesYearClass keyed.format direct.format)

namespace CheckedSemanticIndexDateRangeOverlap

/-- Read both operands once and take the operator's own any-pair verdict over two single-slot
operands in authored order. Absence and formal unavailability skip their slot through the shared
projection, which is why an empty operand on either side suppresses the predicate.

Neither slot carries a filter, so the fired polarity is always the operator's unfiltered one. Each
fault address names the operand's declaration with no path: both classes are unreachable under the
canonical certificates above, and the keyed operand has no path of its own in any case, because the
selecting row belongs to the index column rather than to the operand. -/
def evaluate (operation : CheckedSemanticIndexDateRangeOverlap model)
    (preliminary : CheckedIndexPreliminary model) (keyRaw : RawFlatContext)
    (environment : Env := []) :
    Except SemanticIndexDateRangeOverlapFault Verdict := do
  let keyedObserved ← operation.keyed.observePreliminaryRange preliminary keyRaw
    .validation environment |>.mapError .keyed
  let directObserved ←
    operation.direct.evaluateAt environment .validation preliminary.base
      |>.mapError .direct
  let keyedSlot ← dateRangeOverlapSlotOf
    { field := operation.keyed.target.id, path := [] } keyedObserved
    |>.mapError .slot
  let directSlot ← dateRangeOverlapSlotOf
    { field := operation.direct.source.id, path := [] } directObserved
    |>.mapError .slot
  let keyedOperand : ResolvedDateRangeOperand :=
    { slots := [keyedSlot], hasFilter := false }
  let directOperand : ResolvedDateRangeOperand :=
    { slots := [directSlot], hasFilter := false }
  pure (evalDateRangesOverlap
    (if operation.keyedFirst then [keyedOperand, directOperand]
      else [directOperand, keyedOperand]))

end CheckedSemanticIndexDateRangeOverlap

end A12Kernel
