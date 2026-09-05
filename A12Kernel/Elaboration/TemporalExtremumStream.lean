import A12Kernel.Elaboration.TemporalExtremumOperands
import A12Kernel.Semantics.TimeAggregate
import A12Kernel.Semantics.DateTimeAggregate
import A12Kernel.Elaboration.CheckedStarDocument

/-! # A12Kernel.Elaboration.TemporalExtremumStream — reading an admitted extremum's operands into the fold

[`Semantics/DateAggregate.lean`](../Semantics/DateAggregate.lean) has always folded an
already-classified temporal stream, and [`TemporalExtremumOperands.lean`](TemporalExtremumOperands.lean)
admits the operand lists the Kernel accepts. Nothing joined them: no code turned a model and a
document into the stream, so the extrema were admissible and unevaluable.

**The element type is the operands' own family, not one universal domain.** That was the open
representation question, and it is settled by measurement rather than chosen here: an extremum's
result is refused against a field of a different temporal family exactly as a plain field of its
own family would be, so a domain that erased the family would admit comparisons the Kernel refuses
([checkpoint](../../docs/SOURCES.md#src-extrema-operand-family-is-positional)). The fold was already
parametric in that type, so nothing about it changes; what this module supplies is the projection
into one family's domain.

**Scope: the three families whose element type the measurements fix, direct field operands, scalar
reads.** The admitted component set must be a whole calendar date, a whole clock, or both, which is
exactly the condition under which `FullDate`, `TimeOfDay`, or the payload's retained `Instant` holds
every operand. The DateTime family differs from its siblings in what its domain *is*: the two
date-free and time-free families order decoded labels, while DateTime orders exact instants, so its
projection hands over the payload's retained instant rather than one rebuilt from the label — the
distinction that survives a zone transition. A component-omitting list —
`yyyy-MM`, or a yearless set completed by a Base Year — is declined rather than folded, because its
values are neither, and its element type is an interval this module does not yet carry
([SG6](../../docs/SEMANTICS-GAPS.md)).

**Two routes, one reader each.** The flat route below takes a `FlatContext` and therefore only direct
field operands; a star, group, or filtered operand denotes a row set that no flat context can
address, and folding just its declaring cell would answer for one row where the Kernel folds all of
them. Those forms have their own reader further down, over the immutable checked document. Both
routes share the three families' projections and the one parametric fold, so a family costs two
declarations per route rather than an architecture.
-/

namespace A12Kernel

/-- Why an admitted operand list cannot be read into one family's fold.

    Every arm is this module's own boundary rather than a Kernel refusal, so none projects a
    diagnostic class: each names a shape the Kernel accepts and this slice does not yet evaluate. -/
inductive TemporalExtremumStreamError where
  /-- The agreed component set is not the one this reader was asked for, so its element type cannot hold the operands. Carries both so a consumer can see which family declined and why. -/
  | componentsMismatch (expected found : TemporalComponents)
  /-- A star, group, or filtered operand, which needs the addressed context the flat route does not take. -/
  | operandNeedsAddressing (path : List String)
  deriving Repr, DecidableEq

namespace TemporalExtremumStream

/-- The one declaration a direct operand reads, or the refusal its form earns here. -/
private def directDeclaration :
    ResolvedFieldEntityOperand model →
      Except TemporalExtremumStreamError FlatFieldDecl
  | .field declaration _ => pure declaration
  | .star source => throw (.operandNeedsAddressing source.declaration.path)
  | .starHaving source _ => throw (.operandNeedsAddressing source.declaration.path)
  | .group reference => throw (.operandNeedsAddressing reference.path)
  | .starredGroup source => throw (.operandNeedsAddressing source.group.path)
  | .starredGroupPresence source => throw (.operandNeedsAddressing source.groupPath)

/-- Read one admitted operand list into a fold side of the caller's element type.

    Operands stay in authored order, which the fold's own scan depends on for its left-biased tie
    and for reporting the first unavailable operand. Neither structural marker is set: a direct
    field list has no uninstantiated tail and no filter, and setting one would weaken every result's
    given-ness for no reason this slice can observe.

    The required component set is the caller's, because it is what fixes the element type: a reader
    that accepted any set would have to hold a value its own domain cannot represent. -/
def readSideWith (expected : TemporalComponents)
    (project : CellObservation → SimpleComparisonOperand α)
    (admitted : CheckedTemporalExtremumOperands model)
    (context : FlatContext) (phase : Phase) :
    Except TemporalExtremumStreamError (ResolvedTemporalAggregateSide α) := do
  if admitted.components ≠ expected then
    throw (.componentsMismatch expected admitted.components)
  else
    let declarations ←
      (admitted.shape.first :: admitted.shape.rest).mapM directDeclaration
    pure {
      operands := declarations.map fun declaration =>
        project (context.observeAt phase declaration.id)
      hasUninstantiatedTail := false
      hasHaving := false }

/-- Read one admitted complete-Date operand list into its fold side. -/
def readDateSide (admitted : CheckedTemporalExtremumOperands model)
    (context : FlatContext) (phase : Phase) :
    Except TemporalExtremumStreamError ResolvedDateAggregateSide :=
  readSideWith TemporalComponents.fullDate
    CellObservation.asDateExtremumOperand admitted context phase

/-- Evaluate one admitted complete-Date extremum against a flat context, as the shared classified
    comparison operand every Date consumer already takes. -/
def evalDate (admitted : CheckedTemporalExtremumOperands model)
    (op : TemporalExtremumOp) (context : FlatContext) (phase : Phase) :
    Except TemporalExtremumStreamError (SimpleComparisonOperand FullDate) := do
  pure (evalDateExtremumAggregate op (← readDateSide admitted context phase))

/-- Read one admitted complete-clock operand list into its fold side. -/
def readTimeSide (admitted : CheckedTemporalExtremumOperands model)
    (context : FlatContext) (phase : Phase) :
    Except TemporalExtremumStreamError ResolvedTimeAggregateSide :=
  readSideWith TemporalComponents.time
    CellObservation.asTimeExtremumOperand admitted context phase

/-- Evaluate one admitted complete-clock extremum against a flat context. The Kernel admits a TIME
    beside a DATE_TIME declared with the degenerate time-only format, and both reach this reader
    through the one component-set gate rather than through a kind test. -/
def evalTime (admitted : CheckedTemporalExtremumOperands model)
    (op : TemporalExtremumOp) (context : FlatContext) (phase : Phase) :
    Except TemporalExtremumStreamError (SimpleComparisonOperand TimeOfDay) := do
  pure (evalTimeExtremumAggregate op (← readTimeSide admitted context phase))

/-! ### The addressed route

A star, group, or filtered operand resolves against the immutable checked document rather than a flat
context, so it reaches the fold through a second entry point rather than through the one above. What
that entry point adds is exactly the two structural markers the flat route could leave unset: a star
whose declared capacity is not full contributes an **uninstantiated tail**, and a filter contributes
its own missing provenance, both of which weaken a selected result's given-ness without changing the
value.

Every arm reuses the sole checked owner of its shape — the direct, star, and group core resolvers —
so this module resolves no topology and reads no cell itself. The three declined arms are the same
three the Number sibling declines: a filtered star needs its `Having` elaborated before it can be
resolved, and admitting one unchecked would be worse than refusing it.

**Over-limit rows supply nothing.** The declared-capacity extent is a property of the operand rather
than of the consuming operator, which is what the capacity sweep's distinct-count document separated
from a mere value agreement
([checkpoint](../../docs/SOURCES.md#src-capacity-consumer-sweep)). The extremum is a fifth consumer,
and the two accounts genuinely differ for it: an over-limit cell is formally unavailable, and this
fold *aborts* on an unavailable operand where the sweep's uniqueness carrier merely skips one — so
reading the complete view would answer UNKNOWN for a document the Kernel folds. No retained row
exercises an over-limit extremum; the extent is taken from the sweep's operand-level mechanism, and
that assumption is recorded with its evidence item in [SG6](../../docs/SEMANTICS-GAPS.md).
-/

/-- Why an admitted operand list cannot be folded against an immutable checked document.

    The two causes are different in kind and stay apart: a decline is this slice's own boundary,
    while an addressing failure is the document's. -/
inductive TemporalExtremumStreamFault where
  | declined (cause : TemporalExtremumStreamError)
  | addressing (cause : CheckedAddressingError)
  deriving Repr, DecidableEq, BEq

/-- The resolved extent one operand contributes, through the sole checked owner of its shape, paired
    with **that operand's** uninstantiated-tail bit.

    The bit is returned beside the core rather than inside it because the two come from different
    queries for a group operand, and the core's constructor is the owner's to hold. -/
private def operandExtent (document : CheckedDocument model) (outer : Env) :
    ResolvedFieldEntityOperand model →
      Except TemporalExtremumStreamFault
        (ResolvedCheckedEntityOperandCore × Bool)
  | .field declaration _ =>
      (document.resolveCheckedDirectEntityOperandCore declaration.id).mapError
        .addressing |>.map fun core => (core, core.hasUninstantiatedTail)
  | .star source =>
      (source.resolveCheckedValidationEntityOperandCore document outer
        none).mapError .addressing
        |>.map fun core => (core, core.hasUninstantiatedTail)
  -- A fixed group asks the shared owner **two** questions about one operand: the walk for its
  -- concrete extent, and the tail query for its declared-but-uninstantiated capacity. Both are
  -- needed and neither implies the other — the walk enumerates instantiated rows only, so its own
  -- tail bit is `false` by construction, while `spec/05` gives an omitted tail symmetric missing
  -- provenance on a selected value. Asking only the walk folded a subtree with spare capacity to a
  -- **given** result where the Kernel's is not given: a wrong flag on a right value.
  | .group reference =>
      let declarations := model.groupSubtreeFields reference.path
      let boundCount :=
        (CheckedEntityGroupSource.fixed (model := model) reference).boundLevelCount
      (do
        let core ← document.resolveCheckedGroupEntityOperandCore outer
          boundCount declarations
        let tail ← document.resolveCheckedGroupUninstantiatedTail outer
          boundCount declarations
        pure (core, tail)).mapError .addressing
  -- A **starred group** takes the same two questions at its own depth. The depth is the star plan's
  -- `firstStar` rather than the path's scope, which is `boundLevelCount`'s own account and not a
  -- reading of the star machinery for the *extent*: the walk still enumerates from the model's
  -- repeatability, and `spec/07`'s warning is about the extent. The Boolean value-count carrier
  -- already resolves its starred groups through exactly this path, which is what makes the depth a
  -- settled correspondence rather than this module's guess.
  | .starredGroup source =>
      let declarations := model.groupSubtreeFields source.group.path
      let boundCount :=
        (CheckedEntityGroupSource.starred source).boundLevelCount
      (do
        let core ← document.resolveCheckedGroupEntityOperandCore outer
          boundCount declarations
        let tail ← document.resolveCheckedGroupUninstantiatedTail outer
          boundCount declarations
        pure (core, tail)).mapError .addressing
  -- The two filtered forms never arrive: admission refuses both with `unsupportedOperandForm`,
  -- because no route here elaborates a `Having`. These arms exist for totality and are reported
  -- rather than skipped, so a future admission widening surfaces as a decline instead of silently
  -- folding an unfiltered row set.
  | .starHaving source _ =>
      throw (.declined (.operandNeedsAddressing source.declaration.path))
  | .starredGroupPresence source =>
      throw (.declined (.operandNeedsAddressing source.groupPath))

/-- Read one admitted operand list against an immutable checked document.

    Operands stay in authored order and each star's rows in canonical topology order, which is what
    the fold's left-biased tie and its first-unavailable report depend on. The two markers are the
    disjunction over the resolved operands, because either one anywhere in the list weakens the whole
    selection's given-ness. -/
def readAddressedSideWith (expected : TemporalComponents)
    (project : CellObservation → SimpleComparisonOperand α)
    (admitted : CheckedTemporalExtremumOperands model)
    (document : CheckedDocument model) (outer : Env) (phase : Phase) :
    Except TemporalExtremumStreamFault (ResolvedTemporalAggregateSide α) := do
  if admitted.components ≠ expected then
    throw (.declined (.componentsMismatch expected admitted.components))
  else
    let extents ←
      (admitted.shape.first :: admitted.shape.rest).mapM
        (operandExtent document outer)
    pure {
      operands := extents.flatMap fun (core, _) =>
        core.inCapacityAddressedCells.map fun addressed =>
          project (observeCell phase addressed.cell)
      hasUninstantiatedTail := extents.any (·.2)
      hasHaving := extents.any (·.1.hasHaving) }

/-- Evaluate one admitted complete-Date extremum against an immutable checked document. -/
def evalAddressedDate (admitted : CheckedTemporalExtremumOperands model)
    (op : TemporalExtremumOp) (document : CheckedDocument model)
    (outer : Env) (phase : Phase) :
    Except TemporalExtremumStreamFault (SimpleComparisonOperand FullDate) := do
  pure (evalDateExtremumAggregate op
    (← readAddressedSideWith TemporalComponents.fullDate
      CellObservation.asDateExtremumOperand admitted document outer phase))

/-- Evaluate one admitted complete-clock extremum against an immutable checked document. -/
def evalAddressedTime (admitted : CheckedTemporalExtremumOperands model)
    (op : TemporalExtremumOp) (document : CheckedDocument model)
    (outer : Env) (phase : Phase) :
    Except TemporalExtremumStreamFault (SimpleComparisonOperand TimeOfDay) := do
  pure (evalTimeExtremumAggregate op
    (← readAddressedSideWith TemporalComponents.time
      CellObservation.asTimeExtremumOperand admitted document outer phase))

/-- Evaluate one admitted complete-DateTime extremum against an immutable checked document. -/
def evalAddressedDateTime (admitted : CheckedTemporalExtremumOperands model)
    (op : TemporalExtremumOp) (document : CheckedDocument model)
    (outer : Env) (phase : Phase) :
    Except TemporalExtremumStreamFault (SimpleComparisonOperand Instant) := do
  pure (evalDateTimeExtremumAggregate op
    (← readAddressedSideWith TemporalComponents.now
      CellObservation.asDateTimeExtremumOperand admitted document outer phase))

/-- Read one admitted complete-DateTime operand list into its fold side.

    The required set is `TemporalComponents.now`, which is the complete date-and-time set; that
    name records the constant's first consumer rather than an exclusive one, exactly as its
    neighbours `today` and `baseYear` are aliases of `fullDate`. -/
def readDateTimeSide (admitted : CheckedTemporalExtremumOperands model)
    (context : FlatContext) (phase : Phase) :
    Except TemporalExtremumStreamError ResolvedDateTimeAggregateSide :=
  readSideWith TemporalComponents.now
    CellObservation.asDateTimeExtremumOperand admitted context phase

/-- Evaluate one admitted complete-DateTime extremum against a flat context. Selection is by exact
    instant, which is the fold's own selector; what this route adds is that the instant reaching it
    is the payload's **retained** one rather than one rebuilt from its wall label. -/
def evalDateTime (admitted : CheckedTemporalExtremumOperands model)
    (op : TemporalExtremumOp) (context : FlatContext) (phase : Phase) :
    Except TemporalExtremumStreamError (SimpleComparisonOperand Instant) := do
  pure (evalDateTimeExtremumAggregate op
    (← readDateTimeSide admitted context phase))

end TemporalExtremumStream

namespace TemporalExtremumStreamError

/-- No arm claims a Kernel class. Both name shapes the Kernel admits and this slice declines, which
    this vocabulary reports as absent coverage rather than as a refusal. -/
def diagnostic? : TemporalExtremumStreamError → Option KernelStaticDiagnostic
  | .componentsMismatch _ _ => none
  | .operandNeedsAddressing _ => none

end TemporalExtremumStreamError

end A12Kernel
