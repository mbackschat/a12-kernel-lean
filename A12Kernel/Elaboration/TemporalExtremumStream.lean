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
distinction that survives a zone transition.

**A component-omitting list folds too, on two further arms, and no interval element type is involved
— which an earlier version of this note assumed.** The Kernel admits `yyyy-MM` or a yearless `MM`
and orders it at the shared set's own precision, the yearless one even with no Base Year declared
([checkpoint](../../docs/sources/evaluation-and-application-routes.md#src-extrema-component-omitting-fold)).
Within one shared component set a canonical representative is order-preserving, so the two arms are
`FullDate` for a year-bearing set — its unnamed components masked to the canonical value the
distinct count already fixes, `Semantics/FullDate.lean`'s `maskedDateComponents` — and
`MonthDayValue` for a yearless one, both of which already carry an ordering.

**The shared set fixes the element type; each operand's own declaration fixes what is masked.** Those
are different questions and conflating them is a live defect rather than a subtlety: the admission
gate supplements every declaration by the model Base Year before agreeing the shared set, so a list
whose set names the year can hold an operand that does not name it — the admitted mixed-precision
list. Masking such an operand against the shared set takes its year from the cell, where the Kernel
takes it from the declared Base Year. `TemporalDistinctCount.lean` already projected each slot
through its own set for exactly this reason; this reader now does too. `omittingDateExtremumArm`
selects between them on the set, never the declared kind, and a set the Base Year supplements is
year-bearing. Since the reader is parametric in the element type, the widening added a projection
and no domain ([SG23](../../docs/SEMANTICS-GAPS.md#sg23--the-temporal-extrema)).

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

/-- The component set an operand's **own** declaration names, before the Base-Year supplementation
    the admission gate applied when it fixed the list's shared set.

    This is what a masking projection must read. The shared set can name the year while one
    operand's declaration omits it — exactly the admitted mixed-precision list — and masking such an
    operand against the shared set would take the year from its cell instead of from the declared
    Base Year, which is the supplementation the Kernel does not perform.

    Falling back to the shared set keeps this total. Admission has already established that every
    direct operand is temporal, so the fallback is unreachable; gating on that would put the
    precondition into the projection for no gain. -/
private def declaredComponents (shared : TemporalComponents)
    (declaration : FlatFieldDecl) : TemporalComponents :=
  match declaration.toTemporalField? with
  | some field => field.components
  | none => shared

/-- Read one admitted operand list into a fold side of the caller's element type.

    Operands stay in authored order, which the fold's own scan depends on for its left-biased tie
    and for reporting the first unavailable operand. Neither structural marker is set: a direct
    field list has no uninstantiated tail and no filter, and setting one would weaken every result's
    given-ness for no reason this slice can observe.

    The required component set is the caller's, because it is what fixes the element type: a reader
    that accepted any set would have to hold a value its own domain cannot represent.

    `project` receives each operand's **own** declaration, not just its observation, because the
    list's set and an operand's set can differ: the admission gate supplements every declaration by
    the model Base Year before fixing the shared set, so a list's set can name a component that one
    operand's declaration does not. A projection that masks unnamed components must therefore ask
    the operand rather than the list, or it reads a cell component no declaration named. Readers
    whose element type needs no masking ignore the argument. -/
def readSideWith (expected : TemporalComponents)
    (project : FlatFieldDecl → CellObservation → SimpleComparisonOperand α)
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
        project declaration (context.observeAt phase declaration.id)
      hasUninstantiatedTail := false
      hasHaving := false }

/-- Read one admitted complete-Date operand list into its fold side. -/
def readDateSide (admitted : CheckedTemporalExtremumOperands model)
    (context : FlatContext) (phase : Phase) :
    Except TemporalExtremumStreamError ResolvedDateAggregateSide :=
  readSideWith TemporalComponents.fullDate
    (fun _ => CellObservation.asDateExtremumOperand) admitted context phase

/-- Evaluate one admitted complete-Date extremum against a flat context, as the shared classified
    comparison operand every Date consumer already takes. -/
def evalDate (admitted : CheckedTemporalExtremumOperands model)
    (op : TemporalExtremumOp) (context : FlatContext) (phase : Phase) :
    Except TemporalExtremumStreamError (SimpleComparisonOperand FullDate) := do
  pure (evalDateExtremumAggregate op (← readDateSide admitted context phase))

/-! ## The reduced-precision entry points

A component-omitting list folds at its **own** declared set, so these two pass `admitted.components`
as the expected set: the reader's equality check is then satisfied by construction, which is the
honest shape here because the set is not a constant of the arm but the thing the arm is keyed on.
-/

/-- Whether an admitted component-omitting Date list orders as a completed date or as a yearless
    calendar position. Two arms and not one: a list with no year available anywhere must order on the
    position it spells, and completing it against an invented year would order two such values by
    that invention. -/
inductive OmittingDateExtremumArm where
  | dated
  | yearless
  deriving Repr, DecidableEq

/-- The arm an admitted list orders at.

    **No Base Year parameter, unlike the sibling distinct count**, and the asymmetry is the
    certificates' rather than the operators': this gate applies `withBaseYear` to every declaration
    *before* fixing the expected set, so `components` here is already supplemented and asking again
    would be a second way to compute one thing. `TemporalDistinctCount` stores the authored set and
    therefore must supplement at the fold. Reading the flag off the certificate that carries it is
    what keeps the two from drifting. -/
def omittingDateExtremumArm {model : FlatModel}
    (admitted : CheckedTemporalExtremumOperands model) : OmittingDateExtremumArm :=
  if admitted.components.year then .dated else .yearless

/-- Read one admitted **year-bearing** component-omitting Date list into its fold side. -/
def readMaskedDateSide (admitted : CheckedTemporalExtremumOperands model)
    (baseYear : Option Int) (context : FlatContext) (phase : Phase) :
    Except TemporalExtremumStreamError ResolvedDateAggregateSide :=
  readSideWith admitted.components
    (fun declaration => CellObservation.asMaskedDateExtremumOperand
      (declaredComponents admitted.components declaration) baseYear)
    admitted context phase

/-- Evaluate one admitted year-bearing component-omitting Date extremum. -/
def evalMaskedDate (admitted : CheckedTemporalExtremumOperands model)
    (op : TemporalExtremumOp) (baseYear : Option Int)
    (context : FlatContext) (phase : Phase) :
    Except TemporalExtremumStreamError (SimpleComparisonOperand FullDate) := do
  pure (evalDateExtremumAggregate op (← readMaskedDateSide admitted baseYear context phase))

/-- Read one admitted **yearless** Date list into its fold side. -/
def readYearlessDateSide (admitted : CheckedTemporalExtremumOperands model)
    (context : FlatContext) (phase : Phase) :
    Except TemporalExtremumStreamError ResolvedYearlessDateAggregateSide :=
  readSideWith admitted.components
    (fun declaration => CellObservation.asYearlessDateExtremumOperand
      (declaredComponents admitted.components declaration))
    admitted context phase

/-- Evaluate one admitted yearless Date extremum. -/
def evalYearlessDate (admitted : CheckedTemporalExtremumOperands model)
    (op : TemporalExtremumOp) (context : FlatContext) (phase : Phase) :
    Except TemporalExtremumStreamError (SimpleComparisonOperand MonthDayValue) := do
  pure (evalYearlessDateExtremumAggregate op (← readYearlessDateSide admitted context phase))

/-- Read one admitted complete-clock operand list into its fold side. -/
def readTimeSide (admitted : CheckedTemporalExtremumOperands model)
    (context : FlatContext) (phase : Phase) :
    Except TemporalExtremumStreamError ResolvedTimeAggregateSide :=
  readSideWith TemporalComponents.time
    (fun _ => CellObservation.asTimeExtremumOperand) admitted context phase

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
so this module resolves no topology and reads no cell itself. A filtered star is *admitted* by the
gate, because the Kernel admits it, but declined here: resolving it needs its `Having` elaborated at
admission onto a checked operand this capsule's shared shape does not carry, and folding it without
the filter would return the unfiltered rows — a wrong answer where the decline is merely a missing
one.

**Over-limit rows supply nothing.** The declared-capacity extent is a property of the operand rather
than of the consuming operator, which is what the capacity sweep's distinct-count document separated
from a mere value agreement
([checkpoint](../../docs/SOURCES.md#src-capacity-consumer-sweep)). The extremum is a fifth consumer,
and the two accounts genuinely differ for it: an over-limit cell is formally unavailable, and this
fold *aborts* on an unavailable operand where the sweep's uniqueness carrier merely skips one — so
reading the complete view would answer UNKNOWN for a document the Kernel folds. No retained row
exercises an over-limit extremum; the extent is taken from the sweep's operand-level mechanism, and
that assumption is recorded with its evidence item in [SG23](../../docs/SEMANTICS-GAPS.md#sg23--the-temporal-extrema-operand-gate-element-type-and-fold).
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
private def operandExtent (document : CheckedDocument model) (outer : Env)
    (filter : Option CorrelatedHaving) :
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
  -- A filtered star folds its **selected** rows, through the same core resolver the plain star uses
  -- — the filter is that resolver's own parameter, so nothing here interprets it. The operand is
  -- declined only when admission could not certify the filter, which is not a refusal of the shape:
  -- the Kernel admits it, and folding the unfiltered rows would answer a different question with no
  -- signal that it had.
  | .starHaving source _ =>
      match filter with
      | some condition =>
          (source.resolveCheckedValidationEntityOperandCore document outer
            (some condition)).mapError .addressing
            |>.map fun core => (core, core.hasUninstantiatedTail)
      | none =>
          throw (.declined (.operandNeedsAddressing source.declaration.path))
  -- The **presence** terminal takes the same two questions at the same depth. `boundLevelCount`
  -- gives both starred shapes their star plan's `firstStar`, and the Boolean value-count carrier
  -- already resolves its presence operands through this exact owner — a completed second consumer
  -- with the same meaning and result domain, which is what makes the depth a settled reuse here
  -- rather than a reading of the star machinery.
  | .starredGroupPresence source =>
      let declarations := model.groupSubtreeFields source.groupPath
      let boundCount :=
        (CheckedEntityGroupSource.starredPresence source).boundLevelCount
      (do
        let core ← document.resolveCheckedGroupEntityOperandCore outer
          boundCount declarations
        let tail ← document.resolveCheckedGroupUninstantiatedTail outer
          boundCount declarations
        pure (core, tail)).mapError .addressing

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
    -- Zipped rather than indexed, and safe to zip because `filtersAligned` fixes both lengths: a
    -- filter belongs to exactly one operand, and applying one to its neighbour would silently
    -- select the wrong rows.
    let extents ←
      ((admitted.shape.first :: admitted.shape.rest).zip
        admitted.filters).mapM fun (operand, filter) =>
          operandExtent document outer filter operand
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
    (fun _ => CellObservation.asDateTimeExtremumOperand) admitted context phase

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
