import A12Kernel.Elaboration.StringContext
import A12Kernel.Elaboration.DateRangeInput
import A12Kernel.Elaboration.PartialDateInput
import A12Kernel.Elaboration.OmittingDateInput
import A12Kernel.Elaboration.DateTimeInput
import A12Kernel.Elaboration.TimeInput
import A12Kernel.Semantics.NumericInput
import A12Kernel.Semantics.ScalarText
import A12Kernel.Semantics.StarAddressing
import A12Kernel.Semantics.StringComputation

/-! # Immutable model-certified checked documents

This module starts at the theory's established scalar-parser boundary. A finite input retains physical rows, placed stored text, and the corresponding preclassified scalar input. Construction validates finite topology and placement once, applies the shared address-formal over-repetition gate, runs the already prepared model-owned checker once for every address-admissible placed cell, and produces one immutable checked view shared by existing consumers. Processing context, generated preliminary findings, relevance, scheduling, and application remain separate.
-/

namespace A12Kernel

/-- One physically placed field plus its parser-boundary classification. `stored` retains application text. `raw` remains caller-classified for non-Number kinds and must match the canonical Boolean/Confirm classifier plus the bounded DateRange classifier whenever its declaration and zone are supported. A filled Number may carry an explicit decimal representation in `numericDecimal`; `none` selects the exact String-valued regime already carried by `stored`. Document checking derives and verifies the selected formal-read classification. An absent cell has no entry. -/
structure ClassifiedCellInput where
  address : CellAddr
  stored : String
  raw : RawCell
  /-- Explicit decimal-valued Number input. On a filled Number, `none` means the exact String-valued `stored` input; non-Number and present-empty inputs also require `none`. -/
  numericDecimal : Option NumericInputDecimal := none
  deriving Repr, DecidableEq

/-- Finite immutable document data. Rows remain independent of placed cells. -/
structure DocumentData where
  instantiatedRows : List RowAddr
  cells : List ClassifiedCellInput
  deriving Repr, DecidableEq

namespace DocumentData

/-- Compile finite transport data to the established pure lookup view used by addressing semantics. -/
def toDocument (data : DocumentData) : Document where
  instantiatedRows := data.instantiatedRows
  rawCells := fun address =>
    (data.cells.find? fun cell => cell.address == address).map (·.stored)

end DocumentData

inductive CheckedDocumentError where
  | duplicateRow (row : RowAddr)
  | duplicateCell (address : CellAddr)
  | incoherentCell (address : CellAddr)
  | unknownRowGroup (row : RowAddr)
  | invalidRowDepth (row : RowAddr) (expected : Nat)
  | zeroRowIndex (row : RowAddr)
  | missingParentRow (row parent : RowAddr)
  | nonprefixRow (row predecessor : RowAddr)
  | fieldAddress (address : CellAddr) (cause : ResolveError)
  | invalidCellDepth (address : CellAddr) (expected : Nat)
  | zeroCellIndex (address : CellAddr)
  | missingRow (row : RowAddr)
  | incoherentRepeatableScope (scope : List RepeatableLevel)
  | nonNumericField (address : CellAddr)
  /-- The stored-text read was asked for a declaration whose stored text is not its whole input. -/
  | nonPartialDateField (address : CellAddr)
  deriving Repr, DecidableEq

/-- Structural failures while projecting one repeatable scope's physically instantiated rows into complete named environments. -/
inductive ActualRowEnvironmentError where
  | missingScope
  | unknownLevel (level : RepeatableLevel)
  | incoherentScope (supplied expected : List RepeatableLevel)
  | incoherentRow (row : RowAddr)
  deriving Repr, DecidableEq

structure CheckedCellPlacement where
  address : CellAddr
  cell : CheckedCell
  /-- The exact selected Number input regime. Non-Number and empty placements carry `none`. -/
  numericInput : Option NumericStoredInput := none
  /-- The selected Number formal-read text, including on a formally rejected Number placement. Non-Number and empty placements carry `none`. -/
  numericFormalReadText : Option String := none
  /-- The stored text this placement's cell was read from, which a reader pairs with that cell: a
  token scan's selected text and a partial Date's spelling. It travels with the cell, so a document
  overlaid with a completed target reads that target's rendering rather than the source's text.
  A placement with no text carries `none`. -/
  storedText : Option String := none
  deriving Repr, DecidableEq

/-- One exact-model checked input. `checkDocument` constructs it from source data, so every placed cell is
that source cell's one cached base formal-check result; `overlayNonrepeatableCells` derives a read view
from one, whose replaced placements are no longer that check's result and whose own documentation names
what stays source-derived. The source placement remains immutable in both. -/
structure CheckedDocument (model : FlatModel) where
  private mk ::
  source : DocumentData
  checkedCells : List CheckedCellPlacement
  modelWellFormed : model.validate.isOk = true
  rowsNodup : source.instantiatedRows.Nodup

private def firstDuplicateRow? : List RowAddr → Option RowAddr
  | [] => none
  | row :: rest =>
      if rest.contains row then some row else firstDuplicateRow? rest

private theorem firstDuplicateRow_none_iff_nodup (rows : List RowAddr) :
    firstDuplicateRow? rows = none ↔ rows.Nodup := by
  induction rows with
  | nil => simp [firstDuplicateRow?]
  | cons row remaining inductionHypothesis =>
      by_cases member : row ∈ remaining <;>
        simp [firstDuplicateRow?, member, inductionHypothesis]

private def firstDuplicateCell? : List ClassifiedCellInput → Option CellAddr
  | [] => none
  | cell :: rest =>
      if rest.any fun candidate => candidate.address == cell.address then
        some cell.address
      else
        firstDuplicateCell? rest

/-- Resolve one validated field or group scope to the shared structural axes. A checked model makes failure unreachable; retaining `Option` keeps malformed internal callers explicit. -/
def FlatModel.repeatableAxesForScope? (model : FlatModel) :
    List RepeatableLevel → Option (List StarAxis)
  | [] => some []
  | level :: levels => do
      let group ← model.repeatableGroupAtLevel? level
      let remaining ← model.repeatableAxesForScope? levels
      pure ({ level, repeatability := group.repeatability } :: remaining)

/-- Apply the shared over-capacity decision to one exact model scope and coordinate path. Address depth and zero-coordinate checks remain owned by placement validation. -/
def FlatModel.addressOverLimit? (model : FlatModel)
    (scope : List RepeatableLevel) (path : List Nat) : Option Bool := do
  let axes ← model.repeatableAxesForScope? scope
  pure (StarAxes.environmentOverLimit axes (scope.zip path))

private def parentRow? (scope : List RepeatableLevel) (row : RowAddr) :
    Option RowAddr :=
  match scope.reverse, row.path.reverse with
  | _ :: parentLevel :: _, _ :: _ =>
      some { group := parentLevel, path := row.path.dropLast }
  | _, _ => none

private def predecessorRow? (row : RowAddr) : Option RowAddr :=
  match row.path.reverse with
  | [] => none
  | coordinate :: _ =>
      if coordinate ≤ 1 then none
      else some {
        group := row.group
        path := row.path.dropLast ++ [coordinate - 1]
      }

private structure CheckedRows (rows : List RowAddr) : Type where
  nodup : rows.Nodup

private def validateRows (model : FlatModel) (rows : List RowAddr) :
    Except CheckedDocumentError (CheckedRows rows) := do
  let checkedRows ← match duplicate : firstDuplicateRow? rows with
  | some row => throw (.duplicateRow row)
  | none =>
      pure {
        nodup := firstDuplicateRow_none_iff_nodup rows |>.mp duplicate
      }
  for row in rows do
    let group ← match model.repeatableGroupAtLevel? row.group with
      | some group => pure group
      | none => throw (.unknownRowGroup row)
    let scope := model.repeatableScopeForGroupPath group.path
    if row.path.length != scope.length then
      throw (.invalidRowDepth row scope.length)
    if row.path.any (· == 0) then
      throw (.zeroRowIndex row)
    match parentRow? scope row with
    | some parent =>
        if !rows.contains parent then throw (.missingParentRow row parent)
    | none => pure ()
    match predecessorRow? row with
    | some predecessor =>
        if !rows.contains predecessor then throw (.nonprefixRow row predecessor)
    | none => pure ()
  pure checkedRows

/-- Derive the exact addressed repeatable ancestors for one scope and coordinate path. Depth and positivity are checked by the caller. The result contains only the directly addressed ancestry; predecessor padding is a separate application behavior. -/
def repeatableAncestorRowsFor
    (scope : List RepeatableLevel) (coordinates : List Nat) :
    List RowAddr :=
  go scope coordinates []
where
  go : List RepeatableLevel → List Nat → List Nat → List RowAddr
    | [], [], _ => []
    | level :: levels, coordinate :: remaining, priorPath =>
        let path := priorPath ++ [coordinate]
        { group := level, path } :: go levels remaining path
    | _, _, _ => []

private def validateCellAddressShape (model : FlatModel)
    (address : CellAddr) : Except CheckedDocumentError FlatFieldDecl := do
  let declaration ←
    (model.lookupUniqueId address.field).mapError (.fieldAddress address)
  if address.path.length != declaration.repeatableScope.length then
    throw (.invalidCellDepth address declaration.repeatableScope.length)
  if address.path.any (· == 0) then
    throw (.zeroCellIndex address)
  pure declaration

private def validateCellAddress (model : FlatModel) (rows : List RowAddr)
    (address : CellAddr) : Except CheckedDocumentError FlatFieldDecl := do
  let declaration ← validateCellAddressShape model address
  for row in repeatableAncestorRowsFor
      declaration.repeatableScope address.path do
    if !rows.contains row then throw (.missingRow row)
  pure declaration

private def ClassifiedCellInput.ordinaryCoherent
    (input : ClassifiedCellInput) : Bool :=
  input.numericDecimal.isNone && if input.stored.isEmpty then
    input.raw == .presentEmpty
  else
    match input.raw with
    | .parsed _ | .rejected _ => true
    | .empty | .presentEmpty => false

/-- Whether a declaration may hold a value whose stored text is its **whole** input. That is a Date
declaring a partial precision: such a declaration holds ordinary fully known values and partially known
ones, the latter as `Value.partialDate` carrying the stored spelling, so its text is the one channel
that reads both. -/
private def FlatFieldDecl.mayStorePartialDateText
    (declaration : FlatFieldDecl) : Bool :=
  match declaration.policy.kind, declaration.toTemporalTargetPolicy? with
  | .temporal .date _, some policy => policy.partialMode != .full
  | _, _ => false

private def ClassifiedCellInput.numberCoherent
    (input : ClassifiedCellInput) (constraints : NumericTargetConstraints)
    (info : NumField) : Bool :=
  if input.stored.isEmpty then
    input.numericDecimal.isNone && input.raw == .presentEmpty
  else
    let numeric := input.numericDecimal.map NumericStoredInput.decimal
      |>.getD (.text input.stored)
    numeric.storedText == input.stored &&
      constraints.classifyFormalRead info numeric == input.raw

/-- Whether a caller's temporal cell agrees with what the model's own classifier derives from its
stored text. This is **not** `RawCell` equality, and the difference is load-bearing: the stored text
fixes the wall-label components, the calendar provenance, and the *second*, but a retained instant may
carry a **sub-second remainder** the text cannot express — established behaviour this project already
tests, where milliseconds survive an exact shift until a target renderer drops them. So the instant is
compared to within one second and everything the text does determine is compared exactly. A whole-hour
disagreement, such as a UTC-resolved instant under a non-UTC model zone, still fails. -/
private def temporalCellAgrees (canonical actual : RawCell) : Bool :=
  let sameSecond (left right : Instant) : Bool :=
    (left.epochMillis - right.epochMillis).natAbs < 1000
  match canonical, actual with
  | .empty, .empty => true
  | .presentEmpty, .presentEmpty => true
  | .rejected expected, .rejected found => expected == found
  | .parsed (.temporal (.date expected)),
    .parsed (.temporal (.date found)) =>
      expected.parts == found.parts && expected.basis == found.basis &&
        sameSecond expected.instant found.instant
  | .parsed (.temporal (.dateTime expectedInstant expectedDate expectedTime
      expectedBasis)),
    .parsed (.temporal (.dateTime foundInstant foundDate foundTime
      foundBasis)) =>
      expectedDate == foundDate && expectedTime == foundTime &&
        expectedBasis == foundBasis &&
        sameSecond expectedInstant foundInstant
  | .parsed (.temporal (.time expectedInstant expectedTime)),
    .parsed (.temporal (.time foundInstant foundTime)) =>
      expectedTime == foundTime && sameSecond expectedInstant foundInstant
  | _, _ => false

private def ClassifiedCellInput.canonicalScalarCoherent
    (input : ClassifiedCellInput) (model : FlatModel)
    (declaration : FlatFieldDecl) : Bool :=
  match declaration.policy.kind with
  | .boolean => input.raw == classifyStoredBooleanText input.stored
  | .confirm => input.raw == classifyStoredConfirmText input.stored
  | .temporal _ _ =>
      -- The partially known arm is admitted only on a precision-partial declaration whose own
      -- classifier admits exactly the stored text as partially known, and a text value there is
      -- refused, one of the two encodings the arm replaced; the other, a stored text beside no value,
      -- is refused by `ordinaryCoherent` before this check. Whether a temporal value or a rejection
      -- agrees with its text stays the `temporallyCoherent` property's question, as on every other
      -- temporal declaration.
      match certifyPartialDateInputField declaration with
      | .error _ =>
          match input.raw with
          | .parsed (.partialDate _) => false
          | _ => true
      | .ok checked =>
          match input.raw with
          | .parsed (.temporal _) => true
          | .parsed (.partialDate text) => text == input.stored && checked.admitsPartiallyKnownText text
          | .parsed _ => false
          | .empty | .presentEmpty | .rejected _ => true
  | .dateRange =>
      match declaration.toDateRangeDeclarationPolicy? with
      | none => true
      | some policy =>
          match classifyStoredDateRangeForModel model.timeZoneId model.baseYear
              policy input.stored with
          | .ok canonical => input.raw == canonical
          | .error (.unsupportedPolicy _ _) => true
          | .error (.unsupportedZone _) | .error (.unresolvableEndpoint _) => false
  | _ => true

private def checkPlacedCell
    (prepared : PreparedFlatStringContext model compilePattern)
    (locale : String) (rows : List RowAddr)
    (input : ClassifiedCellInput) :
    Except CheckedDocumentError CheckedCellPlacement := do
  let declaration ← validateCellAddress model rows input.address
  let coherent := match declaration.policy.kind with
    | .number info =>
        input.numberCoherent declaration.numericTargetConstraints info
    | .boolean | .confirm | .string | .enumeration | .temporal _ _ | .dateRange =>
        input.ordinaryCoherent
  if !coherent then throw (.incoherentCell input.address)
  if !input.canonicalScalarCoherent model declaration then
    throw (.incoherentCell input.address)
  let overLimit ← match model.addressOverLimit?
      declaration.repeatableScope input.address.path with
    | some overLimit => pure overLimit
    | none => throw (.incoherentRepeatableScope declaration.repeatableScope)
  let raw : RawFlatContext := {
    read := fun field => if field == input.address.field then input.raw else .empty
  }
  let base :=
    if overLimit then
      checkAdmittedRawCell input.raw
    else
      (prepared.checkContext locale raw).read input.address.field
  let base := if overLimit || model.legalCharset.accepts input.stored then base
    else base.withFinding .unsupportedCharacter
  let numericInput := match declaration.policy.kind with
    | .number _ =>
        if input.stored.isEmpty then none
        else some (input.numericDecimal.map NumericStoredInput.decimal
          |>.getD (.text input.stored))
    | _ => none
  pure {
    address := input.address
    cell := base.withOverRepetitionIf overLimit
    storedText := some input.stored
    numericInput
    numericFormalReadText := match declaration.policy.kind, numericInput with
      | .number _, some numeric =>
          some (numeric.formalReadText
            declaration.numericTargetConstraints.minFractionalDigits)
      | _, _ => none
  }

/-- Validate finite placement, suppress scalar checking beneath over-limit ancestry, and cache every placed cell in one exact checked view. -/
def checkDocument (prepared : PreparedFlatStringContext model compilePattern)
    (locale : String) (source : DocumentData) :
    Except CheckedDocumentError (CheckedDocument model) := do
  let checkedRows ← validateRows model source.instantiatedRows
  match firstDuplicateCell? source.cells with
  | some address => throw (.duplicateCell address)
  | none => pure ()
  let checkedCells ← source.cells.mapM
    (checkPlacedCell prepared locale source.instantiatedRows)
  pure {
    source
    checkedCells
    modelWellFormed := prepared.patterns.modelWellFormed
    rowsNodup := checkedRows.nodup
  }

namespace CheckedDocument

/-- Project physical rows at the deepest level of one repeatable scope into complete named environments, preserving source order. Blank-but-instantiated rows remain observable; rows belonging to other groups do not enter the result. -/
def actualRowEnvironments (checked : CheckedDocument model)
    (scope : List RepeatableLevel) :
    Except ActualRowEnvironmentError (List Env) :=
  match scope.reverse with
  | [] => .error .missingScope
  | deepest :: _ => do
      let group ← match model.repeatableGroupAtLevel? deepest with
        | some group => pure group
        | none => throw (.unknownLevel deepest)
      let expected := model.repeatableScopeForGroupPath group.path
      if scope != expected then
        throw (.incoherentScope scope expected)
      (checked.source.instantiatedRows.filter fun row =>
        row.group == deepest).mapM fun row =>
          if row.path.length == scope.length then
            pure (scope.zip row.path)
          else
            throw (.incoherentRow row)

/-- Whether one target-row environment lies beyond a declared capacity on any of its axes.

Decided over the whole environment rather than the target level's own coordinate: an over-limit
**ancestor** excludes its descendants although their own coordinates are in range, measured over three
repetition axes ([checkpoint](../../docs/SOURCES.md#src-over-limit-computation-target)). -/
def environmentOverLimit (checked : CheckedDocument model)
    (scope : List RepeatableLevel) (environment : Env) : Bool :=
  let _ := checked
  model.addressOverLimit? scope (environment.map (·.2)) == some true

/-- The in-capacity physical rows at one repeatable scope, in document order.

This is **not** the general computation-target domain: an addressed target still receives an outcome
at an over-limit row (a clear), which `computationRowOutcomes` below expresses. It is the domain of a
carrier whose own index column is capacity-bounded, where an over-limit row has no index entry at all
and a structural lookup there would fail rather than produce a value. Whether such a carrier also
clears its over-limit rows is not measured; this projection claims only the execution domain. -/
def inCapacityRowEnvironments (checked : CheckedDocument model)
    (scope : List RepeatableLevel) :
    Except ActualRowEnvironmentError (List Env) := do
  let environments ← checked.actualRowEnvironments scope
  pure (environments.filter fun environment =>
    !checked.environmentOverLimit scope environment)

/-- Walk a **computation target**'s physical rows in document order, producing a value at each
in-capacity row and only a clear at each over-limit one.

The split is measured rather than derived. A repeatable target declared `max 3` receives its
computed value on exactly three rows whether the document instantiates three, four, or five, while
the excess rows draw `zuGrosseZeile` and `zuGrosseKontextnummer`. The excess row is **not** skipped:
a target cell holding a stored value there is reported cleared, in the same run where its in-capacity
siblings compute from a source present for both
([checkpoint](../../docs/SOURCES.md#src-over-limit-computation-target)). So `clearOnly` returns the
carrier's own no-value outcome, which every application projection already turns into a clear, and
dropping the row instead would leave a stale value the Kernel removes.

Document order is preserved and the cleared row keeps its natural position, matching the observed
outcome sequence. `actualRowEnvironments` stays the physical domain because validation still reports
the excluded row. -/
def computationRowOutcomes {Outcome Fault : Type} (checked : CheckedDocument model)
    (scope : List RepeatableLevel)
    (onRowError : ActualRowEnvironmentError → Fault)
    (clearOnly produce : Env → Except Fault Outcome) :
    Except Fault (List Outcome) := do
  let environments ← (checked.actualRowEnvironments scope).mapError onRowError
  environments.mapM fun environment =>
    if checked.environmentOverLimit scope environment then clearOnly environment
    else produce environment

/-- A computation target's outcomes over its instances: a fixed target's one, at the empty
environment, or a repeatable target's per row as `computationRowOutcomes` gives them. -/
def computationTargetOutcomes {Outcome Fault : Type} (checked : CheckedDocument model)
    (scope : List RepeatableLevel)
    (onRowError : ActualRowEnvironmentError → Fault)
    (clearOnly produce : Env → Except Fault Outcome) :
    Except Fault (List Outcome) :=
  if scope.isEmpty then (·::[]) <$> produce []
  else checked.computationRowOutcomes scope onRowError clearOnly produce

private def environmentExtends (parent child : Env) : Bool :=
  child.take parent.length == parent

private def extendValidationRowEnvironments
    (checked : CheckedDocument model)
    (scopePrefix : List RepeatableLevel) (parents : List Env) :
    List RepeatableLevel →
      Except ActualRowEnvironmentError (List Env)
  | [] => pure parents
  | level :: remaining => do
      let scope := scopePrefix ++ [level]
      let actual ← checked.actualRowEnvironments scope
      let implicit := (parents.filter fun parent =>
        !actual.any (environmentExtends parent)).map fun parent =>
          parent ++ [(level, 1)]
      extendValidationRowEnvironments checked scope
        (actual ++ implicit) remaining

/-- Project the row domain used only by nested validation iteration. The outermost level remains concrete-only. At each deeper level, every existing parent without a concrete child contributes child coordinate 1, and that projection composes recursively. As a deterministic Lean-internal account, concrete deepest rows retain their physical encounter order and implicit descendants follow them in parent projection order; external observations establish row membership and pointers but not this relative emission order. -/
def validationRowEnvironments (checked : CheckedDocument model)
    (scope : List RepeatableLevel) :
    Except ActualRowEnvironmentError (List Env) :=
  match scope with
  | [] => .error .missingScope
  | [outer] => checked.actualRowEnvironments [outer]
  | outer :: remaining => do
      let actualOuter ← checked.actualRowEnvironments [outer]
      extendValidationRowEnvironments checked [outer]
        actualOuter remaining

/-- The document a later computation of one run reads: each listed nonrepeatable field's own placement
replaced by the listed placement, or removed, so that field reads empty. Inside a run a completed target
is read through the cell its outcome projects and a pending one reads empty, whatever the document stores
for either ([`kf459`](../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf459)).

This is a read overlay for evaluators that take the whole document, and nothing here applies a result.
Every placement read — `read`, the stored text paired with a cell, the Number input regime and
formal-read text, and the contexts built on them — sees the listed placement, which is why a placement
rather than a bare cell is listed: a replaced target keeps its rendering and a Number its input regime
and formal-read text only if the caller supplies them. The source data and rows are unchanged, so what
is read off `source` — `temporallyCoherent` — still describes the source document. -/
def overlayNonrepeatableCells (checked : CheckedDocument model)
    (placements : List (FieldId × Option CheckedCellPlacement)) : CheckedDocument model :=
  { checked with
    checkedCells :=
      (checked.checkedCells.filter fun placement =>
        !(placement.address.path.isEmpty && placements.any (·.1 == placement.address.field))) ++
      placements.filterMap fun (field, placement) =>
        placement.map fun placement => { placement with address := { field, path := [] } } }

/-- The document a later computation of a plan with repeatable targets reads: every placement of a
`hidden` field removed, so a pending target reads empty at every row, and each completed placement put
at its exact address. `overlayNonrepeatableCells` is the instance whose placements all sit at the root;
the reasons there, a stale stored value never read and a placement rather than a bare cell, are the
same here. -/
def overlayCells (checked : CheckedDocument model) (hidden : List FieldId)
    (placements : List CheckedCellPlacement) : CheckedDocument model :=
  { checked with
    checkedCells :=
      (checked.checkedCells.filter fun placement =>
        !hidden.contains placement.address.field &&
          !placements.any (·.address == placement.address)) ++ placements }

/-- Read a placement using the address declaration supplied by the validation gate. This common
body is exposed so overlay laws can unfold the lookup without duplicating the two read views. -/
def readValidatedAddress (checked : CheckedDocument model) (declaration : FlatFieldDecl)
    (address : CellAddr) : Except CheckedDocumentError CheckedCell := do
  let overLimit ← match model.addressOverLimit?
      declaration.repeatableScope address.path with
    | some overLimit => pure overLimit
    | none => throw (.incoherentRepeatableScope declaration.repeatableScope)
  match checked.checkedCells.find? fun placement => placement.address == address with
  | some placement => pure placement.cell
  | none => pure ((checkAdmittedRawCell .empty).withOverRepetitionIf overLimit)

/-- Query one model-legal instantiated address. Absence of a cell is empty, but absence of its
physical ancestor rows is an addressing failure. -/
def read (checked : CheckedDocument model) (address : CellAddr) :
    Except CheckedDocumentError CheckedCell := do
  checked.readValidatedAddress (← validateCellAddress model checked.source.instantiatedRows address) address

/-- Read a declared slot even when its row is absent. The field-fill grid (2026-10-03) requires a
filter to read an absent declared cell as empty; this view leaves physical topology unchanged. -/
def readDeclared (checked : CheckedDocument model) (address : CellAddr) :
    Except CheckedDocumentError CheckedCell := do
  checked.readValidatedAddress (← validateCellAddressShape model address) address

/-- The stored text placed at one address, read from the placement that owns it, so an overlaid
target reads its rendering; `none` where no placement or no text is placed. -/
def storedTextAt (checked : CheckedDocument model) (address : CellAddr) : Option String :=
  (checked.checkedCells.find? fun placement => placement.address == address).bind (·.storedText)

/-- Select stored text through the declaration's complete scope, so validation and computation
read the same row-local spelling as their parsed-cell view. -/
def storedTextIn (checked : CheckedDocument model) (environment : Env)
    (field : FieldId) : Option String := do
  let declaration ← (model.lookupUniqueId field).toOption
  let path ← (environment.pathForScope declaration.repeatableScope).toOption
  checked.storedTextAt { field, path }

/-- Read one placed cell's **stored text**, for a Date declaring a partial precision.

The text is the one channel that carries every value such a declaration can hold: a *partially* known
Date, which denotes an interval and is placed as `Value.partialDate` with its spelling, and a fully known
one, placed as a temporal value. Reading the text therefore serves both, and what it denotes is left
entirely to the partial-Date classifier that owns it: this read reports presence, emptiness, an earlier
formal rejection, and over-repetition, and decides nothing about the text itself.

Refused for any other declaration, so a caller cannot reach a Number's or a full Date's text by a route
that skips that kind's own read.

Absence, present-emptiness, and a rejection stay distinguishable: absence carries `rawPresent := false`,
a present-but-empty text carries `true` with no parsed text, and a rejection carries its cause. -/
def readStoredText (checked : CheckedDocument model) (address : CellAddr) :
    Except CheckedDocumentError (CheckedCell String) := do
  let declaration ←
    validateCellAddress model checked.source.instantiatedRows address
  if !declaration.mayStorePartialDateText then
    throw (.nonPartialDateField address)
  let cell ← checked.read address
  pure {
    rawPresent := cell.rawPresent
    parsed := if cell.parsed.isSome then checked.storedTextAt address else none
    findings := cell.findings }

/-- Read one checked Number input as a typed cell carrying the regime-selected text. Empty, invalid, and over-limit states retain their ordinary checked-cell structure; the text is never reconstructed from the parsed rational. -/
def readNumberFormalText (checked : CheckedDocument model)
    (address : CellAddr) :
    Except CheckedDocumentError (CheckedCell String) := do
  let declaration ← validateCellAddress model checked.source.instantiatedRows address
  match declaration.policy.kind with
  | .number _ => pure ()
  | _ => throw (.nonNumericField address)
  let cell ← checked.read address
  let formalRead := (checked.checkedCells.find?
    fun placement => placement.address == address).bind
      (fun placement => placement.numericFormalReadText)
  let textCell : CheckedCell String := {
    rawPresent := cell.rawPresent
    parsed := if cell.parsed.isSome then formalRead else none
    findings := cell.findings
  }
  pure textCell

/-- Observe the checked Number input through the regime-selected text required by `FieldValueAsString`. -/
def observeNumberFormalRead (checked : CheckedDocument model)
    (phase : Phase) (address : CellAddr) :
    Except CheckedDocumentError (CellObservation String) := do
  pure (observeCell phase (← checked.readNumberFormalText address))

/-- Existing nonrepeatable evaluators consume the same checked cells. Their checked plans cannot request repeatable fields; a forged request fails closed. -/
def flatContext (checked : CheckedDocument model) : FlatContext where
  storedText field := checked.storedTextAt { field, path := [] }
  read field :=
    match checked.read { field, path := [] } with
    | .ok cell => cell
    | .error _ => malformedCheckedCell

/-- Expose immutable topology with the checked document's current overlay to addressed guards. -/
def computationFillContext (checked : CheckedDocument model) : ComputationFillContext where
  document := checked.source.toDocument
  read environment field :=
    let cell := do
      let declaration ← (model.lookupUniqueId field).toOption
      let path ← (environment.pathForScope declaration.repeatableScope).toOption
      (checked.read { field, path }).toOption
    cell.getD malformedCheckedCell

/-- Read a guard's cell and exact stored text at the same model-owned address. The document
already carries completed target placements (calendar review-control grid, 2026-10-04). -/
def computationContextAt (checked : CheckedDocument model) (environment : Env) : ScalarComputationContext where
  read := checked.computationFillContext.read environment
  storedText := checked.storedTextIn environment
  numberText field := do
    let declaration ← (model.lookupUniqueId field).toOption
    let path ← (environment.pathForScope declaration.repeatableScope).toOption
    (← (checked.readNumberFormalText { field, path }).toOption).parsed
  row := environment
  addressed := some checked.computationFillContext

/-- The checked document's complete computation context before a caller supplies its world. -/
def computationContext (checked : CheckedDocument model) : ScalarComputationContext :=
  { read := checked.flatContext.read, storedText := checked.flatContext.storedText,
    numberText := fun field => ((checked.readNumberFormalText { field, path := [] }).toOption).bind (·.parsed)
    addressed := some checked.computationFillContext }

/-- Project ordinary nonrepeatable computation reads under one explicit world. Heterogeneous computation runs share this immutable source boundary before adding their typed dependency overlay. -/
def scalarComputationContext (checked : CheckedDocument model)
    (world : World) : ScalarComputationContext :=
  checked.computationContext.withWorld world

/-- The sole checked context for String computation. Ordinary leaves retain the exact checked document cell; Number leaves replace only their parsed payload with the already-selected formal-read text. Presence and formal poison are therefore unchanged for guards. -/
def stringComputationContext (checked : CheckedDocument model) :
    StringComputationContext :=
  { checked.computationContext with
    read := fun field =>
      match model.lookupUniqueId field with
      | .ok declaration =>
          match declaration.policy.kind with
          | .number _ =>
              match checked.readNumberFormalText { field, path := [] } with
              | .ok cell => {
                  rawPresent := cell.rawPresent
                  parsed := cell.parsed.map Value.str
                  findings := cell.findings
                }
              | .error _ => malformedCheckedCell
          | _ => checked.flatContext.read field
      | .error _ => malformedCheckedCell
  }

/-- The cell a concrete date takes in the model zone, as the fragment read-back builds it, so a
classifier-completed date is compared with an actual cell by instant and calendar basis as well as by
parts, exactly as a complete Date is. -/
private def canonicalDateCell? (model : FlatModel) (date : CivilDate) : Option RawCell := do
  let profile ← ModelZone.ConcreteProfile.ofId? model.timeZoneId
  let value ← profile.resolveCompletedDateParts? date.parts
  pure (.parsed (.temporal (.date value)))

/-- The cell the owning classifier makes of a temporal declaration's stored text: `none` when no
classifier owns the declaration, and `some none` when one does but the text resolves to no instant in
the model zone. A precision-partial text that is only partly known is the `partialDate` arm carrying
that text; a component-omitting text is the earliest date it denotes. A clock uses the existing
Time classifier's model-zone anchor, regardless of the declaration's temporal kind. -/
def canonicalTemporalCell? (model : FlatModel) (declaration : FlatFieldDecl) (stored : String) :
    Option (Option RawCell) :=
  match declaration.policy.kind with
  | .temporal _ components =>
      match certifyPartialDateInputField declaration, certifyOmittingDateInputField declaration with
      | .ok owner, _ =>
          some <| match owner.classifyStored stored with
            | .presentEmpty => some .presentEmpty
            | .rejected cause => some (.rejected cause)
            | .admitted value => match value.value with
              | .full date => canonicalDateCell? model date.civil
              | .omittedDay _ | .omittedMonth _ | .omittedYear => some (.parsed (.partialDate stored))
      | .error _, .ok owner =>
          some <| match owner.classifyStoredForModel model.baseYear stored with
            | .presentEmpty => some .presentEmpty
            | .rejected cause => some (.rejected cause)
            | .admitted value =>
                (value.earliestCivil? model.baseYearOrDefault).bind (canonicalDateCell? model)
      | .error _, .error _ =>
          if components == TemporalComponents.fullDate then
            (certifyFullDateInputField declaration).toOption.map fun owner =>
              (owner.classifyStoredForModel model.timeZoneId stored).toOption
          else if components == TemporalComponents.now then
            (certifyDateTimeInputField declaration).toOption.map fun owner =>
              (owner.classifyStoredForModel model.timeZoneId stored).toOption
          else
            (certifyTimeInputField declaration).toOption.map fun owner =>
              (owner.classifyStoredForModel model.timeZoneId stored).toOption
  | _ => none

/-- Whether every placed temporal cell whose declaration a classifier owns agrees with the value that
classifier derives from that cell's **own** stored text.

**Deliberately a property a consumer asks for, not a construction gate.** `checkDocument` does enforce
stored/value correspondence for Boolean, Confirm, Number, and DateRange cells; temporal cells are the
documented exception, for two independent reasons.

The first is semantic. The duplicate-value clause compares a temporal cell's *exact stored text*, so the
case that pins which account that clause states needs two cells whose text and decoded value disagree —
`SPEC-2026-08-05-03` records whether a real model can store such a pair as its open residual. Making the
text a function of the value would delete the clause's own subject from the representation.

The second is coverage, and it is bounded by the declared format rather than the declared kind, because
the Kernel's parser follows the declared format with no fallback to the kind (`SPEC-2026-09-06-09`). Five
declaration families have an owning classifier: a complete Date, a complete DateTime, a precision-partial
Date, whose partially known text is the `partialDate` arm and whose fully known text is that date, and a
component-omitting Date or date fragment, whose value is the earliest date its text denotes, and a
clock at the bounded `HH:mm:ss` profile. A gate covering part of a family is one no consumer could
rely on, whereas a property may honestly report on the part it knows.

`true` therefore means: no cell on one of those five declaration families contradicts its stored text.
It does not certify an unsupported declaration and is not a claim that the kernel would produce this
document. -/
def temporallyCoherent (checked : CheckedDocument model) : Bool :=
  checked.source.cells.all fun input =>
    match model.lookupUniqueId input.address.field with
    | .error _ => true
    | .ok declaration =>
        match canonicalTemporalCell? model declaration input.stored with
        | none => true
        | some none => false
        | some (some canonical) => canonical == input.raw || temporalCellAgrees canonical input.raw

end CheckedDocument

end A12Kernel
