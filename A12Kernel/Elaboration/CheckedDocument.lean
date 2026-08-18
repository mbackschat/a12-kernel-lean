import A12Kernel.Elaboration.StringContext
import A12Kernel.Elaboration.DateRangeInput
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
  deriving Repr, DecidableEq

/-- One exact-model checked input. Only `checkDocument` can construct the certificate; the source placement remains immutable and every placed cell has one cached base formal-check result. -/
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

private def validateCellAddress (model : FlatModel) (rows : List RowAddr)
    (address : CellAddr) : Except CheckedDocumentError FlatFieldDecl := do
  let declaration ←
    (model.lookupUniqueId address.field).mapError (.fieldAddress address)
  if address.path.length != declaration.repeatableScope.length then
    throw (.invalidCellDepth address declaration.repeatableScope.length)
  if address.path.any (· == 0) then
    throw (.zeroCellIndex address)
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

private def ClassifiedCellInput.canonicalScalarCoherent
    (input : ClassifiedCellInput) (model : FlatModel)
    (declaration : FlatFieldDecl) : Bool :=
  match declaration.policy.kind with
  | .boolean => input.raw == classifyStoredBooleanText input.stored
  | .confirm => input.raw == classifyStoredConfirmText input.stored
  | .dateRange =>
      match declaration.toDateRangeDeclarationPolicy? with
      | none => true
      | some policy =>
          match classifyStoredDateRange model.timeZoneId policy input.stored with
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
  let numericInput := match declaration.policy.kind with
    | .number _ =>
        if input.stored.isEmpty then none
        else some (input.numericDecimal.map NumericStoredInput.decimal
          |>.getD (.text input.stored))
    | _ => none
  pure {
    address := input.address
    cell := base.withOverRepetitionIf overLimit
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

/-- Query one model-legal address. In-cap absence is a clean empty checked cell, over-limit ancestry is unavailable, and malformed addressing remains an explicit structural error. -/
def read (checked : CheckedDocument model) (address : CellAddr) :
    Except CheckedDocumentError CheckedCell := do
  let declaration ← validateCellAddress model checked.source.instantiatedRows address
  let overLimit ← match model.addressOverLimit?
      declaration.repeatableScope address.path with
    | some overLimit => pure overLimit
    | none => throw (.incoherentRepeatableScope declaration.repeatableScope)
  match checked.checkedCells.find? fun placement => placement.address == address with
  | some placement => pure placement.cell
  | none => pure ((checkAdmittedRawCell .empty).withOverRepetitionIf overLimit)

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
  read field :=
    match checked.read { field, path := [] } with
    | .ok cell => cell
    | .error _ => malformedCheckedCell

/-- Project ordinary nonrepeatable computation reads under one explicit world. Heterogeneous computation runs share this immutable source boundary before adding their typed dependency overlay. -/
def scalarComputationContext (checked : CheckedDocument model)
    (world : World) : ScalarComputationContext :=
  { read := checked.flatContext.read, world := some world }

/-- The sole checked context for String computation. Ordinary leaves retain the exact checked document cell; Number leaves replace only their parsed payload with the already-selected formal-read text. Presence and formal poison are therefore unchanged for guards. -/
def stringComputationContext (checked : CheckedDocument model) :
    StringComputationContext where
  read field :=
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

end CheckedDocument

end A12Kernel
