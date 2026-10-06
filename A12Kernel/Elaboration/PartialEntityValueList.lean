import A12Kernel.Elaboration.PartialSemanticIndex
import A12Kernel.Elaboration.ValueListCondition
import A12Kernel.Elaboration.ValuesNotUniqueCondition

namespace A12Kernel

private def partialListExtent (document : CheckedDocument model) (outer : Env)
    (scope : ValidationRelevanceScope) (declarations : List FlatFieldDecl) (bound : Nat) :
    Except CheckedAddressingError (Option (CellObservation PartialSelectedExtent)) := do
  let (addresses, tail) ← model.groupOperandReads document.source.toDocument outer bound declarations
    (·.repeatableScope) |>.mapError .addressing
  let complete := declarations.all fun declaration => scope.coversValueListExtent model declaration.path
    (declaration.repeatableScope.take bound) (declaration.repeatableScope.drop bound) outer
  pure (some (.value { addresses, hasUninstantiatedTail := tail, extentRelevant := complete }))

/-- Partial list members retain available witnesses independently of operand-local extent
nonrelevance; formal cells stay in place for the quantifier's own UNKNOWN policy (spec/10 §5). -/
private def partialListSide {kind : ValueListKind} {model : FlatModel}
    (selection : Option (CellObservation PartialSelectedExtent)) (emptyScalar : Bool)
    (scope : ValidationRelevanceScope)
    (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell))
    (classify : FlatFieldDecl → Env → CheckedCell → Except CheckedAddressingError (ValueListCell kind)) :
    Except CheckedAddressingError (ResolvedValueListSide kind) := do
  match selection with
  | none => pure { (ResolvedValueListSide.empty (kind := kind)) with hasNonRelevant := true }
  | some (.unknown cause) | some (.poison cause) => pure { (ResolvedValueListSide.empty (kind := kind)) with cells := [.unknown cause] }
  | some .empty => pure { (ResolvedValueListSide.empty (kind := kind)) with cells := [.empty] }
  | some (.value extent) =>
      let mut side : ResolvedValueListSide kind := {
        cells := [], hasUninstantiatedTail := extent.hasUninstantiatedTail, hasHaving := false
        hasNonRelevant := !extent.extentRelevant }
      for (declaration, environment) in extent.addresses do
        if scope.coversCell model declaration.path environment then
          let cell ← match read environment declaration.id with
            | .error (.partialUnavailable _ _) => pure none
            | result => result
          match cell with
          | none => side := { side with hasNonRelevant := true }
          | some cell => side := { side with cells := (← classify declaration environment cell) :: side.cells }
        else side := { side with hasNonRelevant := true }
      pure { side with cells := if emptyScalar && extent.addresses.isEmpty then [.empty] else side.cells.reverse }

/-- Retain Number witnesses and operand-local relevance for list quantifiers and uniqueness. -/
def CheckedNumberEntityOperand.resolvePartialValueListSide (source : CheckedNumberEntityOperand model)
    (document : CheckedDocument model) (outer : Env) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell)) :
    Except CheckedAddressingError (ResolvedValueListSide .number) := do
  let selection ← match source with
    | .field source => partialListExtent document outer scope [source.declaration] source.declaration.repeatableScope.length
    | .selected source =>
        resolvePartialSelectedExtent source.source document scope outer read
          (fun declaration bound reopened environment => scope.coversValueListExtent model declaration.path bound reopened environment)
    | .star source => partialListExtent document outer scope [source.source.declaration] source.source.path.firstStar
    | .group source => partialListExtent document outer scope (model.groupSubtreeFields source.groupPath) source.source.boundLevelCount
    | .starHaving _ => return { (ResolvedValueListSide.empty (kind := .number)) with hasHaving := true }
  partialListSide (model := model) selection (!source.isAlreadyMany) scope read
    (fun _ _ cell => pure (observeCell .validation cell).asNumberValueListCell)

/-- Retain declaration-owned token witnesses and operand-local relevance for both list consumers. -/
def CheckedTokenEntityOperand.resolvePartialValueListSide (source : CheckedTokenEntityOperand model)
    (document : CheckedDocument model) (outer : Env) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell)) :
    Except CheckedAddressingError (ResolvedValueListSide .token) := do
  let selection ← match source with
    | .field source => partialListExtent document outer scope [source.declaration] source.declaration.repeatableScope.length
    | .selected source =>
        resolvePartialSelectedExtent source.source document scope outer read
          (fun declaration bound reopened environment => scope.coversValueListExtent model declaration.path bound reopened environment)
    | .star source => partialListExtent document outer scope [source.source.declaration] source.source.path.firstStar
    | .group source => partialListExtent document outer scope (source.slots.map (·.declaration)) source.source.boundLevelCount
  partialListSide (model := model) selection (!source.isAlreadyMany) scope read fun declaration _ cell => do
    let some operand := source.tokenOperands.find? (·.field.id == declaration.id)
      | throw (.checkedDocumentRequired declaration.path)
    pure (operand.checkedValueListCellAt .validation cell)

/-- Partial temporal uniqueness retains concrete witnesses and exact spelling. A supplied
parsed-only replacement needs an overlaid document; stale backing text cannot stand in for it. -/
def CheckedTemporalUniquenessOperand.resolvePartialValueListSide
    (source : CheckedTemporalUniquenessOperand model)
    (document : CheckedDocument model) (outer : Env) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell)) :
    Except CheckedAddressingError (ResolvedValueListSide .token) := do
  if source.hasHaving then return { (ResolvedValueListSide.empty (kind := .token)) with hasHaving := true }
  let selection ← match source with
    | .field source => partialListExtent document outer scope [source.declaration] source.declaration.repeatableScope.length
    | .selected source _ =>
        resolvePartialSelectedExtent source.source document scope outer read
          (fun declaration bound reopened environment => scope.coversValueListExtent model declaration.path bound reopened environment)
    | .star path source _ => partialListExtent document outer scope [source.declaration] path.path.firstStar
    | .group source => partialListExtent document outer scope source.declarations source.source.boundLevelCount
  let emptyScalar := match source with
    | .field _ => true
    | .selected source _ => match source.source with | .inl _ => true | .inr _ => false
    | _ => false
  partialListSide (model := model) selection emptyScalar scope read fun declaration environment cell => do
    match observeCell .validation cell with
    | .value (.temporal _) | .value (.partialDate _) =>
        let address ← document.cellAddress environment declaration.id
        let some stored := document.storedTextForCell address cell
          | throw (.checkedDocumentRequired declaration.path)
        pure (temporalUniquenessCell cell (some stored))
    | .value _ => throw (.checkedDocumentRequired declaration.path)
    | _ => pure (temporalUniquenessCell cell none)

/-- Execute the three list quantifiers without discarding concrete witnesses from an incomplete
selected extent. The whole-source filter gate precedes selection and target reads. -/
def CheckedValueListCondition.evaluatePartialDocument (source : CheckedValueListCondition model)
    (document : CheckedDocument model) (outer : Env) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell)) :
    Except CheckedAddressingError PartialHavingValueListResult := do
  if source.hasHaving then return .skippedHaving
  let verdict ← match source with
    | .number source => do
        let (fields, values) ← source.quantifier.resolveSidesOrdered
          (fun () => source.fields.operands.mapM (·.resolvePartialValueListSide document outer scope read))
          (fun () => source.values.operands.mapM (·.resolvePartialValueListSide document outer scope read))
        pure (source.quantifier.evalOrdered fields values)
    | .token source => do
        let (fields, values) ← source.quantifier.resolveSidesOrdered
          (fun () => source.fields.operands.mapM (·.resolvePartialValueListSide document outer scope read))
          (fun () => source.values.operands.mapM (·.resolvePartialValueListSide document outer scope read))
        pure (source.quantifier.evalOrdered fields values)
    | .literals source => do
        let fields ← source.fields.operands.mapM (·.resolvePartialValueListSide document outer scope read)
        pure (source.quantifier.evalOrdered fields
          [{ cells := (source.firstValue :: source.restValues).map (ValueListCell.present (kind := .token)),
             hasUninstantiatedTail := false, hasHaving := false }])
  pure (.evaluated verdict)

/-- Uniqueness skips unavailable members and tests known values even under incomplete extent
(spec/10 §5); whole-rule filters still suppress partial execution before any source read. -/
def CheckedValuesNotUniqueCondition.evaluatePartialDocument (source : CheckedValuesNotUniqueCondition model)
    (document : CheckedDocument model) (outer : Env) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell)) :
    Except CheckedAddressingError PartialHavingValueListResult := do
  if source.hasHaving then return .skippedHaving
  let verdict ← match source with
    | .number source => do
        let tagged ← collectTaggedValueListCells
          (fun operand => operand.resolvePartialValueListSide document outer scope read) source.operands
        pure (evalValuesNotUniqueVerdict tagged)
    | .token source => do
        let tagged ← collectTaggedValueListCells
          (fun operand => operand.resolvePartialValueListSide document outer scope read) source.source.operands
        pure (evalValuesNotUniqueVerdict tagged)
    | .temporal source => do
        let tagged ← collectTaggedValueListCells
          (fun operand => operand.resolvePartialValueListSide document outer scope read) source.operands
        pure (evalValuesNotUniqueVerdict tagged)
  pure (.evaluated verdict)

end A12Kernel
