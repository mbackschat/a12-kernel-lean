import A12Kernel.Elaboration.PartialSemanticIndex
import A12Kernel.Elaboration.NumericAggregate.Entities
import A12Kernel.Elaboration.TokenValueCount
import A12Kernel.Elaboration.BooleanValueCount

namespace A12Kernel

/-- Each count owns its extent gate: value counts take declared-slot coverage and distinct counts
reduced-universal relevance (spec/10 §5). Topology fixes the unreopened coordinates. -/
private def partialCountExtent (document : CheckedDocument model) (outer : Env)
    (scope : ValidationRelevanceScope) (declarations : List FlatFieldDecl) (bound : Nat)
    (extentRelevant : FlatFieldDecl → List RepeatableLevel → List RepeatableLevel → Env → Bool :=
      fun declaration _ reopened environment => scope.coversValueCountExtent model declaration.path reopened environment) :
    Except CheckedAddressingError (Option (CellObservation (List (FlatFieldDecl × Env) × Bool))) := do
  if !declarations.all (fun declaration => extentRelevant declaration
      (declaration.repeatableScope.take bound) (declaration.repeatableScope.drop bound) outer) then return none
  let extent ← model.groupOperandReads document.source.toDocument outer bound declarations
    (·.repeatableScope) |>.mapError .addressing
  pure (some (.value extent))

private def readPartialCountCells {kind : ValueListKind} {model : FlatModel}
    (scope : ValidationRelevanceScope)
    (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell))
    (classify : FlatFieldDecl → CheckedCell → Except CheckedAddressingError (ValueListCell kind)) :
    List (FlatFieldDecl × Env) → List (ValueListCell kind) →
      Except CheckedAddressingError (Sum (List (ValueListCell kind)) PartialValidationNumberAggregateResult)
  | [], reversed => pure (.inl reversed.reverse)
  | (declaration, environment) :: rest, reversed => do
      if !scope.coversCell model declaration.path environment then return .inr .nonRelevant
      let some cell ← read environment declaration.id
        | throw (.partialUnavailable environment declaration.id)
      match ← classify declaration cell with
      | .unknown cause => pure (.inr (.evaluated (.unknown cause)))
      | value => readPartialCountCells (model := model) scope read classify rest (value :: reversed)

/-- Count scans stop at reached formal or call-local unavailability; later reads cannot replace
that outcome. Empty scalar selection remains a cell, while an absent keyed star has no cells. -/
private def partialCountSide {kind : ValueListKind} {model : FlatModel}
    (selection : Option (CellObservation (List (FlatFieldDecl × Env) × Bool)))
    (emptyScalar : Bool) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell))
    (classify : FlatFieldDecl → CheckedCell → Except CheckedAddressingError (ValueListCell kind)) :
    Except CheckedAddressingError (Sum (ResolvedValueListSide kind) PartialValidationNumberAggregateResult) := do
  match selection with
  | none => pure (.inr .nonRelevant)
  | some (.unknown cause) | some (.poison cause) => pure (.inr (.evaluated (.unknown cause)))
  | some .empty => pure (.inl { cells := [.empty], hasUninstantiatedTail := false, hasHaving := false })
  | some (.value (addresses, hasTail)) =>
      match ← readPartialCountCells (model := model) scope read classify addresses [] with
      | .inr result => pure (.inr result)
      | .inl cells => pure (.inl {
          cells := if emptyScalar && addresses.isEmpty then [.empty] else cells
          hasUninstantiatedTail := hasTail, hasHaving := false })

private def numberPartialCountSide (source : CheckedNumberEntityOperand model)
    (document : CheckedDocument model) (outer : Env) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell)) :
    Except CheckedAddressingError (Sum (ResolvedValueListSide .number) PartialValidationNumberAggregateResult) := do
  let selection ← match source with
    | .field source => pure (some (.value ([(source.declaration, outer)], false)))
    | .selected source =>
        resolvePartialSelectedAddresses source.source document scope outer read
          (fun declaration bound reopened environment => scope.coversValueListExtent model declaration.path bound reopened environment)
    | .star source => partialCountExtent document outer scope [source.source.declaration] source.source.path.firstStar
    | .group source => partialCountExtent document outer scope (model.groupSubtreeFields source.groupPath) source.source.boundLevelCount
    | .starHaving _ => return .inr .skippedHaving
  let emptyScalar := !source.isAlreadyMany
  partialCountSide (model := model) selection emptyScalar scope read
    (fun _ cell => pure (observeCell .validation cell).asNumberValueListCell)

private def tokenPartialCountSide (source : CheckedTokenEntityOperand model)
    (document : CheckedDocument model) (outer : Env) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell))
    (extentRelevant : FlatFieldDecl → List RepeatableLevel → List RepeatableLevel → Env → Bool :=
      fun declaration _ reopened environment => scope.coversValueCountExtent model declaration.path reopened environment) :
    Except CheckedAddressingError (Sum (ResolvedValueListSide .token) PartialValidationNumberAggregateResult) := do
  let selection ← match source with
    | .field source => pure (some (.value ([(source.declaration, outer)], false)))
    | .selected source =>
        resolvePartialSelectedAddresses source.source document scope outer read extentRelevant
    | .star source => partialCountExtent document outer scope [source.source.declaration] source.source.path.firstStar extentRelevant
    | .group source => partialCountExtent document outer scope (source.slots.map (·.declaration)) source.source.boundLevelCount extentRelevant
  let emptyScalar := !source.isAlreadyMany
  partialCountSide (model := model) selection emptyScalar scope read fun declaration cell => do
    let some operand := source.tokenOperands.find? (·.field.id == declaration.id)
      | throw (.checkedDocumentRequired declaration.path)
    pure (operand.checkedValueListCellAt .validation cell)

private def booleanPartialCountSide (source : CheckedBooleanValueCountOperand model expected)
    (document : CheckedDocument model) (outer : Env) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell)) :
    Except CheckedAddressingError (Sum (ResolvedValueListSide .token) PartialValidationNumberAggregateResult) := do
  let selection ← match source with
    | .field source => pure (some (.value ([(source.declaration, outer)], false)))
    | .selected source =>
        resolvePartialSelectedAddresses source.source document scope outer read
          (fun declaration bound reopened environment => scope.coversValueListExtent model declaration.path bound reopened environment)
    | .star source =>
        if source.filter.isSome then return .inr .skippedHaving
        partialCountExtent document outer scope [source.source.declaration] source.source.path.firstStar
    | .group source => partialCountExtent document outer scope source.fields source.source.boundLevelCount
  partialCountSide (model := model) selection (!source.isAlreadyMany) scope read
    (fun _ cell => pure (booleanValueCountCellAt .validation cell))

/-- Boolean and Confirm counts share call-local selection/relevance with Number and token counts;
the checked constant's kind certificate and Boolean observation projection remain distinct. -/
def CheckedBooleanValueCountSource.evaluatePartialValueCountDocument (source : CheckedBooleanValueCountSource model)
    (document : CheckedDocument model) (outer : Env) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell)) :
    Except CheckedAddressingError PartialValidationNumberAggregateResult :=
  evalPartialResolvedValueCountOperands (kind := .token) (booleanValueCountToken source.expected)
    source.operands source.hasHaving (fun operand => booleanPartialCountSide operand document outer scope read)

/-- Partial Number value counts retain the caller's availability view and the source's checked
shape; the shared count fold owns matching, empty movement and the numeric result. -/
def CheckedNumberEntitySource.evaluatePartialValueCountDocument (source : CheckedNumberEntitySource model)
    (expected : Rat) (document : CheckedDocument model) (outer : Env) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell)) :
    Except CheckedAddressingError PartialValidationNumberAggregateResult :=
  evalPartialResolvedValueCountOperands (kind := .number) expected source.operands source.hasHaving
    (fun operand => numberPartialCountSide operand document outer scope read)

/-- Stored/category token counts classify each reached cell through its declaration-owned
projection; partial selection never borrows another Enumeration field's domain. -/
def CheckedTokenValueCountSource.evaluatePartialValueCountDocument (source : CheckedTokenValueCountSource model)
    (document : CheckedDocument model) (outer : Env) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell)) :
    Except CheckedAddressingError PartialValidationNumberAggregateResult :=
  evalPartialResolvedValueCountOperands (kind := .token) source.expected source.source.operands source.source.hasHaving
    (fun operand => tokenPartialCountSide operand document outer scope read)

/-- Partial token distinct counts share call-local classification with value counts but require
complete aggregate extents; the shared ordered fold preserves the first unavailable read. -/
def CheckedTokenEntitySource.evaluatePartialDistinctCountDocument (source : CheckedTokenEntitySource model)
    (document : CheckedDocument model) (outer : Env) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell)) :
    Except CheckedAddressingError PartialValidationAggregateResult := do
  if source.hasHaving then return .skippedHaving
  match ← scanResolvedValueListOperands
      (fun operand => tokenPartialCountSide operand document outer scope read
        (fun declaration bound reopened environment => scope.coversAggregateExtent model declaration.path bound reopened environment))
      (fun cause => .evaluated (.unknown cause))
      (fun accumulated _ side => accumulated.append side)
      source.operands (ResolvedValueListSide.empty (kind := .token)) with
  | .inl side => pure (.evaluated (evalDistinctCountAggregate side))
  | .inr result => pure result

end A12Kernel
