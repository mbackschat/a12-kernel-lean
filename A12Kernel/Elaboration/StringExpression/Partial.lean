import A12Kernel.Elaboration.StringExpression
import A12Kernel.Elaboration.PartialSemanticIndex

namespace A12Kernel

private abbrev PartialStringM := ExceptT StringComputationFault (StateT Bool (Except CheckedAddressingError))

private def readPartialStringSource (document : CheckedDocument model)
    (scope : ValidationRelevanceScope) (outer : Env)
    (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell))
    (isRelevant : FlatRelevance)
    (source : ResolvedStringSource model) :
    Except CheckedAddressingError (Option (CellObservation (Env × CheckedCell))) := do
  let readAt (relevance : ValidationRelevanceScope) row field := do
    discard <| document.cellAddress row field
    if !relevance.coversField model field row then return none
    pure ((← read row field).map fun cell => CellObservation.value (row, cell))
  match source with
  | .inl field => if isRelevant field then readAt (scope.withGlobals model) outer field else pure none
  | .inr selected =>
      let view ← document.applyPartialGeneratedPreliminaryForScope scope |>.mapError .indexPreliminary
      match ← selected.selectPartial view outer read with
      | none => pure none
      | some .empty => pure (if view.relevance.coversValueListExtent model selected.targetDeclaration.path
          selected.indexDeclaration.repeatableScope.dropLast [selected.group.level] outer then some .empty else none)
      | some (.unknown cause) => pure (some (.unknown cause))
      | some (.poison cause) => pure (some (.poison cause))
      | some (.value row) => readAt view.relevance row selected.targetDeclaration.id

/-- The validation fold reaches later range faults even after an unavailable read (spec/10 §12).
The temporary empty operand is private to the fold; unavailable results never escape as omission. -/
def CheckedBoundStringExpression.evalPartial (expression : CheckedBoundStringExpression model)
    (document : CheckedDocument model) (scope : ValidationRelevanceScope) (outer : Env)
    (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell))
    (isRelevant : FlatRelevance := fun _ => true) :
    Except CheckedAddressingError (Option (SimpleComparisonOperand String)) := do
  let fieldId : ResolvedStringSource model → FieldId
    | .inl field => field
    | .inr source => source.targetDeclaration.id
  let readOperand (source : ResolvedStringSource model) : PartialStringM (SimpleComparisonOperand String) := do
    let field := fieldId source
    let observation ← liftM (readPartialStringSource document scope outer read isRelevant source)
    match observation with
    | none => modify (fun _ => true); pure .notEvaluated
    | some .empty => pure .notEvaluated
    | some (.unknown cause) | some (.poison cause) => pure (.unknown cause)
    | some (.value (row, cell)) =>
        let declaration ← liftM ((model.lookupUniqueId field).mapError (CheckedAddressingError.field field))
        let observed := observeCell .validation cell
        match declaration.policy.kind, observed with
        | .number _, .value (.num _) =>
            let address ← liftM (document.cellAddress row field)
            -- spec/04's stored-decimal identity clause selects text by storage regime. A callback-only numeric replacement
            -- has no such text; like storedTextForCell, require a corresponding document overlay.
            if (document.read address).toOption != some cell then throw .indexedReadUnavailable
            let textCell ← liftM ((document.readNumberFormalText address).mapError CheckedAddressingError.document)
            let some text := textCell.parsed | throw .indexedReadUnavailable
            pure (.value text true)
        | .number _, .empty => pure .notEvaluated
        | .number _, .unknown cause | .number _, .poison cause => pure (.unknown cause)
        | .number _, .value _ => throw (.fieldKindMismatch field)
        | _, _ =>
            match StringExpr.readObservedOperand field observed with
            | .ok operand => pure operand
            | .error fault => throw fault
  let (result, unavailable) ← (expression.core.evalOperandWithSource fieldId .validation readOperand).run false
  let operand ← result.mapError CheckedAddressingError.stringExpression
  pure (if unavailable then none else some operand)

/-- Both operands are reached before relevance masks the verdict; empty computed text retains
the same omission rule as full String comparison (spec/10 §12). -/
def CheckedStringExpressionComparison.evalPartial (comparison : CheckedStringExpressionComparison model)
    (document : CheckedDocument model) (scope : ValidationRelevanceScope) (outer : Env)
    (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell))
    (isRelevant : FlatRelevance := fun _ => true) :
    Except CheckedAddressingError Verdict := do
  let left ← comparison.left.evalPartial document scope outer read isRelevant
  let right ← comparison.right.evalPartial document scope outer read isRelevant
  let operand : SimpleComparisonOperand String → SimpleComparisonOperand String
    | .value "" _ => .notEvaluated
    | other => other
  match left, right with
  | some left, some right => pure (evalSymmetricComparison
      (fun a b => comparison.operator.holds (a == b)) (operand left) (operand right))
  | _, _ => pure .unknown

end A12Kernel
