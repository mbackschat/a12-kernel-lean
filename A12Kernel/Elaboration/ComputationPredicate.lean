import A12Kernel.Elaboration.TokenComparison
import A12Kernel.Elaboration.FirstFilledComparison
import A12Kernel.Elaboration.KeyedGroupPresence
import A12Kernel.Elaboration.StringExpression
import A12Kernel.Elaboration.ValueListCondition
import A12Kernel.Elaboration.NumericAggregate.Entities
import A12Kernel.Semantics.ComputationValueList
import A12Kernel.Elaboration.ScalarFieldComparison
import A12Kernel.Elaboration.DateRangePredicate
import A12Kernel.Elaboration.TemporalExpression
import A12Kernel.Elaboration.ComputationOverlap
import A12Kernel.Elaboration.ComputationFieldFill
import A12Kernel.Elaboration.ValuesNotUniqueCondition
import A12Kernel.Elaboration.CustomFieldValidity
import A12Kernel.Elaboration.ComputationStringPattern

namespace A12Kernel

inductive SurfaceScalarMembershipMembers where
  | fields (members : List SurfaceTextFieldOperand)
  | numbers (members : List Int)
  | tokens (members : List String)
  deriving Repr, DecidableEq

inductive SurfaceComputationPredicate where
  | keyedGroupPresence (operator : GroupPresenceOperator) (source : SurfaceKeyedEntityExtent)
  | indexedFieldPresence (operator : RepeatableFieldPresenceOperator) (source : SurfaceSemanticIndex)
  | pattern (source : SurfaceStringPatternCondition)
  | indexedPattern (source : SurfaceIndexedStringPatternCondition)
  | dateValidity (operation : ConstructedDateValidityOp) (source : SurfaceConstructedDateComponents SurfaceScalarDateComponent)
  | typeValidity (operation : CustomFieldValidityOp) (source : SurfaceFieldPath) (name : String)
  | indexedTypeValidity (operation : CustomFieldValidityOp) (source : SurfaceSemanticIndex) (name : String)
  | stringExpression (operator : EqualityOp) (left right : StringExpr SurfaceFieldPath String)
  | selectedStringExpression (operator : EqualityOp) (left right : SurfaceSelectedStringExpression)
  | tokenComparison (operator : EqualityOp) (left right : SurfaceTokenComparisonOperand)
  | selectedComparison (operator : EqualityOp) (left right : SurfaceFirstFilledComparisonOperand)
  | temporal (operator : TemporalComparisonOp) (left right : SurfaceScalarTemporalExpression)
  | fieldComparison (operator : SurfaceComparisonOp) (left right : SurfaceFieldPath)
  | dateRangeComparison (operator : EqualityOp) (source : SurfaceDateRangeComparison)
  | scalarMembership (operator : ValueListMembershipOp) (subject : SurfaceTextFieldOperand)
      (members : SurfaceScalarMembershipMembers)
  | entityValueList (source : SurfaceNumberEntityValueListSource)
  | tokenLiteralValueList (source : SurfaceTokenEntityStringLiteralValueListSource)
  | fieldFill (operator : FieldFillQuantifier) (source : SurfaceFieldEntitySource)
  | uniqueness (source : SurfaceFieldEntitySource)
  | overlap (source : SurfaceFieldEntitySource)
  | scalarOverlap (source : SurfaceAtLeastOneDateRangeOverlapsSource)

inductive ComputationPredicateElabError where
  | keyedGroup (error : KeyedEntityExtentError)
  | semanticIndex (error : SemanticIndexElabError)
  | pattern (error : ComputationStringPatternElabError)
  | indexedPattern (error : IndexedStringPatternElabError)
  | typeOperand (error : CustomFieldValidityOperandElabError)
  | typeName (error : CustomFieldValidityElabError)
  | indexedTypeOperand (error : IndexedCustomFieldValidityElabError)
  | stringExpression (error : StringComputationElabError)
  | tokenComparison (error : TokenComparisonElabError)
  | selectedComparison (error : FirstFilledComparisonElabError)
  | temporal (error : ScalarTemporalExpressionError)
  | comparison (error : ScalarFieldComparisonElabError)
  | dateRangeComparison (error : DateRangePredicateElabError)
  | read (error : ResolveError)
  | number (error : NumberEntityElabError)
  | uniqueness (number : NumberValuesNotUniqueElabError)
      (token : TokenValuesNotUniqueElabError) (temporal : TemporalValuesNotUniqueElabError)
  | emptyMembers
  | incoherent
  | token (error : TokenEntityValueListElabError)
  | literals (error : TokenEntityStringLiteralValueListElabError)
  | fieldFill (error : FieldFillListElabError)
  | overlap (error : IteratedDateRangeConditionElabError)
  deriving Repr, DecidableEq

def ComputationPredicateElabError.dateValidityDiagnostic? : ComputationPredicateElabError → Option KernelStaticDiagnostic
  | .temporal error => error.dateValidityDiagnostic?
  | _ => none

inductive ComputationPredicateError where
  | indexSelection (error : CheckedAddressingError)
  | stringExpression (error : StringComputationFault)
  /-- Runtime failure at a reached guard becomes the target's calculation-value error, separately
  from inherited operand poison (comparison-guard grid, 2026-10-04). -/
  | valueFailure
  | temporalUnavailable
  | fieldFill (error : ComputationFillError)
  | fieldKindMismatch (field : FieldId)
  | contextRequired
  | unsupportedSelectedComparisonOperand
  | addressing (error : StarAddressingError)
  deriving Repr, DecidableEq

/-- Retain typed source certificates and authored filters; computation traversal keeps reached
errors distinct from validation's unknown verdict. -/
inductive CheckedComputationPredicate (model : FlatModel) where
  | keyedGroupPresence (operator : GroupPresenceOperator) (source : CheckedKeyedEntityExtent model) (dependencyKind : ComputationGroupDependencyKind)
  | indexedFieldPresence (operator : RepeatableFieldPresenceOperator) (source : CheckedSemanticIndexSource model)
  | pattern (source : CheckedComputationStringPattern model)
  | indexedPattern (source : CheckedIndexedStringPatternLeaf model)
  | dateValidity (operation : ConstructedDateValidityOp) (source : CheckedConstructedDateComponents model (ScalarDateComponent model))
  | typeValidity (operation : CustomFieldValidityOp)
      (source : CheckedCustomFieldValidityOperand model) (name : String)
  | indexedTypeValidity (operation : CustomFieldValidityOp)
      (source : CheckedIndexedCustomFieldValidityOperand model) (name : String)
  | stringExpression (source : CheckedStringExpressionComparison model)
  | tokenComparison (source : CheckedTokenComparison model)
  | selectedComparison (source : CheckedFirstFilledComparison model)
  | temporal (source : CheckedScalarTemporalComparison model)
  | fieldComparison (source : CheckedScalarFieldComparison model)
  | dateRangeComparison (source : CheckedDateRangePredicate model)
  | valueList (source : CheckedValueListCondition model)
  | scalarValueList (operator : ValueListMembershipOp) (source : CheckedValueListCondition model)
  | scalarNumberLiterals (operator : ValueListMembershipOp)
      (subject : CheckedNumberEntityField model) (values : List Int)
  | fieldFill (operator : FieldFillQuantifier) (source : CheckedComputationFieldFill model)
  | uniqueness (source : CheckedValuesNotUniqueCondition model)
  | overlap (source : CheckedComputationOverlap model)

namespace CheckedComputationPredicate

def referencesWith (predicate : CheckedComputationPredicate model) (field : FieldId)
    (filterReads : CorrelatedHaving → Bool) : Bool :=
  match predicate with
  | .pattern source => source.source.referencesField field
  | .indexedPattern source => source.selection.referencesField field
  | .dateValidity _ source => source.scalarCore.referencesWith field filterReads
  | .typeValidity _ source _ => source.source == field
  | .indexedTypeValidity _ source _ => source.selection.referencesField field
  | .stringExpression source => source.referencesField field
  | .tokenComparison source => source.referencesField field (fun having _ => filterReads having)
  | .selectedComparison source => source.referencesField field (fun having _ => filterReads having)
  | .temporal source => source.referencesWith field filterReads
  | .fieldComparison source => source.referencesField field
  | .dateRangeComparison source => source.referencesField field
  | .valueList source | .scalarValueList _ source => source.referencesField field (fun having _ => filterReads having)
  | .scalarNumberLiterals _ source _ => source.field.id == field
  | .keyedGroupPresence _ source _ => source.referencesField field
  | .indexedFieldPresence _ source => source.referencesField field
  | .fieldFill _ source => source.referencesField field (fun having _ => filterReads having)
  | .uniqueness source => source.referencesField field (fun having _ => filterReads having)
  | .overlap source => source.referencesField field (fun having _ => filterReads having)

def referencesField (predicate : CheckedComputationPredicate model) (field : FieldId) : Bool :=
  predicate.referencesWith field (·.referencesField field)

private def keyedGroupDependencyCondition (operator : GroupPresenceOperator)
    (source : CheckedKeyedEntityExtent model) (kind : ComputationGroupDependencyKind) : ComputationCondition :=
  .leaf (.groupPresence operator {
    reference := { path := source.groupPath, origin := .path }
    content := model.computationGroupSource source.groupPath
    members := source.declarations.map (·.id), dependencyKind := kind })

def forbidsTarget (predicate : CheckedComputationPredicate model) (target : FieldId) : Bool :=
  match predicate with
  | .keyedGroupPresence operator source kind =>
      source.selection.indexSource.referencesField target ||
        (keyedGroupDependencyCondition operator source kind).forbidsTarget target
  | predicate => predicate.referencesWith target (·.forbidsTarget target)

def requiresProducer (predicate : CheckedComputationPredicate model) (consumer producer : FieldId)
    (protectedGroup : ResolvedGroupReference → Bool) : Bool :=
  match predicate with
  | .keyedGroupPresence operator source kind =>
      source.selection.indexSource.referencesField producer ||
        (keyedGroupDependencyCondition operator source kind).requiresProducer consumer producer protectedGroup
  | predicate => predicate.referencesWith producer (fun having => having.requiresProducer consumer producer protectedGroup)

/-- Conditional protection follows authored group identity even for keyed reads; the kernel's
CalculationOperandsCollector and ConditionalCalculationGroupVisitor classify that same path. -/
def groupReference? : CheckedComputationPredicate model → Option (GroupPresenceOperator × ResolvedGroupReference)
  | .keyedGroupPresence operator source .conditionalPresence => some (operator, { path := source.groupPath, origin := .path })
  | _ => none

def rowBoundBool (predicate : CheckedComputationPredicate model) (scope : List RepeatableLevel) : Bool :=
  match predicate with
  | .pattern source => source.source.declarations.all (·.repeatableScope.isPrefixOf scope)
  | .indexedPattern source => source.bindingScopes.all (·.isPrefixOf scope)
  | .dateValidity _ source => source.scalarBindingScopes.all (·.isPrefixOf scope)
  | .typeValidity _ source _ => source.declaration.repeatableScope.isPrefixOf scope
  | .indexedTypeValidity _ source _ => source.bindingScopes.all (·.isPrefixOf scope)
  | .stringExpression source => source.bindingScopes.all (·.isPrefixOf scope)
  | .tokenComparison source => source.bindingScopes.all (·.isPrefixOf scope)
  | .selectedComparison source => source.bindingScopes.all (·.isPrefixOf scope)
  | .temporal source => (source.left.bindingScopes ++ source.right.bindingScopes).all (·.isPrefixOf scope)
  | .fieldComparison source => source.rowBoundBool scope
  | .dateRangeComparison source => source.rowBoundBool scope
  | .valueList source | .scalarValueList _ source => source.bindingScopes.all (·.isPrefixOf scope)
  | .scalarNumberLiterals _ source _ => source.declaration.repeatableScope.isPrefixOf scope
  | .keyedGroupPresence _ source _ => source.isGroup && source.bindingScopes.all (·.isPrefixOf scope)
  | .indexedFieldPresence _ source => source.bindingScopes.all (·.isPrefixOf scope)
  | .fieldFill _ source => source.rowBoundBool scope
  | .uniqueness source => source.bindingScopes.all (·.isPrefixOf scope)
  | .overlap source => source.rowBoundBool scope

private def addressed (context : ScalarComputationContext) : Except ComputationPredicateError ComputationFillContext :=
  match context.addressed with
  | some addressed => pure addressed
  | none => throw .contextRequired

private def scanCells (consume : State → ValueListCell kind → State ⊕ Result) :
    List (ValueListCell kind) → State → ComputationHavingScanResult State Result
  | [], state => .exhausted state
  | cell :: rest, state => match consume state cell with
      | .inl next => scanCells consume rest next
      | .inr result => .terminated result

private def scanNumber (context : ScalarComputationContext)
    (filterRead : Env → FieldId → CheckedCell)
    (filterStoredText filterNumberText : Env → FieldId → Option String)
    (consume : State → ValueListCell .number → State ⊕ Result)
    (source : CheckedNumberEntityOperand model) (state : State)
    (traversalMode : FilterTraversalMode := .requireSmall) :
    Except ComputationPredicateError (ComputationHavingScanResult State Result) := do
  match source with
  | .selected source =>
      let current ← addressed context
      let side ← (source.sideWith .computation current.document context.row context.read context.storedText
        current.read context.semanticIndexColumnReader).mapError .indexSelection
      pure (scanCells consume side.cells state)
  | .field source => pure (scanCells consume
      (source.resolvedAggregateSideAt .computation { read := context.read }).cells state)
  | .star source =>
      let addressed ← addressed context
      let resolved ← (source.source.path.resolveInCapacity addressed.document context.row).mapError .addressing
      pure (scanCells consume
        (resolved.toResolvedSide (source.checkedValueListCellAt .computation addressed.read)).cells state)
  | .group source =>
      let addressed ← addressed context
      let side ← (source.resolvedSideIn .computation addressed.document context.row addressed.read).mapError .addressing
      pure (scanCells consume side.cells state)
  | .starHaving source =>
      let addressed ← addressed context
      let traversal ← (model.filterTraversal source.source.source.path
        (addressed.document.filterRows.getD addressed.document.instantiatedRows) context.row traversalMode).mapError .addressing
      (source.having.scanComputation (({ read := model.filterRead addressed.document filterRead, storedText := filterStoredText, numberText := filterNumberText, world := context.world } : CorrelationContext).withModelComputationGroups model addressed.document) context.row
        (fun state environment => consume state
          (source.source.checkedValueListCellAt .computation (model.filterRead addressed.document addressed.read) environment))
        traversal.candidates state traversal.occupancy).mapError (fun
          | .calendarUnavailable => .temporalUnavailable
          | .valueFailure => .valueFailure
          | .worldUnavailable => .contextRequired
          | .typeValidityValueFailure => .valueFailure
          | .stringExpressionUnavailable => .addressing (.stringExpressionUnavailable)
          | .storedTextUnavailable fieldId => .addressing (.storedTextUnavailable fieldId)
          | .groupUnavailable path => .addressing (.unsupportedGroupOperand path))

private def scanToken (context : ScalarComputationContext)
    (filterRead : Env → FieldId → CheckedCell)
    (filterStoredText filterNumberText : Env → FieldId → Option String)
    (consume : State → ValueListCell .token → State ⊕ Result)
    (source : CheckedTokenEntityOperand model) (state : State)
    (traversalMode : FilterTraversalMode := .requireSmall) :
    Except ComputationPredicateError (ComputationHavingScanResult State Result) := do
  match source with
  | .selected source => do
      let side ← (source.sideAt .computation context).mapError .indexSelection
      pure (scanCells consume side.cells state)
  | .field source => pure (scanCells consume (source.resolvedSideAt .computation context.read).cells state)
  | .group source =>
      let addressed ← addressed context
      let side ← (source.resolvedSideIn .computation addressed.document context.row addressed.read).mapError .addressing
      pure (scanCells consume side.cells state)
  | .star source =>
      let addressed ← addressed context
      let resolved ← (source.source.path.resolveInCapacity addressed.document context.row).mapError .addressing
      match source.filter with
      | none => pure (scanCells consume
          (resolved.toResolvedSide (source.valueListCellAt .computation addressed.read)).cells state)
      | some having => do
          let traversal ← (model.filterTraversal source.source.path
            (addressed.document.filterRows.getD addressed.document.instantiatedRows) context.row traversalMode).mapError .addressing
          (having.condition.scanComputation (({ read := model.filterRead addressed.document filterRead, storedText := filterStoredText, numberText := filterNumberText, world := context.world } : CorrelationContext).withModelComputationGroups model addressed.document) context.row
          (fun state environment => consume state
            (source.valueListCellAt .computation (model.filterRead addressed.document addressed.read) environment))
            traversal.candidates state traversal.occupancy).mapError (fun
              | .calendarUnavailable => .temporalUnavailable
              | .valueFailure => .valueFailure
              | .worldUnavailable => .contextRequired
              | .typeValidityValueFailure => .valueFailure
              | .stringExpressionUnavailable => .addressing (.stringExpressionUnavailable)
              | .storedTextUnavailable fieldId => .addressing (.storedTextUnavailable fieldId)
              | .groupUnavailable path => .addressing (.unsupportedGroupOperand path))

private def scanOperands
    (scan : operand → State → Except error (ComputationHavingScanResult State Result)) :
    List operand → State → Except error (ComputationHavingScanResult State Result)
  | [], state => pure (.exhausted state)
  | source :: rest, state => do
      match ← scan source state with
      | .exhausted next => scanOperands scan rest next
      | .terminated result => pure (.terminated result)
      | .poison cause => pure (.poison cause)

private def readTokenComparisonOperand (context : ScalarComputationContext)
    (filterRead : Env → FieldId → CheckedCell)
    (filterStoredText filterNumberText : Env → FieldId → Option String)
    (operand : CheckedTokenComparisonOperand model) :
    Except ComputationPredicateError (SimpleComparisonOperand String) := do
  let first (_ : Unit) : ValueListCell .token → Unit ⊕ SimpleComparisonOperand String
    | .empty => .inl ()
    | .present value => .inr (.value value true)
    | .unknown cause => .inr (.unknown cause)
  let operands ← match operand with
    | .literal value => return (if value.isEmpty then .notEvaluated else .value value true)
    | .field source => pure [CheckedTokenEntityOperand.field source]
    | .firstFilled source _ => pure source.operands
  match ← scanOperands (scanToken context filterRead filterStoredText filterNumberText first) operands () with
  | .exhausted _ => pure .notEvaluated
  | .terminated result => pure result
  | .poison cause => pure (.unknown cause)

private def selectedComparisonCells (context : ScalarComputationContext) :
    CheckedFieldFillOperand model → Except ComputationPredicateError (List CellObservation)
  | .field declaration => pure [observeCell .computation (context.read declaration.id)]
  | .indexed source => List.singleton <$>
      (source.observeColumnWith .computation context.semanticIndexColumnReader context.row
        context.read context.storedText).mapError .indexSelection
  | .keyed source => do
      let addressed ← addressed context
      let selected ← (source.selectWith .computation context.semanticIndexColumnReader context.row
        context.read context.storedText).mapError .indexSelection
      (source.observationsWith .computation addressed.document selected addressed.read).mapError .indexSelection
  | .star source => do
      if source.hasHaving then throw .unsupportedSelectedComparisonOperand
      let addressed ← addressed context
      let rows ← (source.source.path.resolveInCapacity addressed.document context.row).mapError .addressing
      pure (rows.environments.map fun row => observeCell .computation (addressed.read row source.source.declaration.id))
  | .group source => do
      let addressed ← addressed context
      let (fields, _) ← (model.groupOperandReads addressed.document context.row
        source.source.boundLevelCount source.declarations (·.repeatableScope)).mapError .addressing
      pure (fields.map fun (field, row) => observeCell .computation (addressed.read row field.id))

private def firstSelectedComparison (context : ScalarComputationContext) :
    List (CheckedFieldFillOperand model) → FirstFilledScanState →
      Except ComputationPredicateError (SimpleComparisonOperand Value)
  | [], _ => pure .notEvaluated
  | operand :: rest, state => do
      let cells ← selectedComparisonCells context operand
      match scanFirstFilledObservations cells (state.enterSelection cells.isEmpty false false) with
      | .inl next => firstSelectedComparison context rest next
      | .inr result => pure result

private def readSelectedComparisonOperand (context : ScalarComputationContext) :
    CheckedFirstFilledComparisonOperand model →
      Except ComputationPredicateError (SimpleComparisonOperand FirstFilledComparisonValue)
  | .boolean value => pure (.value (.boolean value) true)
  | .field declaration _ => pure (projectComparisonObservation model declaration
      (observeCell .computation (context.read declaration.id)))
  | .indexed source _ => do
      let observation ← (source.observeColumnWith .computation context.semanticIndexColumnReader
        context.row context.read context.storedText).mapError .indexSelection
      pure (projectComparisonObservation model source.targetDeclaration observation)
  | .firstFilled source => do
      projectFirstFilledValue model source.first <$> firstSelectedComparison context source.source.operands {}
  | .temporal _ => throw .unsupportedSelectedComparisonOperand

private def temporalIdentity (field : FieldId) (cell : CheckedCell) (stored : Option String) :
    Except ComputationPredicateError (ValueListCell .token) :=
  match observeCell .computation cell with
  | .empty => pure .empty
  | .unknown cause | .poison cause => pure (.unknown cause)
  | .value _ => match stored with
      | some text => pure (.present text)
      | none => throw (.fieldKindMismatch field)

private def scanTemporalSlots
    (read : Slot → Except ComputationPredicateError (ValueListCell .token)) :
    List Slot → List String → Except ComputationPredicateError
      (ComputationHavingScanResult (List String) (Except FormalCause Unit))
  | [], seen => pure (.exhausted seen)
  | slot :: rest, seen => do
      match ValueListCell.duplicateComputationStep (kind := .token) seen (← read slot) with
      | .inl next => scanTemporalSlots read rest next
      | .inr result => pure (.terminated result)

private def scanTemporal (context : ScalarComputationContext)
    (filterRead : Env → FieldId → CheckedCell)
    (filterStoredText filterNumberText : Env → FieldId → Option String)
    (source : CheckedTemporalUniquenessOperand model) (seen : List String)
    (requireSmall : Bool := true) :
    Except ComputationPredicateError
      (ComputationHavingScanResult (List String) (Except FormalCause Unit)) := do
  let direct := fun (declaration : FlatFieldDecl) => temporalIdentity declaration.id
    (context.read declaration.id) (context.storedText declaration.id)
  match source with
  | .selected source _ => do
      let current ← addressed context
      let side ← (source.sideWith (kind := .token) .computation current.document context.row context.read context.storedText
        current.read current.storedText context.semanticIndexColumnReader fun field cell stored =>
          match observeCell .computation cell, stored with
          | .value _, some text => pure (.present text)
          | .value _, none => throw (.checkedDocumentRequired field.path)
          | .empty, _ => pure .empty
          | .unknown cause, _ | .poison cause, _ => pure (.unknown cause)).mapError .indexSelection
      pure (scanCells (ValueListCell.duplicateComputationStep (kind := .token)) side.cells seen)
  | .field source => scanTemporalSlots direct [source.declaration] seen
  | .star path source filter =>
      let contextRead ← addressed context
      let resolved ← (path.path.resolveInCapacity contextRead.document context.row).mapError .addressing
      let read := fun row => temporalIdentity source.declaration.id
        (contextRead.read row source.declaration.id) (contextRead.storedText row source.declaration.id)
      match filter with
      | none => scanTemporalSlots read resolved.environments seen
      | some having => do
          let candidates ← (model.filterEnvironments path.path
            (contextRead.document.filterRows.getD contextRead.document.instantiatedRows) context.row requireSmall).mapError .addressing
          let read := fun row => temporalIdentity source.declaration.id
            (model.filterRead contextRead.document contextRead.read row source.declaration.id) (contextRead.storedText row source.declaration.id)
          having.scanComputationResolving
            (({
              read := fun row field => pure (model.filterRead contextRead.document filterRead row field)
              storedText := filterStoredText
              numberText := filterNumberText
              world := context.world
              stringExpressionUnavailable := .addressing .stringExpressionUnavailable
              unsupportedDateCalendar := .temporalUnavailable
              temporalValueFailure := .valueFailure
              worldUnavailable := .contextRequired
              typeValidityValueFailure := .valueFailure
              storedTextUnavailable := ComputationPredicateError.addressing ∘ StarAddressingError.storedTextUnavailable
              groupUnavailable := ComputationPredicateError.addressing ∘ StarAddressingError.unsupportedGroupOperand
              bindingError := fun error => .addressing error.toStarAddressingError } : ResolvingCorrelationContext ComputationPredicateError).withModelComputationGroups model contextRead.document)
            context.row (fun seen row => ValueListCell.duplicateComputationStep (kind := .token) seen <$> read row)
            candidates seen
  | .group source =>
      scanOperands (fun declaration seen => do
        if declaration.repeatableScope.isEmpty then scanTemporalSlots direct [declaration] seen
        else
          let contextRead ← addressed context
          let rows ← (model.groupOperandEnvironments contextRead.document context.row
            source.source.boundLevelCount declaration.repeatableScope).mapError .addressing
          scanTemporalSlots (fun row => temporalIdentity declaration.id
            (contextRead.read row declaration.id) (contextRead.storedText row declaration.id)) rows seen)
        source.declarations seen

private def uniquenessResult : ComputationHavingScanResult State (Except FormalCause Unit) →
    ComputationConditionResult
  | .exhausted _ => .notTrue
  | .poison cause | .terminated (.error cause) => .poison cause
  | .terminated (.ok ()) => .holds

private def evalUniqueness (source : CheckedValuesNotUniqueCondition model)
    (context : ScalarComputationContext) (filterRead : Env → FieldId → CheckedCell)
    (filterStoredText filterNumberText : Env → FieldId → Option String) :
    Except ComputationPredicateError ComputationConditionResult := do
  match source with
  | .number source =>
      uniquenessResult <$> scanOperands
        (scanNumber context filterRead filterStoredText filterNumberText ValueListCell.duplicateComputationStep
          (traversalMode := .dense)) source.operands []
  | .token source =>
      uniquenessResult <$> scanOperands
        (scanToken context filterRead filterStoredText filterNumberText ValueListCell.duplicateComputationStep
          (traversalMode := .dense)) source.source.operands []
  | .temporal source =>
      uniquenessResult <$> scanOperands
        (scanTemporal context filterRead filterStoredText filterNumberText (requireSmall := false)) source.operands []

private def collectStep (values : List (ValueListAtom kind)) :
    ValueListCell kind → List (ValueListAtom kind) ⊕ FormalCause
  | .empty => .inl values
  | .present value => .inl (value :: values)
  | .unknown cause => .inr cause

private def anyStep (predicate : ValueListAtom kind → Bool) (_ : Unit) :
    ValueListCell kind → Unit ⊕ Except FormalCause Bool
  | .empty => .inl ()
  | .present value => if predicate value then .inr (.ok true) else .inl ()
  | .unknown cause => .inr (.error cause)

private def collectResult : ComputationHavingScanResult (List (ValueListAtom kind)) FormalCause →
    Except FormalCause (List (ValueListAtom kind))
  | .exhausted values => .ok values
  | .terminated cause | .poison cause => .error cause

private def anyResult : ComputationHavingScanResult Unit (Except FormalCause Bool) → Except FormalCause Bool
  | .exhausted _ => .ok false
  | .terminated result => result
  | .poison cause => .error cause

private def evalValueList (operator : ComputationValueListOperator)
    (source : CheckedValueListCondition model) (context : ScalarComputationContext)
    (filterRead : Env → FieldId → CheckedCell)
    (filterStoredText filterNumberText : Env → FieldId → Option String) :
    Except ComputationPredicateError ComputationConditionResult :=
  let traversalMode := match operator with
    | .quantified .atLeastOne => FilterTraversalMode.sparse
    | .quantified .no | .quantified .notAll => .dense
    | .scalar _ => .requireSmall
  match source with
  | .number source => operator.evalUsing
      (fun _ => collectResult <$> scanOperands
        (scanNumber context filterRead filterStoredText filterNumberText collectStep (traversalMode := traversalMode)) source.values.operands [])
      (fun test => anyResult <$> scanOperands
        (scanNumber context filterRead filterStoredText filterNumberText (anyStep test) (traversalMode := traversalMode)) source.fields.operands ())
  | .token source => operator.evalUsing
      (fun _ => collectResult <$> scanOperands
        (scanToken context filterRead filterStoredText filterNumberText collectStep (traversalMode := traversalMode)) source.values.operands [])
      (fun test => anyResult <$> scanOperands
        (scanToken context filterRead filterStoredText filterNumberText (anyStep test) (traversalMode := traversalMode)) source.fields.operands ())
  | .literals source => operator.evalUsing (kind := .token)
      (fun _ => pure (.ok (source.firstValue :: source.restValues)))
      (fun test => anyResult <$> scanOperands
        (scanToken context filterRead filterStoredText filterNumberText (anyStep test) (traversalMode := traversalMode)) source.fields.operands ())

private def evalTypeValidity (operation : CustomFieldValidityOp) (name : String)
    (observation : CellObservation) (world : Option World) :
    Except ComputationPredicateError ComputationConditionResult := do
  match observation.asTypeValidityText with
  | .empty => pure .notTrue
  | .unknown cause | .poison cause => pure (.poison cause)
  | .value stored =>
      if stored.isEmpty then return .notTrue
      let some world := world | throw .contextRequired
      let checked : CheckedCustomFieldValidity := { name, validator? := world.resolveCustomFieldValidator? name }
      match checked.evalComputation operation (.value stored) with
      | .holds => pure .holds
      | .notTrue => pure .notTrue
      | .poison cause => pure (.poison cause)
      | .validatorUnavailable => throw .valueFailure

/-- One phase selector serves typed Number and token streams. A filtered operand is scanned with
its consumer continuation, so a deciding subject avoids the suffix beyond its prefetched successor. -/
def evalChecked (predicate : CheckedComputationPredicate model)
    (context : ScalarComputationContext)
    (filterRead? : Option (Env → FieldId → CheckedCell) := none)
    (indexColumn? : Option SemanticIndexColumnReader := none)
    (filterStoredText? : Option (Env → FieldId → Option String) := none)
    (filterNumberText? : Option (Env → FieldId → Option String) := none) :
    Except ComputationPredicateError ComputationConditionResult :=
  let context := (indexColumn?.map (context.withIndexColumnReader model)).getD context
  let filterRead := filterRead?.getD (fun row field =>
    (context.addressed.map (fun addressed => addressed.read row field)).getD (context.read field))
  let filterStoredText := filterStoredText?.getD (if filterRead?.isSome then
    fun _ _ => none
    else fun row field => context.addressed.bind fun addressed => addressed.storedText row field)
  let filterNumberText := filterNumberText?.getD (if filterRead?.isSome then
    fun _ _ => none
    else fun row field => context.addressed.bind fun addressed => addressed.numberText row field)
  match predicate with
  | .keyedGroupPresence operator source _ => do
      let some column := indexColumn? | throw .contextRequired
      source.computationGroupPresence operator context column |>.mapError .indexSelection
  | .indexedFieldPresence operator source => do
      let some readColumn := indexColumn? | throw .contextRequired
      let observation ← source.observeColumnWith .computation readColumn context.row context.read context.storedText
        |>.mapError .indexSelection
      pure (match operator with
        | .filled => observation.evalComputationFilled
        | .notFilled => observation.evalComputationNotFilled)
  | .pattern source => (source.eval { read := context.read }).mapError .stringExpression
  | .indexedPattern source => do
      let some addressed := context.addressed | throw .contextRequired
      let selected ← source.selection.selectEnvironmentWith .computation context.semanticIndexColumnReader
        context.row context.read context.storedText |>.mapError .indexSelection
      pure (source.evalComputationObservation (match selected with
        | .empty => .empty
        | .unknown cause | .poison cause => .poison cause
        | .value row => observeCell .computation (addressed.read row source.leaf.condition.field.id)))
  | .dateValidity operation source => do
      let observation ← match source.directComponents? with
        | some direct => (direct.evaluateComponentsWith (fun component =>
            component.readWith .computation context.read context.storedText context.world) >>= direct.applyProfileReality)
              |>.mapError (fun | .stringNotConvertible _ _ => .valueFailure | _ => .temporalUnavailable)
        | none => (source.evaluateScalarValidity .computation context).mapError (fun
            | .componentNumberInvalid | .dateTimeLabelUnresolved => .valueFailure
            | .addressing (.addressing (.storedTextUnavailable field)) => .addressing (.storedTextUnavailable field)
            | _ => .temporalUnavailable)
      pure (match observation.validityVerdict operation with
        | .error cause => .poison cause
        | .ok (.fired _) => .holds
        | .ok _ => .notTrue)
  | .typeValidity operation source name =>
      evalTypeValidity operation name (observeCell .computation (context.read source.source))
        context.world
  | .indexedTypeValidity operation source name => do
      let some addressed := context.addressed | throw .contextRequired
      let selected ← source.selection.selectEnvironmentWith .computation context.semanticIndexColumnReader
        context.row context.read context.storedText |>.mapError .indexSelection
      match selected with
      | .empty => pure .notTrue
      | .unknown cause | .poison cause => pure (.poison cause)
      | .value row =>
          evalTypeValidity operation name
            (observeCell .computation (addressed.read row source.operand.source))
            context.world
  | .stringExpression source => (source.evalComputation { read := context.read } context.numberText (some context)).mapError .stringExpression
  | .tokenComparison source =>
      evalComputationComparisonExcept (fun left right => source.operator.holds (left == right))
        (readTokenComparisonOperand context filterRead filterStoredText filterNumberText source.left)
        (fun _ => readTokenComparisonOperand context filterRead filterStoredText filterNumberText source.right)
  | .selectedComparison source =>
      evalComputationComparisonExcept
        (CheckedFirstFilledComparison.holds source.operator)
        (readSelectedComparisonOperand context source.left)
        (fun _ => readSelectedComparisonOperand context source.right)
  | .temporal source => (source.evalComputation { read := context.read, storedText := context.storedText, world := context.world } context.addressed context.row).mapError (fun
      | .dateTimeLabelUnresolved | .componentNumberInvalid => .valueFailure
      | .addressing .worldUnavailable => .contextRequired
      | .addressing (.addressing (.storedTextUnavailable field)) => .addressing (.storedTextUnavailable field)
      | .addressing error => if error.isFilterValueFailure then .valueFailure else .temporalUnavailable
      | .calendarUnavailable | .indexedOperandNotSupported => .temporalUnavailable)
  | .fieldComparison source => (source.evalComputation { read := context.read, storedText := context.storedText, world := context.world }).mapError .fieldKindMismatch
  | .dateRangeComparison source => (source.evalComputation { read := context.read, storedText := context.storedText, world := context.world }).mapError .fieldKindMismatch
  | .fieldFill operator source =>
      source.evalCheckedWith operator context filterRead .fieldFill
        (fun indexed => do
          let some readColumn := indexColumn? | throw .contextRequired
          indexed.observeColumnWith .computation readColumn context.row context.read context.storedText
            |>.mapError .indexSelection)
        (fun keyed => do
          let some readColumn := indexColumn? | throw .contextRequired
          keyed.computationSlotsIn context readColumn |>.mapError .indexSelection)
        (filterStoredText := filterStoredText) (filterNumberText := filterNumberText)
  | .overlap source => (source.evalChecked context filterRead (filterStoredText := filterStoredText) (filterNumberText := filterNumberText)).mapError fun
      | .contextRequired => .contextRequired
      | .addressing error => .addressing error
      | .selection error => .indexSelection error
      | .fieldKindMismatch field => .fieldKindMismatch field
  | .uniqueness source => evalUniqueness source context filterRead filterStoredText filterNumberText
  | .valueList source => evalValueList (.quantified source.quantifier) source context filterRead filterStoredText filterNumberText
  | .scalarValueList operator source => evalValueList (.scalar operator) source context filterRead filterStoredText filterNumberText
  | .scalarNumberLiterals operator source values =>
      (ComputationValueListOperator.scalar operator).evalUsing (kind := .number)
        (fun _ => pure (.ok (values.map Rat.ofInt)))
        (fun test => pure (ValueListCell.anyComputation test
          [source.field.valueListCellAt .computation { read := context.read }]))

end CheckedComputationPredicate

private def scalarEntity (operand : SurfaceTextFieldOperand) : SurfaceFieldEntityOperand :=
  .field operand.reference (match operand.projectionRef with
    | .stored => .stored | .category category => .projected category)

/-- A computation binds the same scalar read gates from its target group. Bracketed members
are checked before the construct's subject kind, including when the subject names a fixed group
(spec/12 §3 and the field-value-read predictions checkpoint). -/
private def scalarRead (model : FlatModel) (declaringGroup targetGroup : GroupPath)
    (bracketed : Bool) (operand : SurfaceTextFieldOperand) : Except ResolveError FlatFieldDecl := do
  let declaration ← model.resolveComputationEntityRead declaringGroup targetGroup operand.reference
  let refusal := match operand.projectionRef with
    | .stored => if bracketed then declaration.fieldValueReadRefusal? else none
    | .category _ => declaration.categoryReadRefusal?
  if let some error := refusal then throw error
  pure declaration

private def scalarMemberReads (model : FlatModel) (declaringGroup targetGroup : GroupPath)
    (subject : SurfaceTextFieldOperand) (members : List SurfaceTextFieldOperand) :
    Except ComputationPredicateElabError Unit :=
  (checkScalarMembershipReads (scalarRead model declaringGroup targetGroup false)
    (scalarRead model declaringGroup targetGroup true) subject members).mapError .read

private def elaborateEntityMembership (model : FlatModel) (declaringGroup targetGroup : GroupPath)
    (source : SurfaceNumberEntityValueListSource) :
    Except ComputationPredicateElabError (CheckedValueListCondition model) :=
  match elaborateNumberEntityValueListSource model declaringGroup source (some targetGroup) with
  | .ok checked => pure (.number checked)
  | .error _ => CheckedValueListCondition.token <$>
      (elaborateTokenEntityValueListSource model declaringGroup
        { quantifier := source.quantifier, fields := source.fields, values := source.values }
        (targetGroup? := some targetGroup)).mapError .token

def FlatModel.elaborateComputationPredicate (model : FlatModel)
    (declaringGroup targetGroup : GroupPath) (surface : SurfaceComputationPredicate)
    (compilePattern : StringPatternCompiler := builtinStringPatternCompiler) :
    Except ComputationPredicateElabError (CheckedComputationPredicate model) := do
  match surface with
  | .keyedGroupPresence operator source => do
      let checked ← elaborateKeyedEntityExtent model declaringGroup source
        (some (model.repeatableScopeForGroupPath targetGroup)) |>.mapError .keyedGroup
      if !checked.isGroup || checked.isStarredGroup then throw .incoherent
      pure (.keyedGroupPresence operator checked .conditionalPresence)
  | .indexedFieldPresence operator source =>
      CheckedComputationPredicate.indexedFieldPresence operator <$>
        (elaborateSemanticIndexSource model declaringGroup source
          (some (model.repeatableScopeForGroupPath targetGroup))).mapError .semanticIndex
  | .pattern source => CheckedComputationPredicate.pattern <$>
      (elaborateComputationStringPattern compilePattern model declaringGroup targetGroup source).mapError .pattern
  | .indexedPattern source => CheckedComputationPredicate.indexedPattern <$>
      (elaborateIndexedStringPattern compilePattern model declaringGroup source
        (some (model.repeatableScopeForGroupPath targetGroup))).mapError .indexedPattern
  | .dateValidity operation source => do
      let checked ← (elaborateScalarDateValidityComponents model declaringGroup source targetGroup).mapError .temporal
      pure (.dateValidity operation checked)
  | .typeValidity operation path name => do
      let declaration ← (model.resolveComputationFieldValueRead declaringGroup targetGroup path).mapError .read
      let source ← (elaborateCustomFieldValidityOperand model declaration.id).mapError .typeOperand
      if name.isEmpty then throw (.typeName .emptyTypeName)
      pure (.typeValidity operation source name)
  | .indexedTypeValidity operation authored name => do
      let source ← (elaborateIndexedCustomFieldValidityOperand model declaringGroup authored
        (some (model.repeatableScopeForGroupPath targetGroup))).mapError .indexedTypeOperand
      if name.isEmpty then throw (.typeName .emptyTypeName)
      pure (.indexedTypeValidity operation source name)
  | .uniqueness source =>
      match elaborateNumberValuesNotUniqueSource model declaringGroup source targetGroup (some targetGroup) with
      | .ok source => pure (.uniqueness (.number source))
      | .error numberError =>
          match elaborateTokenValuesNotUniqueSource model declaringGroup source targetGroup (some targetGroup) with
          | .ok source => pure (.uniqueness (.token source))
          | .error tokenError =>
              match elaborateTemporalValuesNotUniqueSource model declaringGroup source targetGroup (some targetGroup) with
              | .ok source => pure (.uniqueness (.temporal source))
              | .error temporalError => throw (.uniqueness numberError tokenError temporalError)
  | .fieldFill operator source =>
      .fieldFill operator <$> (CheckedComputationFieldFill.elaborate model declaringGroup targetGroup source).mapError .fieldFill
  | .overlap source =>
      let scope := model.repeatableScopeForGroupPath targetGroup
      match elaborateDateRangesOverlapSourceIn model declaringGroup scope source targetGroup (some targetGroup) with
      | .ok source => pure (.overlap (.anyPair source))
      | .error exactError =>
          match elaborateYearlessDateRangesOverlapSourceIn model declaringGroup scope source targetGroup (some targetGroup) with
          | .ok source => pure (.overlap (.yearlessAnyPair source))
          | .error _ => throw (.overlap (.overlap exactError))
  | .scalarOverlap source =>
      let scope := model.repeatableScopeForGroupPath targetGroup
      match elaborateAtLeastOneDateRangeOverlapsSourceIn model declaringGroup scope source targetGroup (some targetGroup) with
      | .ok source => pure (.overlap (.scalar source))
      | .error exactError =>
          match elaborateYearlessAtLeastOneDateRangeOverlapsSourceIn model declaringGroup scope source targetGroup (some targetGroup) with
          | .ok source => pure (.overlap (.yearlessScalar source))
          | .error _ => throw (.overlap (.pluralOverlap exactError))
  | .tokenComparison op left right => .tokenComparison <$>
      (elaborateTokenComparison model declaringGroup op left right targetGroup).mapError .tokenComparison
  | .selectedComparison op left right => do
      let checked ← (elaborateFirstFilledComparison model declaringGroup targetGroup
        (if op == .equal then .equal else .notEqual) left right).mapError .selectedComparison
      if checked.hasHaving || [checked.left.profile, checked.right.profile].any
          (fun | .temporal _ _ => true | _ => false) then throw .incoherent
      pure (.selectedComparison checked)
  | .selectedStringExpression op left right => .stringExpression <$>
      (elaborateSelectedStringExpressionComparison model declaringGroup targetGroup op left right).mapError .stringExpression
  | .stringExpression op left right => .stringExpression <$>
      (elaborateStringExpressionComparison model declaringGroup targetGroup op left right).mapError .stringExpression
  | .temporal op left right => .temporal <$>
      (elaborateScalarTemporalComparison model declaringGroup op left right (some targetGroup)).mapError .temporal
  | .fieldComparison op left right => .fieldComparison <$>
      (elaborateScalarFieldComparison model declaringGroup targetGroup op left right).mapError .comparison
  | .dateRangeComparison operator source => .dateRangeComparison <$>
      (elaborateDateRangePredicate model (model.repeatableScopeForGroupPath targetGroup)
        (model.resolveComputationOperandUnchecked declaringGroup targetGroup)
        (model.resolveComputationFieldValueRead declaringGroup targetGroup) operator source).mapError .dateRangeComparison
  | .entityValueList source => .valueList <$> elaborateEntityMembership model declaringGroup targetGroup source
  | .tokenLiteralValueList source =>
      (.valueList ∘ .literals) <$>
        (elaborateTokenEntityStringLiteralValueListSource model declaringGroup source
          (targetGroup? := some targetGroup)).mapError .literals
  | .scalarMembership operator subject members =>
      let fields : SurfaceFieldEntitySource := { first := scalarEntity subject, rest := [] }
      match members with
      | .fields members =>
          scalarMemberReads model declaringGroup targetGroup subject members
          let first :: rest := members | throw .emptyMembers
          .scalarValueList operator <$> elaborateEntityMembership model declaringGroup targetGroup {
            quantifier := operator.quantifier, fields
            values := { first := scalarEntity first, rest := rest.map scalarEntity } }
      | .tokens values =>
          discard <| (scalarRead model declaringGroup targetGroup false subject).mapError .read
          (.scalarValueList operator ∘ .literals) <$>
            (elaborateTokenEntityStringLiteralValueListSource model declaringGroup
              { quantifier := operator.quantifier, fields, values }
              (targetGroup? := some targetGroup)).mapError .literals
      | .numbers values =>
          discard <| (scalarRead model declaringGroup targetGroup false subject).mapError .read
          let source ← (elaborateNumberEntitySource model declaringGroup fields
            (fixedTargetGroup? := some targetGroup) (writtenGroup := targetGroup)
            (arity := .soleAllowed) (bindingGroup? := some targetGroup)).mapError .number
          if values.isEmpty then throw .emptyMembers
          match source.operands with
          | [.field field] => pure (.scalarNumberLiterals operator field values)
          | _ => throw .incoherent

end A12Kernel
