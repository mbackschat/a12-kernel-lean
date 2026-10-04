import A12Kernel.Elaboration.StringExpression
import A12Kernel.Elaboration.ValueListCondition
import A12Kernel.Elaboration.NumericAggregate.Entities
import A12Kernel.Semantics.ComputationValueList
import A12Kernel.Elaboration.ScalarFieldComparison
import A12Kernel.Elaboration.TemporalExpression
import A12Kernel.Elaboration.ComputationOverlap
import A12Kernel.Elaboration.ComputationFieldFill
import A12Kernel.Elaboration.ValuesNotUniqueCondition
import A12Kernel.Elaboration.CustomFieldValidity

namespace A12Kernel

inductive SurfaceScalarMembershipMembers where
  | fields (members : List SurfaceTextFieldOperand)
  | numbers (members : List Int)
  | tokens (members : List String)
  deriving Repr, DecidableEq

inductive SurfaceComputationPredicate where
  | dateValidity (operation : ConstructedDateValidityOp) (source : SurfaceConstructedDateComponents)
  | typeValidity (operation : CustomFieldValidityOp) (source : SurfaceFieldPath) (name : String)
  | stringExpression (operator : EqualityOp) (left right : StringExpr SurfaceFieldPath)
  | temporal (operator : TemporalComparisonOp) (left right : SurfaceScalarTemporalExpression)
  | fieldComparison (operator : SurfaceComparisonOp) (left right : SurfaceFieldPath)
  | scalarMembership (operator : ValueListMembershipOp) (subject : SurfaceTextFieldOperand)
      (members : SurfaceScalarMembershipMembers)
  | entityValueList (source : SurfaceNumberEntityValueListSource)
  | tokenLiteralValueList (source : SurfaceTokenEntityStringLiteralValueListSource)
  | fieldFill (operator : FieldFillQuantifier) (source : SurfaceFieldEntitySource)
  | uniqueness (source : SurfaceFieldEntitySource)
  | overlap (source : SurfaceFieldEntitySource)
  | scalarOverlap (source : SurfaceAtLeastOneDateRangeOverlapsSource)

inductive ComputationPredicateElabError where
  | typeOperand (error : CustomFieldValidityOperandElabError)
  | typeName (error : CustomFieldValidityElabError)
  | stringExpression (error : StringComputationElabError)
  | temporal (error : ScalarTemporalExpressionError)
  | comparison (error : ScalarFieldComparisonElabError)
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

inductive ComputationPredicateError where
  | stringExpression (error : StringComputationFault)
  /-- Runtime failure at a reached guard becomes the target's calculation-value error, separately
  from inherited operand poison (comparison-guard grid, 2026-10-04). -/
  | valueFailure
  | temporalUnavailable
  | fieldFill (error : ComputationFillError)
  | fieldKindMismatch (field : FieldId)
  | contextRequired
  | addressing (error : StarAddressingError)
  deriving Repr, DecidableEq

/-- Retain typed source certificates and authored filters; computation traversal keeps reached
errors distinct from validation's unknown verdict. -/
inductive CheckedComputationPredicate (model : FlatModel) where
  | dateValidity (operation : ConstructedDateValidityOp) (source : CheckedConstructedDateComponents model)
  | typeValidity (operation : CustomFieldValidityOp)
      (source : CheckedCustomFieldValidityOperand model) (name : String)
  | stringExpression (source : CheckedStringExpressionComparison model)
  | temporal (source : CheckedScalarTemporalComparison model)
  | fieldComparison (source : CheckedScalarFieldComparison model)
  | valueList (source : CheckedValueListCondition model)
  | scalarValueList (operator : ValueListMembershipOp) (source : CheckedValueListCondition model)
  | scalarNumberLiterals (operator : ValueListMembershipOp)
      (subject : CheckedNumberEntityField model) (values : List Int)
  | fieldFill (operator : FieldFillQuantifier) (source : CheckedComputationFieldFill model)
  | uniqueness (source : CheckedValuesNotUniqueCondition model)
  | overlap (source : CheckedComputationOverlap model)

namespace CheckedComputationPredicate

def referencesField (predicate : CheckedComputationPredicate model) (field : FieldId) : Bool :=
  match predicate with
  | .dateValidity _ source => source.fields.contains field
  | .typeValidity _ source _ => source.source == field
  | .stringExpression source => source.referencesField field
  | .temporal source => source.referencesField field
  | .fieldComparison source => source.referencesField field
  | .valueList source | .scalarValueList _ source => source.referencesField field
  | .scalarNumberLiterals _ source _ => source.field.id == field
  | .fieldFill _ source => source.referencesField field
  | .uniqueness source => source.referencesField field
  | .overlap source => source.referencesField field

def rowBoundBool (predicate : CheckedComputationPredicate model) (scope : List RepeatableLevel) : Bool :=
  match predicate with
  | .dateValidity _ source => source.fields.all (fun field => (model.fieldRepeatableScope field).isPrefixOf scope)
  | .typeValidity _ source _ => source.declaration.repeatableScope.isPrefixOf scope
  | .stringExpression source => source.declarations.all (·.repeatableScope.isPrefixOf scope)
  | .temporal source => (source.left.bindingScopes ++ source.right.bindingScopes).all (·.isPrefixOf scope)
  | .fieldComparison source => source.rowBoundBool scope
  | .valueList source | .scalarValueList _ source => source.bindingScopes.all (·.isPrefixOf scope)
  | .scalarNumberLiterals _ source _ => source.declaration.repeatableScope.isPrefixOf scope
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
    (consume : State → ValueListCell .number → State ⊕ Result)
    (source : CheckedNumberEntityOperand model) (state : State) :
    Except ComputationPredicateError (ComputationHavingScanResult State Result) := do
  match source with
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
      let resolved ← (source.source.source.path.resolveInCapacity addressed.document context.row).mapError .addressing
      pure (source.having.scanComputation { read := filterRead } context.row
        (fun state environment => consume state
          (source.source.checkedValueListCellAt .computation addressed.read environment))
        resolved.environments state)

private def scanToken (context : ScalarComputationContext)
    (filterRead : Env → FieldId → CheckedCell)
    (consume : State → ValueListCell .token → State ⊕ Result)
    (source : CheckedTokenEntityOperand model) (state : State) :
    Except ComputationPredicateError (ComputationHavingScanResult State Result) := do
  match source with
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
      | some having => pure (having.condition.scanComputation { read := filterRead } context.row
          (fun state environment => consume state
            (source.valueListCellAt .computation addressed.read environment)) resolved.environments state)

private def scanOperands
    (scan : operand → State → Except error (ComputationHavingScanResult State Result)) :
    List operand → State → Except error (ComputationHavingScanResult State Result)
  | [], state => pure (.exhausted state)
  | source :: rest, state => do
      match ← scan source state with
      | .exhausted next => scanOperands scan rest next
      | .terminated result => pure (.terminated result)
      | .poison cause => pure (.poison cause)

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
    (source : CheckedTemporalUniquenessOperand model) (seen : List String) :
    Except ComputationPredicateError
      (ComputationHavingScanResult (List String) (Except FormalCause Unit)) := do
  let direct := fun (declaration : FlatFieldDecl) => temporalIdentity declaration.id
    (context.read declaration.id) (context.storedText declaration.id)
  match source with
  | .field source => scanTemporalSlots direct [source.declaration] seen
  | .star path source filter =>
      let contextRead ← addressed context
      let resolved ← (path.path.resolveInCapacity contextRead.document context.row).mapError .addressing
      let read := fun row => temporalIdentity source.declaration.id
        (contextRead.read row source.declaration.id) (contextRead.storedText row source.declaration.id)
      match filter with
      | none => scanTemporalSlots read resolved.environments seen
      | some having =>
          having.scanComputationResolving
            { read := fun row field => pure (filterRead row field)
              bindingError := fun error => .addressing error.toStarAddressingError }
            context.row (fun seen row => ValueListCell.duplicateComputationStep (kind := .token) seen <$> read row)
            resolved.environments seen
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
    (context : ScalarComputationContext) (filterRead : Env → FieldId → CheckedCell) :
    Except ComputationPredicateError ComputationConditionResult := do
  match source with
  | .number source =>
      uniquenessResult <$> scanOperands
        (scanNumber context filterRead ValueListCell.duplicateComputationStep) source.operands []
  | .token source =>
      uniquenessResult <$> scanOperands
        (scanToken context filterRead ValueListCell.duplicateComputationStep) source.source.operands []
  | .temporal source =>
      uniquenessResult <$> scanOperands
        (scanTemporal context filterRead) source.operands []

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
    (filterRead : Env → FieldId → CheckedCell) :
    Except ComputationPredicateError ComputationConditionResult :=
  match source with
  | .number source => operator.evalUsing
      (fun _ => collectResult <$> scanOperands (scanNumber context filterRead collectStep) source.values.operands [])
      (fun test => anyResult <$> scanOperands (scanNumber context filterRead (anyStep test)) source.fields.operands ())
  | .token source => operator.evalUsing
      (fun _ => collectResult <$> scanOperands (scanToken context filterRead collectStep) source.values.operands [])
      (fun test => anyResult <$> scanOperands (scanToken context filterRead (anyStep test)) source.fields.operands ())
  | .literals source => operator.evalUsing (kind := .token)
      (fun _ => pure (.ok (source.firstValue :: source.restValues)))
      (fun test => anyResult <$> scanOperands (scanToken context filterRead (anyStep test)) source.fields.operands ())

/-- One phase selector serves typed Number and token streams. A filtered operand is scanned with
its consumer continuation, so a deciding subject avoids the suffix beyond its prefetched successor. -/
def evalChecked (predicate : CheckedComputationPredicate model)
    (context : ScalarComputationContext)
    (filterRead? : Option (Env → FieldId → CheckedCell) := none) :
    Except ComputationPredicateError ComputationConditionResult :=
  let filterRead := filterRead?.getD (fun row field =>
    (context.addressed.map (fun addressed => addressed.read row field)).getD (context.read field))
  match predicate with
  | .dateValidity operation source => do
      let observation ← (source.evaluateComponentsWith (fun component =>
        component.readWith .computation context.read context.storedText context.world) >>= source.applyProfileReality)
          |>.mapError (fun _ => .temporalUnavailable)
      pure (match observation.validityVerdict operation with
        | .error cause => .poison cause
        | .ok (.fired _) => .holds
        | .ok _ => .notTrue)
  | .typeValidity operation source name => do
      let observation := observeCell .computation (context.read source.source)
      match observation with
      | .empty => pure .notTrue
      | .unknown cause | .poison cause => pure (.poison cause)
      | .value _ =>
          let some stored := context.storedText source.source | throw .contextRequired
          if stored.isEmpty then return .notTrue
          let some world := context.world | throw .contextRequired
          let checked : CheckedCustomFieldValidity := { name, validator? := world.resolveCustomFieldValidator? name }
          match checked.evalComputation operation (.value stored) with
          | .holds => pure .holds
          | .notTrue => pure .notTrue
          | .poison cause => pure (.poison cause)
          | .validatorUnavailable => throw .valueFailure
  | .stringExpression source => (source.evalComputation { read := context.read } context.numberText).mapError .stringExpression
  | .temporal source => (source.evalComputation { read := context.read, storedText := context.storedText, world := context.world } context.addressed context.row).mapError (fun
      | .dateTimeLabelUnresolved => .valueFailure
      | .calendarUnavailable => .temporalUnavailable)
  | .fieldComparison source => (source.evalComputation { read := context.read, storedText := context.storedText, world := context.world }).mapError .fieldKindMismatch
  | .fieldFill operator source => (source.evalChecked operator context filterRead).mapError .fieldFill
  | .overlap source => (source.evalChecked context filterRead).mapError fun
      | .contextRequired => .contextRequired
      | .addressing error => .addressing error
      | .fieldKindMismatch field => .fieldKindMismatch field
  | .uniqueness source => evalUniqueness source context filterRead
  | .valueList source => evalValueList (.quantified source.quantifier) source context filterRead
  | .scalarValueList operator source => evalValueList (.scalar operator) source context filterRead
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
    (declaringGroup targetGroup : GroupPath) (surface : SurfaceComputationPredicate) :
    Except ComputationPredicateElabError (CheckedComputationPredicate model) := do
  match surface with
  | .dateValidity operation source => do
      let checked ← (elaborateConstructedDateSources model source
        (model.repeatableScopeForGroupPath targetGroup)).mapError (fun error => .temporal (.dateComponents error))
      if checked.fields.isEmpty then throw .incoherent
      pure (.dateValidity operation checked)
  | .typeValidity operation path name => do
      let declaration ← (model.resolveComputationFieldValueRead declaringGroup targetGroup path).mapError .read
      let source ← (elaborateCustomFieldValidityOperand model declaration.id).mapError .typeOperand
      if name.isEmpty then throw (.typeName .emptyTypeName)
      pure (.typeValidity operation source name)
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
  | .stringExpression op left right => .stringExpression <$>
      (elaborateStringExpressionComparison model declaringGroup targetGroup op left right).mapError .stringExpression
  | .temporal op left right => .temporal <$>
      (elaborateScalarTemporalComparison model declaringGroup op left right (some targetGroup)).mapError .temporal
  | .fieldComparison op left right => .fieldComparison <$>
      (elaborateScalarFieldComparison model declaringGroup targetGroup op left right).mapError .comparison
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
