import A12Kernel.Elaboration.DeclaredPartialFields
import A12Kernel.Elaboration.FieldFillList
import A12Kernel.Elaboration.TemporalExpression
import A12Kernel.Semantics.DateRangeComparison

/-! # Typed first-filled validation comparisons

Selection retains its declaration profile, missing prefix and formal cause through comparison.
The entity-list gates precede the whole-list Confirm gate and exact source-format agreement;
comparison compatibility then uses the existing Boolean, temporal and DateRange owners.
-/

namespace A12Kernel

inductive FirstFilledComparisonProfile where
  | boolean
  | confirm
  | temporal (format : String) (components : TemporalComponents)
  | dateRange (format : DateRangeInputFormat)
  deriving Repr, DecidableEq

private def firstFilledProfile? (declaration : FlatFieldDecl) : Option FirstFilledComparisonProfile :=
  match declaration.policy.kind with
  | .boolean => some .boolean
  | .confirm => some .confirm
  | .temporal _ components => do
      let policy ← declaration.toTemporalTargetPolicy?
      if policy.partialMode != .full then none else pure (.temporal policy.format components)
  | .dateRange => do
      let policy ← declaration.toDateRangeDeclarationPolicy?
      .dateRange <$> DateRangeInputFormat.ofPolicy? policy
  | _ => none

inductive SurfaceFirstFilledComparisonOperand where
  | firstFilled (source : SurfaceFieldEntitySource)
  | field (reference : SurfaceFieldPath)
  | indexed (source : SurfaceSemanticIndex)
  | boolean (value : Bool)
  | temporal (expression : SurfaceScalarTemporalExpression)

inductive FirstFilledComparisonElabError where
  | model (cause : ResolveError)
  | shape (cause : FieldEntityShapeElabError)
  | source (cause : FieldFillListElabError)
  | temporal (cause : ScalarTemporalExpressionError)
  | semanticIndex (cause : SemanticIndexElabError)
  | admission (diagnostic : KernelStaticDiagnostic)
  | unsupportedSource
  | confirmOperand (path : List String)
  | varyingProfiles
  | incompatibleComparison
  | noSelection
  deriving Repr, DecidableEq

def FirstFilledComparisonElabError.diagnostic? : FirstFilledComparisonElabError → Option KernelStaticDiagnostic
  | .shape cause => cause.diagnostic?
  | .admission diagnostic => some diagnostic
  | .confirmOperand _ => some .noBoolyAllowed
  | .varyingProfiles => some .varyingTypesNotAllowed
  | _ => none

structure CheckedTypedFirstFilledSource (model : FlatModel) where
  private mk ::
  source : CheckedFieldFillList model
  first : FlatFieldDecl
  profile : FirstFilledComparisonProfile

inductive CheckedFirstFilledComparisonOperand (model : FlatModel) where
  | firstFilled (source : CheckedTypedFirstFilledSource model)
  | field (declaration : FlatFieldDecl) (profile : FirstFilledComparisonProfile)
  | indexed (source : CheckedSemanticIndexSource model) (profile : FirstFilledComparisonProfile)
  | boolean (value : Bool)
  | temporal (expression : CheckedScalarTemporalExpression model)

namespace CheckedFirstFilledComparisonOperand

def profile : CheckedFirstFilledComparisonOperand model → FirstFilledComparisonProfile
  | .firstFilled source => source.profile
  | .field _ profile => profile
  | .indexed _ profile => profile
  | .boolean _ => .boolean
  | .temporal expression => .temporal "" expression.components

def fieldIds : CheckedFirstFilledComparisonOperand model → List FieldId
  | .firstFilled source => source.source.declarations.map (·.id)
  | .field declaration _ => [declaration.id]
  | .indexed source _ => [source.targetDeclaration.id, source.indexDeclaration.id] ++
      (match source.key with | .field declaration => [declaration.id] | .literal _ _ => [])
  | .boolean _ => []
  | .temporal expression => expression.fieldIds

def hasHaving : CheckedFirstFilledComparisonOperand model → Bool
  | .firstFilled source => source.source.hasHaving
  | .temporal expression => expression.core.hasHaving
  | _ => false

def referencesField (operand : CheckedFirstFilledComparisonOperand model) (field : FieldId)
    (filterReads : CorrelatedHaving → FieldId → Bool) : Bool :=
  match operand with
  | .firstFilled source => source.source.operands.any (·.referencesField field filterReads)
  | .indexed source _ => source.referencesField field
  | .temporal expression => expression.referencesWith field (fun having => filterReads having field)
  | _ => operand.fieldIds.contains field

def bindingScopes : CheckedFirstFilledComparisonOperand model → List (List RepeatableLevel)
  | .firstFilled source => source.source.operands.flatMap (·.bindingScopes)
  | .field declaration _ => [declaration.repeatableScope]
  | .indexed source _ => source.bindingScopes
  | .boolean _ => []
  | .temporal expression => expression.bindingScopes

end CheckedFirstFilledComparisonOperand

structure CheckedFirstFilledComparison (model : FlatModel) where
  private mk ::
  left : CheckedFirstFilledComparisonOperand model
  right : CheckedFirstFilledComparisonOperand model
  operator : TemporalComparisonOp
  modelWellFormed : model.validate.isOk = true

private def checkFirstFilledComparisonOperand (model : FlatModel) (declaringGroup bindingGroup : GroupPath) :
    SurfaceFirstFilledComparisonOperand → Except FirstFilledComparisonElabError (CheckedFirstFilledComparisonOperand model)
  | .boolean value => pure (.boolean value)
  | .field reference => do
      let declaration ← (model.resolveFieldDeclarationUnchecked declaringGroup reference).mapError .model
      let some profile := firstFilledProfile? declaration | throw .unsupportedSource
      pure (.field declaration profile)
  | .indexed source => do
      let source ← (elaborateSemanticIndexSource model declaringGroup source
        (some (model.repeatableScopeForGroupPath bindingGroup))).mapError .semanticIndex
      let some profile := firstFilledProfile? source.targetDeclaration | throw .unsupportedSource
      if let .temporal _ _ := profile then throw .unsupportedSource
      pure (.indexed source profile)
  | .temporal expression => do
      let checked ← (elaborateScalarTemporalExpression model declaringGroup expression (some bindingGroup)).mapError .temporal
      pure (.temporal checked)
  | .firstFilled authored => do
      let _ ← (elaborateFieldEntityShapeIn model declaringGroup
        (model.repeatableScopeForGroupPath bindingGroup) authored
        (writtenGroup := bindingGroup) (groupReadScope := .ruleBound)).mapError .shape
      let source ← (elaborateFieldFillList model declaringGroup authored bindingGroup).mapError .source
      if let some declaration := source.declarations.find? (·.policy.kind.surfaceKind == .confirm) then
        throw (.confirmOperand declaration.path)
      let first :: _ := source.declarations | throw .unsupportedSource
      let some profile := firstFilledProfile? first | throw .unsupportedSource
      for declaration in source.declarations do
        let some candidate := firstFilledProfile? declaration | throw .unsupportedSource
        if candidate != profile then throw .varyingProfiles
      pure (.firstFilled { source, first, profile })

def elaborateFirstFilledComparison (model : FlatModel) (declaringGroup bindingGroup : GroupPath)
    (operator : TemporalComparisonOp) (left right : SurfaceFirstFilledComparisonOperand) :
    Except FirstFilledComparisonElabError (CheckedFirstFilledComparison model) := do
  match h : model.validate with
  | .error error => throw (.model error)
  | .ok () =>
      let left ← checkFirstFilledComparisonOperand model declaringGroup bindingGroup left
      let right ← checkFirstFilledComparisonOperand model declaringGroup bindingGroup right
      if !(match left, right with
          | .firstFilled _, _ | _, .firstFilled _ | .indexed _ _, _ | _, .indexed _ _ => true
          | _, _ => false) then
        throw .noSelection
      let equality := operator == .equal || operator == .notEqual
      if !equality && (left.profile == .boolean || left.profile == .confirm ||
          right.profile == .boolean || right.profile == .confirm) then
        throw (.admission .invalidTypeForComparison)
      if left.profile == .confirm || right.profile == .confirm then
        let admitted := match left, right with
          | .boolean true, other | other, .boolean true => other.profile == .confirm
          | left, right => left.profile == .confirm && right.profile == .confirm && operator == .notEqual
        if !admitted then throw (.admission .invalidCompareToYes)
      let compatible := match left.profile, right.profile with
        | .boolean, .boolean => equality
        | .confirm, .boolean | .boolean, .confirm | .confirm, .confirm => equality
        | .dateRange a, .dateRange b => equality && a.components == b.components
        | .temporal _ a, .temporal _ b => operator.admitsFormats model.hasBaseYear a b
        | _, _ => false
      if !compatible then throw .incompatibleComparison
      for profile in [left.profile, right.profile] do
        if let .temporal _ components := profile then
          let components := if components.hasDate then components.withBaseYear model.hasBaseYear else components
          if components.hasTime && components != TemporalComponents.now && components != TemporalComponents.time then
            throw .unsupportedSource
      pure { left, right, operator, modelWellFormed := by rw [h]; rfl }

private def scanTypedFirstFilled (document : CheckedDocument model) (outer : Env)
    (world : Option World := none) :
    List (CheckedFieldFillOperand model) → FirstFilledScanState →
      Except CheckedAddressingError (SimpleComparisonOperand Value)
  | [], _ => pure .notEvaluated
  | operand :: rest, state => do
      let ordinary (_ : Unit) := do
        let cells ← operand.observations (world := world) (traversalMode := .dense) document outer
        pure (scanFirstFilledObservations cells (state.enterSelection cells.isEmpty false operand.hasHaving))
      let scanned ← match operand with
        | .star source => match source.filter with
          | some having =>
              source.source.scanValidationCells having.condition document outer
                (fun state cell => scanFirstFilledObservations [observeCell .validation cell.cell] state)
                (state.enter false true) .dense world
          | none => do
              let resolved ← source.source.resolveCheckedValidationEntityOperandCore document outer none
              let cells := resolved.inCapacityAddressedCells.map fun cell => observeCell .validation cell.cell
              let emptyPrefix := cells.isEmpty || resolved.topology.any (·.domain.hasEmptyPrefix)
              pure (scanFirstFilledObservations cells (state.enterSelection emptyPrefix false false))
        | _ => ordinary ()
      match scanned with
      | .inl next => scanTypedFirstFilled (world := world) document outer rest next
      | .inr result => pure result

inductive FirstFilledComparisonValue where
  | boolean (value : Bool)
  | temporal (value : ScalarTemporalValue)
  | dateRange (value : DateRangeCellValue)

private def mapFirstFilledOperand (wrap : α → β) : SimpleComparisonOperand α → SimpleComparisonOperand β
  | .notEvaluated => .notEvaluated
  | .unknown cause => .unknown cause
  | .value value given => .value (wrap value) given

/-- Preserve first-filled omission provenance while projecting the admitted typed value. -/
def projectFirstFilledValue (model : FlatModel) (declaration : FlatFieldDecl) :
    SimpleComparisonOperand Value → SimpleComparisonOperand FirstFilledComparisonValue
  | .notEvaluated => .notEvaluated
  | .unknown cause => .unknown cause
  | .value (.bool value) given => .value (.boolean value) given
  | .value (.conf true) given => .value (.boolean true) given
  | .value (.dateRange value) given => .value (.dateRange value) given
  | .value value given =>
      match declaration.toTemporalField? with
      | none => .unknown .malformed
      | some field =>
          match projectScalarTemporalObservation model field (.value value) with
          | .value value _ => .value (.temporal value) given
          | .notEvaluated => .notEvaluated
          | .unknown cause => .unknown cause

/-- Direct Confirm absence substitutes false; other typed absence suppresses comparison (spec/02 §A.3). -/
def projectComparisonObservation (model : FlatModel) (declaration : FlatFieldDecl)
    (observation : CellObservation) : SimpleComparisonOperand FirstFilledComparisonValue :=
  match declaration.policy.kind with
  | .boolean | .confirm => mapFirstFilledOperand .boolean
      (observation.asBooleanComparisonOperand (declaration.policy.kind == .confirm))
  | _ => projectFirstFilledValue model declaration observation.asValidationSimpleOperand

private def CheckedFirstFilledComparisonOperand.evaluate
    (document : CheckedDocument model) (outer : Env) (context : FlatContext) :
    CheckedFirstFilledComparisonOperand model →
      Except (Sum CheckedAddressingError ScalarTemporalEvaluationFault) (SimpleComparisonOperand FirstFilledComparisonValue)
  | .boolean value => pure (.value (.boolean value) true)
  | .temporal expression => do
      let cells ← expression.boundFieldIds.mapM fun field => do
        let cell ← (document.fullValidationAddressedCell outer field).mapError Sum.inl
        pure (field, cell.cell)
      let context := { context with
        read := fun field => ((cells.find? (·.1 == field)).map (·.2)).getD malformedCheckedCell
        storedText := document.storedTextIn outer }
      mapFirstFilledOperand .temporal <$> (expression.evalResult .validation context
        (some document.indexedComputationFillContext) outer).mapError ScalarTemporalEvaluationFault.separateAddressing
  | .field declaration _ => do
      let addressed ← (document.fullValidationAddressedCell outer declaration.id).mapError Sum.inl
      pure (projectComparisonObservation model declaration (observeCell .validation addressed.cell))
  | .indexed source _ => do
      let observation ← (source.observeDocument document outer .validation).mapError Sum.inl
      pure (projectComparisonObservation model source.targetDeclaration observation)
  | .firstFilled source => do
      let result ← (scanTypedFirstFilled (world := context.world) document outer source.source.operands {}).mapError Sum.inl
      pure (projectFirstFilledValue model source.first result)

private def partialFirstFilledFields? (outer : Env) :
    CheckedFieldFillOperand model → Except CheckedAddressingError (Option DeclaredPartialFields)
  | .field declaration => pure (some { addresses := [(declaration, outer)] })
  | .star source => declaredPartialFields? model [source.source.declaration]
      source.source.path.firstStar outer
  | .group source => declaredPartialFields? model source.declarations
      source.source.boundLevelCount outer
  | .indexed _ | .keyed _ => throw .unsupportedIndexedFillQuantifier

private def scanPartialFirstFilledCells {model : FlatModel} (scope : ValidationRelevanceScope)
    (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell))
    (fields : DeclaredPartialFields) :
    List (FlatFieldDecl × Env) → FirstFilledScanState →
      Except CheckedAddressingError (FirstFilledScanState ⊕ Option (SimpleComparisonOperand Value))
  | [], state => pure (.inl state)
  | (declaration, row) :: rest, state => do
      let some cell ← fields.readCell? model scope read declaration row | return .inr none
      match scanFirstFilledObservations [observeCell .validation cell] state with
      | .inl next => scanPartialFirstFilledCells (model := model) scope read fields rest next
      | .inr result => pure (.inr (some result))

private def scanPartialTypedFirstFilled (document : CheckedDocument model) (outer : Env)
    (scope : ValidationRelevanceScope)
    (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell)) :
    List (CheckedFieldFillOperand model) → FirstFilledScanState →
      Except CheckedAddressingError (Option (SimpleComparisonOperand Value))
  | [], _ => pure (some .notEvaluated)
  | operand :: rest, state => do
      let selected : Option (Sum (CheckedSemanticIndexSource model) (CheckedKeyedEntityExtent model)) := match operand with
        | .indexed source => some (.inl source)
        | .keyed source => some (.inr source)
        | _ => none
      let step ← match selected with
        | some source => do
            match ← resolveDeclaredPartialSelected source document scope outer read with
            | none => pure (.inr none)
            | some (.unknown cause) | some (.poison cause) => pure (.inr (some (.unknown cause)))
            | some .empty => pure (.inl (state.enterSelection true false false))
            | some (.value fields) =>
                scanPartialFirstFilledCells (model := model) scope read fields fields.addresses
                  (state.enterSelection fields.addresses.isEmpty false false)
        | none => do
            match ← partialFirstFilledFields? outer operand with
            | none => pure (.inr none)
            | some fields =>
                scanPartialFirstFilledCells (model := model) scope read fields fields.addresses
                  (state.enterSelection fields.addresses.isEmpty false false)
      match step with
      | .inl next => scanPartialTypedFirstFilled document outer scope read rest next
      | .inr result => pure result

private def CheckedFirstFilledComparisonOperand.evaluatePartial
    (document : CheckedDocument model) (outer : Env) (context : FlatContext)
    (scope : ValidationRelevanceScope)
    (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell)) :
    CheckedFirstFilledComparisonOperand model →
      Except (Sum CheckedAddressingError ScalarTemporalEvaluationFault) (Option (SimpleComparisonOperand FirstFilledComparisonValue))
  | .boolean value => pure (some (.value (.boolean value) true))
  | .field declaration _ => do
      if !scope.coversCell model declaration.path outer then return none
      let cell ← (read outer declaration.id).mapError Sum.inl
      pure (cell.map fun cell => projectComparisonObservation model declaration (observeCell .validation cell))
  | .indexed source _ => do
      let observation ← (source.observePartialDocument document scope outer read).mapError Sum.inl
      pure (observation.map (projectComparisonObservation model source.targetDeclaration))
  | .firstFilled source => do
      let value ← (scanPartialTypedFirstFilled document outer scope read source.source.operands {}).mapError Sum.inl
      pure (value.map (projectFirstFilledValue model source.first))
  | .temporal expression => do
      let partialRead : TemporalPartialReadContext model := { document, scope, read }
      let result ← (expression.evalResult .validation context (row := outer)
        (partialRead? := some partialRead)).mapError ScalarTemporalEvaluationFault.separateAddressing
      pure (some (mapFirstFilledOperand .temporal result))

namespace CheckedFirstFilledComparison

def bindingScopes (comparison : CheckedFirstFilledComparison model) :=
  comparison.left.bindingScopes ++ comparison.right.bindingScopes

def hasHaving (comparison : CheckedFirstFilledComparison model) :=
  comparison.left.hasHaving || comparison.right.hasHaving

def referencesField (comparison : CheckedFirstFilledComparison model) (field : FieldId)
    (filterReads : CorrelatedHaving → FieldId → Bool := CorrelatedHaving.referencesField) : Bool :=
  comparison.left.referencesField field filterReads || comparison.right.referencesField field filterReads

/-- Compare values after profile admission; DateRange equality uses stored component identity. -/
def holds (operator : TemporalComparisonOp) : FirstFilledComparisonValue → FirstFilledComparisonValue → Bool
  | .boolean a, .boolean b => if operator == .equal then a == b else a != b
  | .dateRange a, .dateRange b => if operator == .equal then a.sameIdentity b else !(a.sameIdentity b)
  | .temporal (.date a), .temporal (.instant b) => operator.holdsInstant a.instant b
  | .temporal (.instant a), .temporal (.date b) => operator.holdsInstant a b.instant
  | .temporal a, .temporal b => ScalarTemporalValue.holds operator a b
  | _, _ => false

private def verdict (operator : TemporalComparisonOp)
    (left right : SimpleComparisonOperand FirstFilledComparisonValue) : Verdict :=
  let normalize : SimpleComparisonOperand FirstFilledComparisonValue → SimpleComparisonOperand FirstFilledComparisonValue
    | .value (.temporal .noValue) _ => .notEvaluated
    | value => value
  match left, right with
  | .value (.temporal .nonRelevant) _, _ | _, .value (.temporal .nonRelevant) _ => .unknown
  | _, _ => evalSymmetricComparison (holds operator) (normalize left) (normalize right)

def evaluateFull (comparison : CheckedFirstFilledComparison model) (document : CheckedDocument model)
    (outer : Env) (context : FlatContext) : Except (Sum CheckedAddressingError ScalarTemporalEvaluationFault) Verdict := do
  pure (verdict comparison.operator
    (← comparison.left.evaluate document outer context) (← comparison.right.evaluate document outer context))

/-- Partial selection stops on a reached uncovered or silently unavailable cell, retaining that
absence separately from empty substitution and formal causes (spec/07, partial FirstFilledValue). -/
def evaluatePartial? (comparison : CheckedFirstFilledComparison model) (document : CheckedDocument model)
    (outer : Env) (context : FlatContext) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell)) :
    Option (Except (Sum CheckedAddressingError ScalarTemporalEvaluationFault) Verdict) :=
  if comparison.hasHaving then none else some do
    let left ← comparison.left.evaluatePartial document outer context scope read
    let right ← comparison.right.evaluatePartial document outer context scope read
    pure (match left, right with
      | some left, some right => verdict comparison.operator left right
      | _, _ => .unknown)

end CheckedFirstFilledComparison
end A12Kernel
