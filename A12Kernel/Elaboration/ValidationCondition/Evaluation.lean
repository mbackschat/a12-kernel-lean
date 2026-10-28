import A12Kernel.Elaboration.ValidationCondition.Core
import A12Kernel.Elaboration.PartialEntityValueList
import A12Kernel.Elaboration.PartialFieldFill
import A12Kernel.Elaboration.StringExpression.Partial

/-! # Checked validation-leaf evaluation

This focused module owns how one reached leaf produces a verdict: the scalar route, the addressed
route, the partial-view route, and the rule-owned uniqueness substitution. Leaf construction, static
admission, and dependency discovery stay in `Core`, so a leaf family that adds an evaluation arm
lands here beside its siblings rather than beside its certificate.
-/

namespace A12Kernel

namespace ValidationConditionLeaf

/-- Evaluate one reached leaf with its own relevance rule. Ordinary numeric expressions require every field atom, ordered numeric atoms gate their own reached sources, and flat leaf rules retain their existing operator-specific checks. -/
def evalSelected (context : ValidationEvaluationContext)
    (isRelevant : FlatRelevance) :
    ValidationConditionLeaf model → Verdict
  | .customCondition name => (context.customResult name.value).toOption.getD .unknown
  | .flat condition => condition.evalSelected context.fields isRelevant
  | .scalarTemporal comparison =>
      if comparison.fieldIds.all isRelevant then
        comparison.eval context.fields
      else .unknown
  | .numeric _ comparison =>
      if comparison.allRelevant isRelevant then
        comparison.evalSelectedWithGroups context
      else .unknown
  | .orderedNumeric _ comparison =>
      comparison.evalSelected context isRelevant
  | .groupPresence operator reference =>
      match context.groups reference.path with
      | some state => operator.eval state
      | none => .unknown
  | .groupList operator operands =>
      match operands.mapM fun operand =>
          operand.evalDirectPresence? context isRelevant with
      | some states =>
          (operator.evalPresence states).asConservativeVerdict
      | none => .unknown
  | .keyedGroupPresence _ _ | .indexedFieldPresence _ _ | .repeatableFieldPresence _ _ | .indexedCustomFieldValidity _ | .indexedStringPattern _ => .unknown
  | .repetitionNotUnique _ => .unknown
  | .guardedRootCurrentRepetition guard _ comparison =>
      Verdict.conj
        (if isRelevant guard.id then
          guard.toPresenceField.evalFilled context.fields
        else
          .unknown)
        comparison.eval
  | .guardedRepeatableCurrentRepetition _ _ _ => .unknown
  | .iteratedDateRange _ => .unknown
  -- A nonrelevant operand is UNKNOWN like every other leaf's, and a relevant one reads its checked
  -- cell: the validator never sees a value the surrounding theory treats as unreadable.
  | .customFieldValidity leaf =>
      if isRelevant leaf.operand.source then
        leaf.evalAt context.fields .validation
      else .unknown
  | .stringPattern leaf =>
      if isRelevant leaf.condition.field.id then leaf.condition.evalSelected context.fields
      else .unknown
  | .firstFilledComparison _ | .stringExpression _ | .tokenComparison _ | .constructedDateValidity _ _ | .fieldFill _ _ | .valueList _ | .valuesNotUnique _ => .unknown

/-- A plain numeric comparison read through the ordered carrier, every atom as an ordinary one. In each
call of partial validation each atom then reads with its own relevance, and a fixed-group `NumberOfFilledGroups`
walks its counted groups as the ordered leaf does (spec/10 §5): the population replay's partial channel
over the negated-corpus, group-coverage and computation-guard captures, 2026-10-24. -/
def _root_.A12Kernel.NumericComparisonOf.toOrdered (comparison : NumericComparison) : OrderedNumericComparison model :=
  { op := comparison.op, left := comparison.left.map .ordinary, right := comparison.right.map .ordinary
    suppressExactScaleWarning := comparison.suppressExactScaleWarning }

/-- Whether a leaf has an exact partial addressed interpretation. `false` is structural unsupported information and must not be converted to semantic UNKNOWN. -/
def supportsAddressedPartial : ValidationConditionLeaf model → Bool
  | .fieldFill _ source => !source.hasHaving
  | .valuesNotUnique _ => true
  | .indexedFieldPresence _ _ | .keyedGroupPresence _ _ | .valueList _ => true
  | .firstFilledComparison comparison => !comparison.hasHaving
  | .tokenComparison comparison => !comparison.hasHaving
  | .flat _ | .groupPresence _ _ | .repeatableFieldPresence _ _ => true
  | .orderedNumeric _ comparison =>
      comparison.supportsAddressedPartial
  | .numeric _ comparison => (comparison.toOrdered (model := model)).supportsAddressedPartial
  | .groupList operator operands =>
      operands.all fun
        | .field _ | .indexed _ | .group _ => true
        | .keyed source => source.isGroup && (!source.isStarredGroup || operator.toStarredGroupFillQuantifier?.isSome)
        | .starredGroup _ | .starredGroupPresence _ => operator.toStarredGroupFillQuantifier?.isSome
  | .repetitionNotUnique _ => true
  | .stringExpression _ => true
  | .constructedDateValidity _ source => !source.scalarCore.hasHaving
  | .scalarTemporal source => !source.left.core.hasHaving && !source.right.core.hasHaving
  | .customCondition _ | .customFieldValidity _ | .indexedCustomFieldValidity _ | .stringPattern _ | .indexedStringPattern _ => true
  | .guardedRootCurrentRepetition _ _ _ => false
  | .guardedRepeatableCurrentRepetition _ _ _ => false
  | _ => false

/-- Select component cells at the current row before invoking the shared constructor. Partial
unavailability retains a separate relevance bit: the empty placeholder permits later eager argument
conversion, but no constructor value escapes when any source was unavailable (spec/05 §3). -/
private def evalDirectConstructedDateAddressed
    (context : AddressedValidationEvaluationContext model) (isRelevant : FlatRelevance)
    (operation : ConstructedDateValidityOp) (source : CheckedConstructedDateComponents model) :
    Except CheckedAddressingError Verdict := do
  let document ← match context.input with
    | .checked document | .partialView document _ => pure document
    | .legacy _ _ => throw (.checkedDocumentRequired [])
  let cells ← source.fields.mapM fun field => do
    let cell ← if isRelevant field then context.readPartialCell context.outer field else pure none
    pure (field, cell)
  let readCell field := ((cells.find? (·.1 == field)).bind (·.2)).getD (checkAdmittedRawCell .presentEmpty)
  let observation ← (source.evaluateComponentsWith (fun component =>
    component.readWith .validation readCell (document.storedTextIn context.outer)
      context.scalar.fields.world) .validation >>= source.applyProfileReality).mapError .constructedDate
  pure (if cells.all (·.2.isSome) then (observation.validityVerdict operation).toOption.getD .unknown
    else .unknown)

private def evalConstructedDateAddressed
    (context : AddressedValidationEvaluationContext model) (isRelevant : FlatRelevance)
    (operation : ConstructedDateValidityOp)
    (source : CheckedConstructedDateComponents model (ScalarDateComponent model)) :
    Except CheckedAddressingError Verdict := do
  if let some direct := source.directComponents? then
    return ← evalDirectConstructedDateAddressed context isRelevant operation direct
  let document ← match context.input with
    | .checked document => pure document
    | .legacy _ _ | .partialView _ _ => throw (.checkedDocumentRequired [])
  if !source.scalarBoundFieldIds.all isRelevant then return .unknown
  for scope in source.scalarBindingScopes do
    discard <| (context.outer.pathForScope scope).mapError CheckedAddressingError.environment
  let fields := source.scalarFieldIds.filter fun field =>
    (context.outer.pathForScope (model.fieldRepeatableScope field)).isOk
  let cells ← fields.mapM fun field => do pure (field, ← context.readCell context.outer field)
  let selected := { (document.indexedComputationContextAt context.outer) with
    read := fun field => ((cells.find? (·.1 == field)).map (·.2)).getD malformedCheckedCell
    world := context.scalar.fields.world }
  let observation ← (source.evaluateScalarValidity .validation selected
    (filtered := OrderedNumericValidationAtom.filteredAmountReader context)).mapError (fun _ => .temporalUnavailable)
  pure ((observation.validityVerdict operation).toOption.getD .unknown)

/-- Partial relevance is independent of String omission: an unavailable operand never becomes
an empty contribution. The common fold still checks reached range operations (spec/10 §12). -/
private def evalStringExpressionAddressed
    (context : AddressedValidationEvaluationContext model) (isRelevant : FlatRelevance)
    (comparison : CheckedStringExpressionComparison model) : Except CheckedAddressingError Verdict := do
  if comparison.hasIndexed then
    match context.input with
    | .checked document =>
        let cells ← comparison.boundDeclarations.mapM fun declaration => do
          pure (declaration.id, ← context.readCell context.outer declaration.id)
        let selected := { (document.indexedComputationContextAt context.outer) with
          read := fun field => ((cells.find? (·.1 == field)).map (·.2)).getD malformedCheckedCell }
        return ← (comparison.eval { context.scalar.fields with read := selected.read }
          selected.numberText (some selected)).mapError .stringExpression
    | .legacy _ _ | .partialView _ _ => throw (.checkedDocumentRequired [])
  let document ← match context.input with
    | .checked document | .partialView document _ => pure document
    | .legacy _ _ => throw (.checkedDocumentRequired [])
  let cells ← comparison.declarations.mapM fun declaration => do
    let cell ← if isRelevant declaration.id then context.readPartialCell context.outer declaration.id
      else pure none
    pure (declaration.id, cell)
  let fields : FlatContext := { context.scalar.fields with
    read := fun field => ((cells.find? (·.1 == field)).bind (·.2)).getD (checkAdmittedRawCell .presentEmpty) }
  let numberText field := do
    let declaration ← (model.lookupUniqueId field).toOption
    let path ← (context.outer.pathForScope declaration.repeatableScope).toOption
    (← (document.readNumberFormalText { field, path }).toOption).parsed
  let verdict ← (comparison.eval fields numberText).mapError .stringExpression
  pure (if cells.all (·.2.isSome) then verdict else .unknown)

private def evalFlatLeafAddressedPartial
    (leaf : FlatConditionLeaf)
    (context : AddressedValidationEvaluationContext model)
    (isRelevant : FlatRelevance) :
    Except CheckedAddressingError Verdict := do
  let rec resolve :
      List FlatFieldDecl →
        Except CheckedAddressingError
          (Option (List (FieldId × Option CheckedCell)))
    | [] => pure (some [])
    | declaration :: remaining =>
        if leaf.referencesField declaration.id &&
            isRelevant declaration.id then do
          let cell ← context.readPartialCell context.outer declaration.id
          if cell.isNone && !leaf.isScalarMembership then return none
          match ← resolve remaining with
          | none => pure none
          | some cells => pure (some ((declaration.id, cell) :: cells))
        else
          resolve remaining
  match ← resolve model.fields with
  | none => pure .unknown
  | some cells =>
      let fields : FlatContext := {
        context.scalar.fields with
        read := fun field =>
          ((cells.find? fun entry => entry.1 == field).bind (·.2)).getD
            (context.scalar.fields.read field) }
      -- Scalar membership consumes per-operand unavailability (spec/06 B.4, spec/10),
      -- so a suppressed member cannot erase a different available match.
      let available field := isRelevant field && !(cells.any fun entry => entry.1 == field && entry.2.isNone)
      pure (leaf.evalSelected fields available)

def evalTemporalPartialResult? (context : AddressedValidationEvaluationContext model)
    (scope : ValidationRelevanceScope) (resolveGroup? : Option PartialGroupResolver := none) :
    ValidationConditionLeaf model →
    Option (Except (Sum CheckedAddressingError ScalarTemporalEvaluationFault) Verdict)
  | .scalarTemporal comparison => some do
      let document ← match context.input with
        | .checked document | .partialView document _ => pure document
        | .legacy _ _ => throw (Sum.inl (.checkedDocumentRequired []))
      let partialRead : TemporalPartialReadContext model := { document, scope, read := context.readPartialCell, resolveGroup? }
      (comparison.evalResult .validation context.scalar.fields none context.outer (some partialRead))
        |>.mapError ScalarTemporalEvaluationFault.separateAddressing
  | .constructedDateValidity operation source =>
      if source.directComponents?.isSome then none else some do
        let document ← match context.input with
          | .checked document | .partialView document _ => pure document
          | .legacy _ _ => throw (Sum.inl (.checkedDocumentRequired []))
        let partialRead : TemporalPartialReadContext model := { document, scope, read := context.readPartialCell, resolveGroup? }
        let selected := { (document.indexedComputationContextAt context.outer) with world := context.scalar.fields.world }
        let observation ← (source.evaluateScalarValidity .validation selected (some partialRead))
          |>.mapError ScalarTemporalEvaluationFault.separateAddressing
        pure ((observation.validityVerdict operation).toOption.getD .unknown)
  | _ => none

/-- Positive presence reads held rows first, as Kernel's entity iterator does. The remaining
negative obligation walks declared positions lazily: an uncovered missing position blocks absence
without allocating the whole capacity product (mixed group-predicate matrix, spec/10 §5). -/
private def partialStarredGroupStates (operator : StarredGroupFillQuantifier)
    (path : StarPath) (groupPath : GroupPath)
    (document : Document) (outer : Env) (resolveGroup : PartialGroupResolver) :
    Except CheckedAddressingError (List GroupListPresenceState) := do
  if operator == .atLeastOneGroupFilled then
    let held ← path.inCapacityEnvironments document outer |>.mapError .addressing
    for environment in held do
      if (← resolveGroup groupPath environment).derive.asGroupListPresence == .filled then
        return [.filled]
    return []
  let bound ← path.boundEnvironment outer |>.mapError .addressing
  if StarAxes.environmentOverLimit path.axes bound then return [.empty]
  let rec allEmpty (axes : List StarAxis) (environment : Env) :
      Except CheckedAddressingError Bool := do
    match axes with
    | [] => pure ((← resolveGroup groupPath environment).derive.asGroupListPresence == .empty)
    | axis :: remaining =>
        let some capacity := axis.repeatability | return false
        for coordinate in [:capacity] do
          unless ← allEmpty remaining (environment ++ [(axis.level, coordinate + 1)]) do
            return false
        return true
  pure [if ← allEmpty (path.axes.drop path.firstStar) bound then .empty else .unavailable]

/-- A selected parent binds only the indexed level; lower group stars keep their declared
positions. A missing parent needs wildcard coverage there and complete lower-slot coverage
(keyed-star predicate matrix, spec/10 §5). -/
private def partialKeyedStarStates (operator : StarredGroupFillQuantifier)
    (source : CheckedKeyedEntityExtent model) (document : CheckedDocument model)
    (scope : ValidationRelevanceScope) (outer : Env)
    (read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell))
    (resolveGroup : PartialGroupResolver) : Except CheckedAddressingError (List GroupListPresenceState) := do
  let view ← document.applyPartialGeneratedPreliminaryForScope scope |>.mapError .indexPreliminary
  match ← source.selectPartial view outer read with
  | none | some (.unknown _) | some (.poison _) => pure [.unavailable]
  | some .empty =>
      if operator == .atLeastOneGroupFilled then return []
      let bound := source.selection.indexDeclaration.repeatableScope.dropLast
      let complete ← source.declarations.allM fun declaration =>
        view.relevance.coversDeclaredFieldExtent model declaration.path
          (declaration.repeatableScope.drop bound.length) outer
          (some source.selection.indexSource.group.level) |>.mapError .addressing
      pure [if complete then .empty else .unavailable]
  | some (.value environment) =>
      let some axes := model.repeatableAxesForScope? (model.repeatableScopeForGroupPath source.groupPath)
        | throw (.addressing (.unsupportedGroupOperand source.groupPath))
      partialStarredGroupStates operator { axes, firstStar := source.boundLevelCount }
        source.groupPath document.source.toDocument environment resolveGroup

/-- Delay presence reads until the predicate reaches their authored position. Selected fixed
groups share the scalar state query; selected stars retain the lower declared extent. -/
def partialGroupOperandStates? (operator : GroupFillQuantifier)
    (context : AddressedValidationEvaluationContext model) (scope : ValidationRelevanceScope)
    (isRelevant : FlatRelevance) (resolveGroup : PartialGroupResolver)
    (operand : ResolvedGroupListOperand model) :
    Option (Unit → Except CheckedAddressingError (List GroupListPresenceState)) :=
  let document := match context.input with
    | .legacy document _ => document
    | .checked checked | .partialView checked _ => checked.source.toDocument
  match operand with
  | .field declaration => some fun () => do
      if !isRelevant declaration.id then return [.unavailable]
      let cell ← context.readPartialCell context.outer declaration.id
      pure [cell.map (fun value => (observeCell .validation value).asGroupListPresence) |>.getD .unavailable]
  | .indexed source =>
      match context.input with
      | .legacy _ _ => none
      | .checked checked | .partialView checked _ => some fun () => do
          let observation ← source.observePartialDocument checked scope context.outer context.readPartialCell
          pure [observation.map CellObservation.asGroupListPresence |>.getD .unavailable]
  | .keyed source =>
      if !source.isGroup then none else
      match context.input with
      | .legacy _ _ => none
      | .checked checked | .partialView checked _ =>
          if source.isStarredGroup then do
            let selected ← operator.toStarredGroupFillQuantifier?
            pure fun () => partialKeyedStarStates selected source checked scope context.outer
              context.readPartialCell resolveGroup
          else some fun () => do
            let state ← source.partialGroupState checked scope context.outer context.readPartialCell
            pure [state.map GroupPresenceState.asGroupListPresence |>.getD .unavailable]
  | .group reference => some fun () => do
      pure [(← resolveGroup reference.path context.outer).derive.asGroupListPresence]
  | .starredGroup source => do
      let selected ← operator.toStarredGroupFillQuantifier?
      pure fun () => partialStarredGroupStates selected source.path source.group.path document context.outer resolveGroup
  | .starredGroupPresence source => do
      let selected ← operator.toStarredGroupFillQuantifier?
      pure fun () => partialStarredGroupStates selected source.path source.groupPath document context.outer resolveGroup

private def scanPartialGroupReaders (operator : GroupFillQuantifier)
    (readers : List (Unit → Except CheckedAddressingError (List GroupListPresenceState))) :
    Except CheckedAddressingError Verdict := do
  for read in readers do
    let verdict := (operator.evalPresence (← read ())).asConservativeVerdict
    match operator with
    | .atLeastOneGroupFilled =>
        if verdict == .fired .value then return verdict
    | .notAllGroupsFilled =>
        if verdict == .fired .omission then return verdict
    | .allGroupsFilled =>
        unless verdict == .fired .value do return .unknown
    | .noGroupFilled =>
        unless verdict == .fired .omission do return .unknown
    | .groupsNotCollectivelyFilled => return .unknown
  pure (operator.evalPresence []).asConservativeVerdict

/-- The mixed predicate checks the positive witness before searching for a settled empty
operand; unavailable peers do not erase either witness (RuntimeController entity-list helpers,
spec/10 §5). The two passes retain the Kernel's reached-read order. -/
def evalPartialGroupReaders (operator : GroupFillQuantifier)
    (readers : List (Unit → Except CheckedAddressingError (List GroupListPresenceState))) :
    Except CheckedAddressingError Verdict := do
  if operator == .groupsNotCollectivelyFilled then
    if (← scanPartialGroupReaders .atLeastOneGroupFilled readers) != .fired .value then
      return .unknown
    scanPartialGroupReaders .notAllGroupsFilled readers
  else scanPartialGroupReaders operator readers

/-- Evaluate one partial addressed leaf. `isRelevant` is read as given: the public rule entry adds model globals before normalizing it, so only a caller bypassing that entry can exclude a global source. The caller supplies the sole relevance-selected group-product query; `none` is structural unsupported information, not semantic UNKNOWN. A reached but nonrelevant supported source returns the family's exact UNKNOWN result. A missing RNU result means that partial relevance excluded the current composite key, while a mismatched result is a structural preparation error. -/
def evalAddressedPartial?
    (context : AddressedValidationEvaluationContext model)
    (scope : ValidationRelevanceScope)
    (isRelevant : FlatRelevance)
    (resolveGroup :
      GroupPath → Env →
        Except CheckedAddressingError ResolvedGroupPresenceInput)
    (repetitionNotUniqueResult? : Option RepetitionNotUniqueResult) :
    ValidationConditionLeaf model →
      Option (Except CheckedAddressingError Verdict)
  | .fieldFill operator source =>
      match context.input with
      | .legacy _ _ => none
      | .checked document | .partialView document _ =>
          some (source.evaluatePartialFill operator document scope context.outer context.readPartialCell)
  | .valuesNotUnique source =>
      match context.input with
      | .legacy _ _ => none
      | .checked document | .partialView document _ => some do
          match ← source.evaluatePartialDocument document context.outer scope context.readPartialCell with
          | .skippedHaving => pure .unknown
          | .evaluated verdict => pure verdict
  | .valueList source =>
      match context.input with
      | .legacy _ _ => none
      | .checked document | .partialView document _ => some do
          match ← source.evaluatePartialDocument document context.outer scope context.readPartialCell with
          | .skippedHaving => pure .unknown
          | .evaluated verdict => pure verdict
  | .customCondition name => some ((context.scalar.customResult name.value).mapError .customCondition)
  | .flat condition =>
      some (evalFlatLeafAddressedPartial condition context isRelevant)
  | .firstFilledComparison comparison =>
      match context.input with
      | .checked document | .partialView document _ =>
          (comparison.evaluatePartial? document context.outer context.scalar.fields scope context.readPartialCell).map fun result =>
            result.mapError fun | .inl error => error | .inr _ => .temporalUnavailable
      | .legacy _ _ => none
  | .tokenComparison comparison =>
      match context.input with
      | .checked document | .partialView document _ =>
          comparison.evaluatePartial? document context.outer scope context.readCell
      | .legacy _ _ => none
  | .stringExpression comparison =>
      match context.input with
      | .checked document | .partialView document _ =>
          some (comparison.evalPartial document scope context.outer context.readPartialCell isRelevant)
      | .legacy _ _ => none
  | leaf@(.scalarTemporal _) => (leaf.evalTemporalPartialResult? context scope (some resolveGroup)).map
      (Except.mapError fun | .inl error => error | .inr fault => fault.toAddressing)
  | leaf@(.constructedDateValidity operation source) =>
      match source.directComponents? with
      | some direct => some (evalDirectConstructedDateAddressed context isRelevant operation direct)
      | none => (leaf.evalTemporalPartialResult? context scope (some resolveGroup)).map
          (Except.mapError fun | .inl error => error | .inr fault => fault.toAddressing)
  | .indexedFieldPresence operator source =>
      some do
        let document ← match context.input with
          | .checked document | .partialView document _ => pure document
          | .legacy _ _ => throw (.checkedDocumentRequired source.group.path)
        let value ← source.observePartialDocument document scope context.outer context.readPartialCell
        pure (value.map operator.eval |>.getD .unknown)
  | .keyedGroupPresence operator source =>
      some do
        let document ← match context.input with
          | .checked document | .partialView document _ => pure document
          | .legacy _ _ => throw (.checkedDocumentRequired source.groupPath)
        source.partialGroupPresence operator document scope context.outer context.readPartialCell
  | .repeatableFieldPresence operator declaration =>
      some (if isRelevant declaration.id then
        context.readPartialCell context.outer declaration.id |>.map fun cell? =>
          match cell? with
          | some cell => operator.eval (observeCell .validation cell)
          | none => .unknown
      else
        pure .unknown)
  | .indexedStringPattern leaf =>
      some do
        let document ← match context.input with
          | .checked document | .partialView document _ => pure document
          | .legacy _ _ => throw (.checkedDocumentRequired leaf.selection.group.path)
        let observation ← leaf.selection.observePartialDocument document scope context.outer context.readPartialCell
        leaf.leaf.condition.pattern.checkExecution.mapError (fun _ => .stringExpression .emptyPattern)
        pure (observation.map leaf.evalObservation |>.getD .unknown)
  | .indexedCustomFieldValidity leaf =>
      some do
        let document ← match context.input with
          | .checked document | .partialView document _ => pure document
          | .legacy _ _ => throw (.checkedDocumentRequired leaf.source.selection.group.path)
        let observation ← leaf.source.selection.observePartialDocument document scope context.outer context.readPartialCell
        match observation with
        | none => pure .unknown
        | some observation => (leaf.directLeaf.evalValidationObservation observation).mapError (fun _ => .typeValidityValueFailure)
  | .customFieldValidity leaf =>
      some do
        if !isRelevant leaf.operand.source then return .unknown
        match ← context.readPartialCell context.outer leaf.operand.source with
        | some cell => (leaf.evalValidationObservation (observeCell .validation cell)).mapError (fun _ => .typeValidityValueFailure)
        | none => pure .unknown
  | .stringPattern leaf => some do
      let source := leaf.condition.field.id
      let cell? ← if isRelevant source then context.readPartialCell context.outer source else pure none
      leaf.condition.pattern.checkExecution.mapError (fun _ => .stringExpression .emptyPattern)
      match cell? with
      | some cell => pure (leaf.condition.evalSelected { context.scalar.fields with
          read := fun field => if field == source then cell else context.scalar.fields.read field })
      | none => pure .unknown
  | .orderedNumeric _ comparison =>
      comparison.evalAddressedPartial? context scope isRelevant resolveGroup
  | .numeric _ comparison =>
      comparison.toOrdered.evalAddressedPartial? context scope isRelevant resolveGroup
  | .groupPresence operator reference =>
      some do
        let input ← resolveGroup reference.path context.outer
        pure (operator.eval input.derive)
  | .groupList operator operands =>
      do
        let readers ← operands.mapM (partialGroupOperandStates? operator context scope isRelevant resolveGroup)
        pure (evalPartialGroupReaders operator readers)
  | .repetitionNotUnique _ =>
      some (match repetitionNotUniqueResult? with
        | some result =>
            if result.row == context.outer then
              pure result.verdict
            else
              .error (.repetitionNotUniqueResult context.outer)
        | none => pure .unknown)
  | _ => none

def evalFirstFilledComparisonAddressedResult (context : AddressedValidationEvaluationContext model)
    (comparison : CheckedFirstFilledComparison model) :
    Except (Sum CheckedAddressingError ScalarTemporalEvaluationFault) Verdict :=
  match context.input with
  | .checked document => comparison.evaluateFull document context.outer context.scalar.fields
      (OrderedNumericValidationAtom.filteredAmountReader context)
  | .legacy _ _ | .partialView _ _ => .error (.inl (.checkedDocumentRequired []))

/-- Evaluate one addressed leaf through the same relevance rules. Ordered numeric and starred group-list sources preserve structural addressing failures; direct scalar/group leaves remain the exact pure evaluator lifted into that channel. -/
def evalAddressed (context : AddressedValidationEvaluationContext model) :
    ValidationConditionLeaf model → Except CheckedAddressingError Verdict
  | .flat condition => do
      if !(ValidationConditionLeaf.flat (model := model) condition).requiresAddressedValidation then
        return condition.evalSelected context.scalar.fields context.directRelevant
      let cells ← (model.fields.filter fun field =>
        condition.referencesField field.id && context.directRelevant field.id).mapM fun field => do
          pure (field.id, ← context.readCell context.outer field.id)
      let fields : FlatContext := { context.scalar.fields with
        read := fun field => (cells.find? (·.1 == field)).map (·.2) |>.getD (context.scalar.fields.read field) }
      pure (condition.evalSelected fields context.directRelevant)
  | .customCondition name => (context.scalar.customResult name.value).mapError .customCondition
  | .indexedStringPattern leaf => do
      let document ← match context.input with
        | .checked document => pure document
        | .legacy _ _ | .partialView _ _ => throw (.checkedDocumentRequired leaf.selection.group.path)
      let observation ← leaf.selection.observeDocument document context.outer .validation
      leaf.leaf.condition.pattern.checkExecution.mapError (fun _ => .stringExpression .emptyPattern)
      pure (leaf.evalObservation observation)
  | .indexedCustomFieldValidity leaf => do
      let document ← match context.input with
        | .checked document => pure document
        | .legacy _ _ | .partialView _ _ => throw (.checkedDocumentRequired leaf.source.selection.group.path)
      (leaf.directLeaf.evalValidationObservation
        (← leaf.source.selection.observeDocument document context.outer .validation)).mapError
          (fun _ => .typeValidityValueFailure)
  | .customFieldValidity leaf => do
      if !context.directRelevant leaf.operand.source then return .unknown
      let cell ← context.readCell context.outer leaf.operand.source
      (leaf.evalValidationObservation (observeCell .validation cell)).mapError
        (fun _ => .typeValidityValueFailure)
  | .stringPattern leaf => do
      let source := leaf.condition.field.id
      let cell? ← if context.directRelevant source then some <$> context.readCell context.outer source else pure none
      leaf.condition.pattern.checkExecution.mapError (fun _ => .stringExpression .emptyPattern)
      let some cell := cell? | return .unknown
      pure (leaf.condition.evalSelected { context.scalar.fields with
        read := fun field => if field == source then cell else context.scalar.fields.read field })
  | .stringExpression comparison =>
      evalStringExpressionAddressed context context.directRelevant comparison
  | .firstFilledComparison comparison =>
      (evalFirstFilledComparisonAddressedResult context comparison).mapError fun
        | .inl error => error
        | .inr _ => .temporalUnavailable
  | .tokenComparison comparison =>
      match context.input with
      | .checked document => comparison.evaluateFull (world := context.scalar.fields.world) document context.outer
      | .legacy _ _ | .partialView _ _ => .error (.checkedDocumentRequired [])
  | .constructedDateValidity operation source =>
      evalConstructedDateAddressed context context.directRelevant operation source
  | .valuesNotUnique source =>
      match context.input with
      | .checked document => source.evaluateFull (world := context.scalar.fields.world) document context.outer
      | .legacy _ _ | .partialView _ _ => .error (.checkedDocumentRequired [])
  | .valueList source =>
      match context.input with
      | .checked document => source.evaluateFull (world := context.scalar.fields.world) document context.outer
      | .legacy _ _ | .partialView _ _ => .error (.checkedDocumentRequired [])
  | .orderedNumeric _ comparison => comparison.evalAddressed context
  | .groupList operator operands => do
      pure (operator.evalTally
        (← ResolvedGroupListOperands.evalAddressedTally
          context operands)).asConservativeVerdict
  | .groupPresence operator reference =>
      match context.input with
      | .legacy _ _ =>
          let leaf : ValidationConditionLeaf model :=
            .groupPresence operator reference
          pure (leaf.evalSelected context.scalar context.directRelevant)
      | .checked document | .partialView document _ => do
          let input ←
            (document.groupPresenceInput reference.path context.outer
              .fullyRelevant false (context.groupPresenceReleased reference.path)).mapError .group
          pure (operator.eval input.derive)
  | .keyedGroupPresence operator source => do
      let document ← match context.input with
        | .checked document => pure document
        | _ => throw (.checkedDocumentRequired source.groupPath)
      source.validationGroupPresence operator document context.outer
  | .indexedFieldPresence operator source => do
      let document ← match context.input with
        | .checked document => pure document
        | .legacy _ _ | .partialView _ _ => throw (.checkedDocumentRequired source.group.path)
      pure (operator.eval (← source.observeDocument document context.outer .validation))
  | .repeatableFieldPresence operator declaration => do
      pure (operator.eval
        (observeCell .validation
          (← context.readCell context.outer declaration.id)))
  | .repetitionNotUnique _ =>
      .error (.repetitionNotUniqueResult context.outer)
  | .iteratedDateRange condition =>
      match context.input with
      | .checked document | .partialView document _ =>
          condition.verdictOf (world := context.scalar.fields.world) document context.outer
      | .legacy _ _ =>
          -- The legacy scalar channel carries no checked document, and this leaf reads at a row.
          .error (.checkedDocumentRequired [])
  | .guardedRepeatableCurrentRepetition guard source comparison => do
      let cell ← context.readCell context.outer guard.id
      let coordinate ← source.coordinateAt context.outer
        |>.mapError .environment
      pure (Verdict.conj
        (RepeatableFieldPresenceOperator.filled.eval
          (observeCell .validation cell))
        (comparison.eval coordinate))
  -- The list reads the checked document's in-capacity extent. An unretained maximum the
  -- declared-range quantifiers need answers UNKNOWN rather than an invented tail, so the pair
  -- regions hold at this leaf only with a retained capacity.
  | .fieldFill operator source =>
      match context.input with
      | .checked document => do
          let outcome? ← source.evaluateFill? (world := context.scalar.fields.world) operator document context.outer
          pure ((outcome?.map ValidationFillOutcome.asConservativeVerdict).getD .unknown)
      | .legacy _ _ | .partialView _ _ =>
          .error (.checkedDocumentRequired ((source.operands.head?.map (·.groupPath)).getD []))
  | leaf => pure (leaf.evalSelected context.scalar context.directRelevant)

/-- Evaluate one reached leaf with the rule-owned current-row RNU result. Every other leaf delegates to the established addressed evaluator unchanged. -/
def evalAddressedWithRepetitionNotUnique
    (context : AddressedValidationEvaluationContext model)
    (result? : Option RepetitionNotUniqueResult) :
    ValidationConditionLeaf model → Except CheckedAddressingError Verdict
  | .repetitionNotUnique _ =>
      match result? with
      | some result =>
          if result.row == context.outer then
            pure result.verdict
          else
            .error (.repetitionNotUniqueResult context.outer)
      | none => .error (.repetitionNotUniqueResult context.outer)
  | leaf => leaf.evalAddressed context

end ValidationConditionLeaf

end A12Kernel
