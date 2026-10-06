import A12Kernel.Elaboration.ValidationCondition.Core

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
  | .indexedFieldPresence _ _ | .repeatableFieldPresence _ _ => .unknown
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

/-- Whether a leaf has an exact partial addressed interpretation. `false` is structural unsupported information and must not be converted to semantic UNKNOWN. -/
def supportsAddressedPartial : ValidationConditionLeaf model → Bool
  | .firstFilledComparison comparison => !comparison.hasHaving
  | .tokenComparison comparison => !comparison.hasHaving
  | .flat _ | .groupPresence _ _ | .repeatableFieldPresence _ _ => true
  | .orderedNumeric _ comparison =>
      comparison.supportsAddressedPartial
  | .groupList operator [.starredGroup _] =>
      operator.toStarredGroupFillQuantifier?.isSome
  | .groupList operator [.starredGroupPresence _] =>
      operator.toStarredGroupFillQuantifier?.isSome
  | .repetitionNotUnique _ => true
  | .customCondition _ | .customFieldValidity _ | .stringPattern _ | .constructedDateValidity _ _ | .stringExpression _ => true
  | .guardedRootCurrentRepetition _ _ _ => false
  | .guardedRepeatableCurrentRepetition _ _ _ => false
  | _ => false

/-- Select component cells at the current row before invoking the shared constructor. Partial
unavailability retains a separate relevance bit: the empty placeholder permits later eager argument
conversion, but no constructor value escapes when any source was unavailable (spec/05 §3). -/
private def evalConstructedDateAddressed
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

/-- Partial relevance is independent of String omission: an unavailable operand never becomes
an empty contribution. The common fold still checks reached range operations (spec/10 §12). -/
private def evalStringExpressionAddressed
    (context : AddressedValidationEvaluationContext model) (isRelevant : FlatRelevance)
    (comparison : CheckedStringExpressionComparison model) : Except CheckedAddressingError Verdict := do
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
          (Option (List (FieldId × CheckedCell)))
    | [] => pure (some [])
    | declaration :: remaining =>
        if leaf.referencesField declaration.id &&
            isRelevant declaration.id then do
          match ← context.readPartialCell context.outer declaration.id with
          | none => pure none
          | some cell => do
              match ← resolve remaining with
              | none => pure none
              | some cells =>
                  pure (some ((declaration.id, cell) :: cells))
        else
          resolve remaining
  match ← resolve model.fields with
  | none => pure .unknown
  | some cells =>
      let fields : FlatContext := {
        context.scalar.fields with
        read := fun field =>
          match cells.find? fun entry => entry.1 == field with
          | some entry => entry.2
          | none => context.scalar.fields.read field }
      pure (leaf.evalSelected fields isRelevant)

/-- Evaluate one partial addressed leaf. The caller supplies the sole relevance-selected group-product query; `none` is structural unsupported information, not semantic UNKNOWN. A reached but nonrelevant supported source returns the family's exact UNKNOWN result. A missing RNU result means that partial relevance excluded the current composite key, while a mismatched result is a structural preparation error. -/
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
      some (evalStringExpressionAddressed context isRelevant comparison)
  | .constructedDateValidity operation source =>
      some (evalConstructedDateAddressed context isRelevant operation source)
  | .repeatableFieldPresence operator declaration =>
      some (if isRelevant declaration.id then
        context.readPartialCell context.outer declaration.id |>.map fun cell? =>
          match cell? with
          | some cell => operator.eval (observeCell .validation cell)
          | none => .unknown
      else
        pure .unknown)
  -- An **uncovered** cell is UNKNOWN and never reaches the validator, which is the same answer an
  -- unreadable covered cell gets and for the same reason: the predicate only ever speaks about a
  -- value this theory could read. The covered branch shares the family's own `evalCell`, so it
  -- cannot drift from the scalar route.
  | .customFieldValidity leaf =>
      some (if isRelevant leaf.operand.source then
        context.readPartialCell context.outer leaf.operand.source
          |>.map fun cell? =>
            match cell? with
            | some cell => leaf.evalCell .validation cell
            | none => .unknown
      else
        pure .unknown)
  -- The covered cell replaces its own read in the scalar context, so both routes share the
  -- condition's `evalSelected`.
  | .stringPattern leaf =>
      let source := leaf.condition.field.id
      some (if isRelevant source then
        context.readPartialCell context.outer source |>.map fun cell? =>
          match cell? with
          | some cell => leaf.condition.evalSelected { context.scalar.fields with
              read := fun field => if field == source then cell else context.scalar.fields.read field }
          | none => .unknown
      else
        pure .unknown)
  | .orderedNumeric _ comparison =>
      comparison.evalAddressedPartial? context scope isRelevant resolveGroup
  | .groupPresence operator reference =>
      some do
        let input ← resolveGroup reference.path context.outer
        pure (operator.eval input.derive)
  | .groupList operator [.starredGroup source] =>
      match operator.toStarredGroupFillQuantifier? with
      | none => none
      | some starredOperator =>
          some do
            let document := match context.input with
              | .legacy document _ => document
              | .checked document | .partialView document _ =>
                  document.source.toDocument
            (source.evaluatePartialQuantifier starredOperator document
              context.outer scope).mapError .addressing
  | .groupList operator [.starredGroupPresence source] =>
      match operator.toStarredGroupFillQuantifier? with
      | none => none
      | some _ =>
          some do
            let document := match context.input with
              | .legacy document _ => document
              | .checked checked | .partialView checked _ =>
                  checked.source.toDocument
            let environments ←
              (source.inCapacityEnvironments document context.outer)
                |>.mapError .addressing
            let states ← environments.mapM fun environment => do
              let input ← resolveGroup source.groupPath environment
              pure input.derive.asGroupListPresence
            pure (operator.evalPresence states).asConservativeVerdict
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
  | .legacy _ _ | .partialView _ _ => .error (.inl (.checkedDocumentRequired []))

/-- Evaluate one addressed leaf through the same relevance rules. Ordered numeric and starred group-list sources preserve structural addressing failures; direct scalar/group leaves remain the exact pure evaluator lifted into that channel. -/
def evalAddressed (context : AddressedValidationEvaluationContext model) :
    ValidationConditionLeaf model → Except CheckedAddressingError Verdict
  | .customCondition name => (context.scalar.customResult name.value).mapError .customCondition
  | .stringPattern leaf => do
      let source := leaf.condition.field.id
      if !context.directRelevant source then return .unknown
      let cell ← context.readCell context.outer source
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
              .fullyRelevant false).mapError .group
          pure (operator.eval input.derive)
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
