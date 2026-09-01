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
  | .flat condition => condition.evalSelected context.fields isRelevant
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
  | .repeatableFieldPresence _ _ => .unknown
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

/-- Whether a leaf has an exact partial addressed interpretation. `false` is structural unsupported information and must not be converted to semantic UNKNOWN. -/
def supportsAddressedPartial : ValidationConditionLeaf model → Bool
  | .flat _ | .groupPresence _ _ | .repeatableFieldPresence _ _ => true
  | .orderedNumeric _ comparison =>
      comparison.supportsAddressedPartial
  | .groupList operator [.starredGroup _] =>
      operator.toStarredGroupFillQuantifier?.isSome
  | .repetitionNotUnique _ => true
  | .guardedRootCurrentRepetition _ _ _ => false
  | .guardedRepeatableCurrentRepetition _ _ _ => false
  | _ => false

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
  | .flat condition =>
      some (evalFlatLeafAddressedPartial condition context isRelevant)
  | .repeatableFieldPresence operator declaration =>
      some (if isRelevant declaration.id then
        context.readPartialCell context.outer declaration.id |>.map fun cell? =>
          match cell? with
          | some cell => operator.eval (observeCell .validation cell)
          | none => .unknown
      else
        pure .unknown)
  | .orderedNumeric _ comparison =>
      comparison.evalAddressedPartial? context scope isRelevant
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
  | .repetitionNotUnique _ =>
      some (match repetitionNotUniqueResult? with
        | some result =>
            if result.row == context.outer then
              pure result.verdict
            else
              .error (.repetitionNotUniqueResult context.outer)
        | none => pure .unknown)
  | _ => none

/-- Evaluate one addressed leaf through the same relevance rules. Ordered numeric and starred group-list sources preserve structural addressing failures; direct scalar/group leaves remain the exact pure evaluator lifted into that channel. -/
def evalAddressed (context : AddressedValidationEvaluationContext model) :
    ValidationConditionLeaf model → Except CheckedAddressingError Verdict
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
  | .repeatableFieldPresence operator declaration => do
      pure (operator.eval
        (observeCell .validation
          (← context.readCell context.outer declaration.id)))
  | .repetitionNotUnique _ =>
      .error (.repetitionNotUniqueResult context.outer)
  | .iteratedDateRange condition =>
      match context.input with
      | .checked document | .partialView document _ =>
          condition.verdictOf document context.outer
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
