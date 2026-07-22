import A12Kernel.Semantics.FlatValidation

/-! # A12Kernel.Semantics.PartialValidation — flat rule and reference relevance

This capsule implements the resolved nonrepeatable subset of [`spec/10` §5](../../spec/10-validation-and-polarity.md#5-full-vs-partial-validation), including kernel 30.8.1's rule-level early skip when a preceding elaborator reports any `Having` filter. Actual filter syntax/evaluation, groups, wildcard repetitions, aggregates, uniqueness, phantom rows, checked whole rules, and messages remain outside it.
-/

namespace A12Kernel

/-- Two flat contexts agree on the explicit evaluation world and every field made concrete by this partial-validation call. Values outside the predicate may differ arbitrarily. -/
def FlatContext.AgreesOn (left right : FlatContext)
    (isRelevant : FlatRelevance) : Prop :=
  left.world = right.world ∧
    ∀ field, isRelevant field = true → left.read field = right.read field

/-- Whether the flat partial-validation rule was skipped by its error-field gate or
    evaluated to the ordinary four-state condition verdict. `skipped` remains distinct
    from an evaluated `notFired` or `unknown` result. -/
inductive FlatPartialResult where
  | skipped
  | evaluated (verdict : Verdict)
  deriving Repr, DecidableEq

/-- Whether the already-elaborated rule contains any `Having` filter. Kernel 30.8.1 skips the filtered branch before every relevance decision; this discriminator does not evaluate or represent the filter itself. -/
inductive FlatRuleFilterPresence where
  | unfiltered
  | filtered
  deriving Repr, DecidableEq

/-- Evaluate one resolved nonrepeatable rule instance under a flat relevant-field
    predicate. Filtered rules skip first. For unfiltered rules, the error-field gate
    remains separate from reference masking: inferring the error field from the
    condition would be semantically wrong. -/
def FlatCondition.evalPartial (condition : FlatCondition) (context : FlatContext)
    (errorField : FieldId) (isRelevant : FlatRelevance)
    (filterPresence : FlatRuleFilterPresence) : FlatPartialResult :=
  match filterPresence with
  | .filtered => .skipped
  | .unfiltered =>
      if isRelevant errorField then
        .evaluated (condition.evalSelected context isRelevant)
      else
        .skipped

end A12Kernel
