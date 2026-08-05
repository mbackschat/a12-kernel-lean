import A12Kernel.Elaboration.NumberValuesNotUnique
import A12Kernel.Elaboration.TokenValuesNotUnique
import A12Kernel.Proofs.NumericAggregate

/-! # `FieldValuesNotUnique` route laws

These laws are about the **path** from a checked operand list to a verdict, not about the comparison itself, which [`Proofs/NumericAggregate.lean`](NumericAggregate.lean) owns.

They exist because a correction to the comparison is not a correction to the operator while any gate on that path still pre-empts it: the availability gate the aggregate families need once suppressed this operator's own route, so a duplicate beside a formally unavailable cell answered UNKNOWN even after the comparison had been fixed to skip it. Each overload's guarantee is a specialization of the one mechanism law rather than an independent statement.
-/

namespace A12Kernel

/-- The Number overload's checked route can never answer UNKNOWN. Reintroducing any suppressing gate between the checked document and the comparison breaks this proof. -/
theorem numberValuesNotUnique_route_never_unknown
    (checked : CheckedNumberEntitySource model)
    (document : CheckedDocument model) (outer : Env) :
    CheckedNumberValuesNotUniqueSource.evaluateCheckedDocumentValuesNotUnique
      checked document outer ≠ .ok .unknown :=
  collectTaggedValueListCells_valuesNotUnique_never_unknown _ _

/-- The String/stored-Enumeration overload's checked route, by the same mechanism law. -/
theorem tokenValuesNotUnique_route_never_unknown
    (checked : CheckedTokenValuesNotUniqueSource model)
    (document : CheckedDocument model) (outer : Env) :
    CheckedTokenValuesNotUniqueSource.evaluateCheckedDocumentValuesNotUnique
      checked document outer ≠ .ok .unknown :=
  collectTaggedValueListCells_valuesNotUnique_never_unknown _ _

end A12Kernel
