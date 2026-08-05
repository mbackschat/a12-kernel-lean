import A12Kernel.Elaboration.NumberValuesNotUnique
import A12Kernel.Elaboration.TokenValuesNotUnique
import A12Kernel.Elaboration.TemporalValuesNotUnique
import A12Kernel.Proofs.NumericAggregate

/-! # `FieldValuesNotUnique` checked-boundary laws

These laws are about the operator's **admission gate** and about the **path** from a checked operand list to a verdict. The comparison itself belongs to [`Proofs/NumericAggregate.lean`](NumericAggregate.lean).

The route laws exist because a correction to the comparison is not a correction to the operator while any gate on that path still pre-empts it: the availability gate the aggregate families need once suppressed this operator's own route, so a duplicate beside a formally unavailable cell answered UNKNOWN even after the comparison had been fixed to skip it. Each overload's guarantee is a specialization of the one mechanism law rather than an independent statement.
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

/-- The temporal overload's checked route, by the same mechanism law. A formally unavailable temporal cell is skipped like an empty one here too, so no reachable temporal input makes this route answer UNKNOWN. -/
theorem temporalValuesNotUnique_route_never_unknown
    (checked : CheckedTemporalValuesNotUniqueSource model)
    (document : CheckedDocument model) (outer : Env) :
    CheckedTemporalValuesNotUniqueSource.evaluateCheckedDocumentValuesNotUnique
      checked document outer ≠ .ok .unknown :=
  collectTaggedValueListCells_valuesNotUnique_never_unknown _ _

/-- **The kind gate never reports the mixing class.** This is the local half of the measured pre-emption: a Boolean beside a String reports the kind code with the mixing code observed *absent*, so whatever the kind gate refuses, its diagnostic is never `varyingTypesNotAllowed`. The elaborator runs this scan over the whole operand list before certification, so no authored order can substitute the mixing class for the kind class. -/
theorem firstKindGateRefusal_never_mixing
    (operands : List (ResolvedFieldEntityOperand model))
    (refusal : TemporalValuesNotUniqueElabError) :
    firstKindGateRefusal? operands = some refusal →
      refusal.diagnostic? ≠ some .varyingTypesNotAllowed := by
  induction operands with
  | nil => intro refused; simp [firstKindGateRefusal?] at refused
  | cons head remaining inductionHypothesis =>
      intro refused
      simp only [firstKindGateRefusal?] at refused
      by_cases refusedByKind :
          head.declaration.policy.kind.surfaceKind.fieldListAdmission ==
            FieldListOperandAdmission.refusedByKind
      · rw [if_pos refusedByKind] at refused
        simp only [Option.some.injEq] at refused
        subst refused
        simp [TemporalValuesNotUniqueElabError.diagnostic?]
      · rw [if_neg refusedByKind] at refused
        cases later : firstKindGateRefusal? remaining with
        | some deeper =>
            rw [later] at refused
            simp only [Option.some.injEq] at refused
            subst refused
            exact inductionHypothesis later
        | none =>
            rw [later] at refused
            by_cases unestablished :
                head.declaration.policy.kind.surfaceKind.fieldListAdmission ==
                  FieldListOperandAdmission.unestablished
            · rw [if_pos unestablished] at refused
              simp only [Option.some.injEq] at refused
              subst refused
              simp [TemporalValuesNotUniqueElabError.diagnostic?]
            · rw [if_neg unestablished] at refused
              simp at refused

/-- Only BOOLEAN is refused outright in this representation. DATE_RANGE, the Kernel's other outright refusal, has no declaration form here, so the table's measured scope is exactly one kind rather than two. -/
theorem fieldListAdmission_refusedByKind_iff (kind : SurfaceScalarKind) :
    kind.fieldListAdmission = .refusedByKind ↔ kind = .boolean := by
  cases kind <;> simp [SurfaceScalarKind.fieldListAdmission]

/-- The certificate's format scan says what the temporal admission gate claims: **every** operand carries the list's one declared format. The elaborator stores the scan result, so this is what turns that stored fact into the gate a consumer can rely on. -/
theorem temporalValuesNotUnique_oneDeclaredFormat
    (checked : CheckedTemporalValuesNotUniqueSource model) :
    ∀ operand ∈ checked.operands, operand.format = checked.format := by
  have scanned : ∀ (operands : List (CheckedTemporalUniquenessOperand model))
      (expected : String),
      firstMismatchedTemporalFormat? expected operands = none →
        ∀ operand ∈ operands, operand.format = expected := by
    intro operands
    induction operands with
    | nil => intro _ _ operand member; cases member
    | cons head remaining inductionHypothesis =>
        intro expected exhausted operand member
        simp only [firstMismatchedTemporalFormat?] at exhausted
        split at exhausted
        case isTrue matched =>
            rcases List.mem_cons.mp member with head? | tail?
            · exact head? ▸ (beq_iff_eq.mp matched)
            · exact inductionHypothesis expected exhausted operand tail?
        case isFalse => exact absurd exhausted (by simp)
  intro operand member
  rcases List.mem_cons.mp member with head? | tail?
  · exact head? ▸ rfl
  · exact scanned checked.rest checked.first.format checked.oneDeclaredFormat
      operand tail?

end A12Kernel
