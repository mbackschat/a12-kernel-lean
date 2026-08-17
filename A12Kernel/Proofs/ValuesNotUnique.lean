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

/-- A retained temporal group omits no descendant: every declaration in its recursive subtree is
    present in the certified expansion with its exact declared temporal policy. -/
theorem checkedTemporalUniquenessGroup_expansion_complete
    (group : CheckedTemporalUniquenessGroup model)
    (declaration : FlatFieldDecl)
    (member : declaration ∈ model.groupSubtreeFields group.groupPath) :
    ∃ field,
      declaration.toTemporalUniquenessField? = some field ∧
      field ∈ group.fields := by
  have admitted : declaration.toTemporalUniquenessField?.isSome = true :=
    List.all_eq_true.mp group.expansionAllTemporal declaration member
  match hField : declaration.toTemporalUniquenessField? with
  | none => rw [hField] at admitted; simp at admitted
  | some field =>
      refine ⟨field, rfl, ?_⟩
      have retained : field ∈
          (model.groupSubtreeFields group.source.groupPath).filterMap
            FlatFieldDecl.toTemporalUniquenessField? :=
        List.mem_filterMap.mpr ⟨declaration, member, hField⟩
      rw [group.expansionOwned] at retained
      simpa [CheckedTemporalUniquenessGroup.fields] using retained

/-- **The kind gate never reports the mixing class.** This is the local half of the measured pre-emption: a Boolean or Confirm beside another category reports the kind code with the mixing code absent, so whatever the kind gate refuses, its diagnostic is never `varyingTypesNotAllowed`. The elaborator runs this scan over the whole operand list before certification, so no authored order can substitute the mixing class for the kind class. -/
theorem firstKindGateRefusal_never_mixing
    (operands : List (ResolvedFieldEntityOperand model))
    (refusal : TemporalValuesNotUniqueElabError) :
    firstKindGateRefusal? operands = some refusal →
      refusal.diagnostic? ≠ some .varyingTypesNotAllowed := by
  intro refused
  rw [firstKindGateRefusal?] at refused
  cases found : firstFieldListKindRefusal? operands with
  | none =>
      rw [found] at refused
      contradiction
  | some kindRefusal =>
      rw [found] at refused
      injection refused with refused
      subst refusal
      simp [TemporalValuesNotUniqueElabError.diagnostic?]

/-- BOOLEAN and CONFIRM are the represented kinds refused outright. DATE_RANGE, the Kernel's
    other measured outright refusal, has no declaration form here. -/
theorem fieldListAdmission_refusedByKind_iff (kind : SurfaceScalarKind) :
    kind.fieldListAdmission = .refusedByKind ↔
      kind = .boolean ∨ kind = .confirm := by
  cases kind <;> simp [SurfaceScalarKind.fieldListAdmission]

/-- An admitted entity list has pairwise non-overlapping slots: the indirect duplicate arm's scan
    returns `none` exactly when no slot is a strict ancestor or descendant of another. A consumer
    reasoning about what a rule reaches may therefore treat the authored slots as independent
    scopes instead of intersecting their extents.

    The nearest stronger claim is false, and deliberately: this is **not** pairwise distinctness.
    The same starred group written twice is admitted and does not overlap itself, because the
    relation ruled out here is strict ancestry rather than equality. -/
theorem firstResolvedOperandOverlap_eq_none_iff
    (operands : List (ResolvedFieldEntityOperand model)) :
    firstResolvedOperandOverlap? operands = none ↔
      operands.Pairwise (fun left right => left.overlaps right = false) := by
  induction operands with
  | nil => simp [firstResolvedOperandOverlap?]
  | cons operand remaining inductionHypothesis =>
      cases found : remaining.find? (operand.overlaps ·) with
      | some overlapping =>
          simp only [firstResolvedOperandOverlap?, found]
          constructor
          · intro impossible; simp at impossible
          · intro pairwise
            have disjoint := (List.pairwise_cons.mp pairwise).1 overlapping
              (List.mem_of_find?_eq_some found)
            rw [List.find?_some found] at disjoint
            simp at disjoint
      | none =>
          simp only [firstResolvedOperandOverlap?, found]
          rw [inductionHypothesis, List.pairwise_cons]
          constructor
          · intro tail
            exact ⟨fun candidate member => by
              simpa using List.find?_eq_none.mp found candidate member, tail⟩
          · intro both; exact both.2

/-- One slot's own scan misses no refused declaration in its expansion. -/
theorem firstExpandedKindRefusal_eq_none_iff (declarations : List FlatFieldDecl) :
    firstExpandedKindRefusal? declarations = none ↔
      ∀ declaration ∈ declarations,
        declaration.policy.kind.surfaceKind.fieldListAdmission ≠ .refusedByKind := by
  induction declarations with
  | nil => simp [firstExpandedKindRefusal?]
  | cons declaration remaining inductionHypothesis =>
      cases admission : declaration.policy.kind.surfaceKind.fieldListAdmission with
      | refusedByKind => simp [firstExpandedKindRefusal?, admission]
      | category _ => simp [firstExpandedKindRefusal?, admission, inductionHypothesis]

/-- The whole-list scan misses no refused declaration: it returns `none` exactly when every
    declaration reached through **every** slot's expansion is admitted to a comparability category.

    The quantifier ranges over the expansion rather than over the slots, which is the whole content
    of the group-operand rule: a group contributes its recursive subtree, so a refused kind two
    levels below the authored path is still caught here. -/
theorem firstFieldListKindRefusal_eq_none_iff
    (operands : List (ResolvedFieldEntityOperand model)) :
    firstFieldListKindRefusal? operands = none ↔
      ∀ operand ∈ operands, ∀ declaration ∈ operand.expansionDeclarations,
        declaration.policy.kind.surfaceKind.fieldListAdmission ≠ .refusedByKind := by
  induction operands with
  | nil => simp [firstFieldListKindRefusal?]
  | cons operand remaining inductionHypothesis =>
      have expandedIff := firstExpandedKindRefusal_eq_none_iff
        (declarations := operand.expansionDeclarations)
      cases refusal : firstExpandedKindRefusal? operand.expansionDeclarations with
      | some found =>
          simp only [firstFieldListKindRefusal?, refusal]
          constructor
          · intro impossible; simp at impossible
          · intro all
            have scanned : firstExpandedKindRefusal? operand.expansionDeclarations = none :=
              expandedIff.mpr (all operand (by simp))
            rw [refusal] at scanned
            simp at scanned
      | none =>
          simp only [firstFieldListKindRefusal?, refusal]
          rw [inductionHypothesis]
          simp only [List.forall_mem_cons]
          exact ⟨fun tail => ⟨expandedIff.mp refusal, tail⟩, fun both => both.2⟩

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
