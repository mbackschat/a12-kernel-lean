import A12Kernel.Semantics.CoreIL
-- The transport section cites this family's laws directly, so the dependency is deliberate:
-- a transported law must inherit from a named theorem rather than restate its content.
import A12Kernel.Proofs.ValueList

/-!
# Core-IL preservation for the value-list quantifier family

The adequacy argument for [`Semantics/CoreIL.lean`](../Semantics/CoreIL.lean). Preservation is
what makes the core usable as a derivation target: it is universal over all operand shapes, so
every law already proved about `evalOrdered` transports by rewriting instead of reproof.

It is also the design guard. A core that erased a kernel-observable distinction — collapsing
poisoning into UNKNOWN, or letting a collection lose its omission potential — would make these
statements unprovable, and the proof would fail at exactly the erased case. Recorded criteria
are in [`docs/SEMANTIC-CORE-IL-PROPOSAL.md`](../../docs/SEMANTIC-CORE-IL-PROPOSAL.md).
-/

namespace A12Kernel

/-- The two firing quantifiers share one fold, so their scans must agree with it. `AtLeastOne`
searches inside the member set. -/
theorem runFindWitness_inside_eq_scanAtLeastOne
    (members : List (ValueListAtom kind)) (omission : Bool)
    (fields : List (ResolvedValueListSide kind)) :
    CoreTerm.runFindWitness .inside members omission fields
      = scanValueListAtLeastOneFields members omission fields := by
  induction fields with
  | nil => rfl
  | cons operand remaining ih =>
      -- The family's two firing scans order this disjunction differently, so the shared core
      -- formula matches each only up to commutativity.
      simp [CoreTerm.runFindWitness, scanValueListAtLeastOneFields, ih, or_comm]

/-- `NotAll` searches outside the member set. Same fold, opposite membership direction — this is
the whole difference between the two firing quantifiers. -/
theorem runFindWitness_outside_eq_scanNotAll
    (members : List (ValueListAtom kind)) (omission : Bool)
    (fields : List (ResolvedValueListSide kind)) :
    CoreTerm.runFindWitness .outside members omission fields
      = scanValueListNotAllFields members omission fields := by
  induction fields with
  | nil => rfl
  | cons operand remaining ih =>
      simp [CoreTerm.runFindWitness, scanValueListNotAllFields, ih]

/-- The inverted unavailability-sensitive fold agrees with the `No` scan. -/
theorem runScanUntilMatch_eq_scanNo
    (members : List (ValueListAtom kind))
    (fields : List (ResolvedValueListSide kind)) (omission : Bool) :
    CoreTerm.runScanUntilMatch members fields omission
      = scanValueListNoFields members fields omission := by
  induction fields generalizing omission with
  | nil => rfl
  | cons operand remaining ih =>
      simp only [CoreTerm.runScanUntilMatch, scanValueListNoFields]
      split
      · rfl
      · cases h : scanValueListNoCells members operand.cells
            (omission || operand.hasHaving || operand.hasUninstantiatedTail) with
        | matched => rfl
        | unknown => rfl
        | exhausted next => simp [ih]

/-- `AtLeastOne`'s member collection is the core's present-only policy. -/
theorem collectPresentOnly_eq (values : List (ResolvedValueListSide kind)) :
    CoreTerm.collectPresentOnly values = collectAtLeastOneValueListMembers values := by
  induction values with
  | nil => rfl
  | cons operand remaining ih =>
      simp [CoreTerm.collectPresentOnly, collectAtLeastOneValueListMembers, ih]

/-- The poisoning policy agrees with the family's poisoning collection, carrying the same
members and the same omission potential. Stated as a case split rather than an equality because
the two result domains differ: the core keeps `poisoned` separate from a verdict. -/
theorem collectPoisoning_eq (values : List (ResolvedValueListSide kind)) :
    (CoreTerm.collectPoisoning values = .poisoned
        ∧ collectPoisoningValueListMembers values = .unknown)
      ∨ ∃ atoms omission,
          CoreTerm.collectPoisoning values = .members atoms omission
            ∧ collectPoisoningValueListMembers values = .known atoms omission := by
  induction values with
  | nil => exact .inr ⟨[], false, rfl, rfl⟩
  | cons operand remaining ih =>
      simp only [CoreTerm.collectPoisoning, collectPoisoningValueListMembers]
      split
      · exact .inl ⟨rfl, rfl⟩
      · rcases ih with ⟨hCore, hFamily⟩ | ⟨atoms, omission, hCore, hFamily⟩
        · exact .inl ⟨by simp [hCore], by simp [hFamily]⟩
        · exact .inr ⟨operand.presentValues ++ atoms,
            operand.hasHaving || operand.hasMissingPotential || omission,
            by simp [hCore], by simp [hFamily]⟩

/-- `AtLeastOne`'s empty-member short-circuit is redundant: with no members the shared fold
already exhausts to non-firing, so the guard is an optimization rather than a semantic gate.

This is the opposite finding to `NotAll`'s presence guard, which is load-bearing
([`LF72`](../../docs/LEAN-FINDINGS.md)) — and the reason the core keeps one and drops the other. -/
theorem runFindWitness_inside_nil_members (omission : Bool)
    (fields : List (ResolvedValueListSide kind)) :
    CoreTerm.runFindWitness .inside [] omission fields = .notFired := by
  induction fields with
  | nil => rfl
  | cons operand remaining ih =>
      simp [CoreTerm.runFindWitness, valueListMembersContain, ih]

/-- The core's guard predicate is the family's presence predicate. -/
theorem any_hasPresent_eq (fields : List (ResolvedValueListSide kind)) :
    fields.any ResolvedValueListSide.hasPresent
      = orderedValueListFieldsHavePresent fields := by
  induction fields with
  | nil => rfl
  | cons operand remaining ih =>
      simp [orderedValueListFieldsHavePresent, ih]

/-- The redundancy above, transported to the family scan the core replaces. -/
theorem scanAtLeastOne_nil_members (omission : Bool)
    (fields : List (ResolvedValueListSide kind)) :
    scanValueListAtLeastOneFields [] omission fields = .notFired := by
  rw [← runFindWitness_inside_eq_scanAtLeastOne, runFindWitness_inside_nil_members]

/-- **Preservation.** Core evaluation of the lowered term equals the family's ordered evaluator,
for every quantifier and every operand shape. Universal, hypothesis-free beyond checkedness. -/
theorem lowerValueListQuantifier_preserves (quantifier : ValueListQuantifier)
    (fields values : List (ResolvedValueListSide kind)) :
    CoreTerm.eval fields values (lowerValueListQuantifier quantifier)
      = .verdict (quantifier.evalOrdered fields values) := by
  cases quantifier with
  | atLeastOne =>
      simp only [lowerValueListQuantifier, CoreTerm.eval,
        ValueListQuantifier.evalOrdered, collectPresentOnly_eq,
        runFindWitness_inside_eq_scanAtLeastOne]
      split
      · rename_i hEmpty
        rw [List.isEmpty_iff] at hEmpty
        rw [hEmpty, scanAtLeastOne_nil_members]
      · rfl
  | no =>
      simp only [lowerValueListQuantifier, CoreTerm.eval, ValueListQuantifier.evalOrdered]
      rcases collectPoisoning_eq (kind := kind) values with
        ⟨hCore, hFamily⟩ | ⟨atoms, omission, hCore, hFamily⟩
      · simp [hCore, hFamily]
      · simp [hCore, hFamily, runScanUntilMatch_eq_scanNo]
  | notAll =>
      simp only [lowerValueListQuantifier, CoreTerm.eval, ValueListQuantifier.evalOrdered,
        any_hasPresent_eq]
      split
      · rcases collectPoisoning_eq (kind := kind) values with
          ⟨hCore, hFamily⟩ | ⟨atoms, omission, hCore, hFamily⟩
        · simp [hCore, hFamily]
        · simp [hCore, hFamily, runFindWitness_outside_eq_scanNotAll]
      · rfl

/-! ## Law transport

The point of preservation is that existing family laws become core laws by rewriting rather than
by reproof. These two are re-derived, not restated: each cites the family theorem it inherits
from and adds no reasoning of its own. Both hold for every operand shape via the general theorem
above; the concrete separators are chosen to match the family's own retained cases. -/

/-- Transported: values-side unavailability poisons an immediate fields match, in the core. -/
theorem core_valueListNo_unknownMember_before_fields
    (value : ValueListAtom kind) (cause : FormalCause) :
    CoreTerm.eval
        [{ cells := [.present value]
           hasUninstantiatedTail := false, hasHaving := false }]
        [{ cells := [.present value, .unknown cause]
           hasUninstantiatedTail := false, hasHaving := false }]
        (lowerValueListQuantifier .no)
      = .verdict .unknown := by
  rw [lowerValueListQuantifier_preserves, valueListNo_unknownMember_before_fields]

/-- Transported: a reached filtered fields operand makes an exhausted `No` scan omission-typed. -/
theorem core_valueListNo_filtered_nonmatch :
    CoreTerm.eval (kind := .token)
        [{ cells := [.present "B"]
           hasUninstantiatedTail := false, hasHaving := true }]
        [{ cells := [.present "A"]
           hasUninstantiatedTail := false, hasHaving := false }]
        (lowerValueListQuantifier .no)
      = .verdict (.fired .omission) := by
  rw [lowerValueListQuantifier_preserves, valueListNo_filtered_nonmatch]

end A12Kernel
