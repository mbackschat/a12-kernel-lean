import A12Kernel.Elaboration.CheckedGroupPresence
import A12Kernel.Elaboration.NumericComputation
import A12Kernel.Proofs.GroupPresence
import A12Kernel.Proofs.Observation
import A12Kernel.Proofs.SingleGroupElaboration

/-! # Numeric computation group-count reading laws

How the computation arm reads a `NumberOfFilledGroups` operand: which shapes it admits, that its
pre-read gate and its reader refuse together, that its row constituent is the validation arm's, that
the fixed-only and the mixed atom read and gate an all-fixed list alike, and where the count stays
independent of the iteration context.
-/

namespace A12Kernel

/-- A fixed group count over operands none of which is a bound instance acquires no iteration
    reader and no outer environment.

    This restates a guard that used to say the count delegates to the scalar reader outright and
    so needs no document at all. The measured repeatable-descendant shape falsified the *document*
    half — a group whose only content is a repeatable descendant counts on an instantiated row, and
    only the document carries rows — so the clause reads `document` deliberately. The measured
    bound-instance shape falsified the rest for a group below a repeatable level, which a row target
    counts as the instance its row binds
    ([checkpoint](../../docs/sources/computation-scheduling-probes.md#src-row-atoms)), so the
    hypothesis excludes exactly that shape. Every other operand stays invariant in `outer`,
    `filterRead`, and `starRead`, which is what still separates it from an iterated or correlated
    read. -/
theorem numericComputationEvaluationContext_filledGroupCount_ignoresIteration
    (context : NumericComputationEvaluationContext)
    (groups : List ResolvedGroupReference)
    (outer : Env) (filterRead starRead : Env → FieldId → CheckedCell)
    (unbound : ∀ reference ∈ groups, reference.boundInstanceOperand model = false) :
    ({ context with outer, filterRead, starRead } :
        NumericComputationEvaluationContext).readCheckedNumericComputationAtom
        (model := model) (.numeric (.filledGroupCount groups)) =
      context.readCheckedNumericComputationAtom
        (model := model) (.numeric (.filledGroupCount groups)) := by
  have readings : ∀ (remaining : List ResolvedGroupReference),
      (∀ reference ∈ remaining, reference.boundInstanceOperand model = false) →
      remaining.mapM (fun reference =>
          ({ context with outer, filterRead, starRead } :
            NumericComputationEvaluationContext).readGroupCountOperand model (.fixed reference)) =
        remaining.mapM (fun reference => context.readGroupCountOperand model (.fixed reference)) := by
    intro remaining
    induction remaining with
    | nil => intro _; rfl
    | cons reference rest induction =>
        intro unboundAll
        have head : reference.boundInstanceOperand model = false := unboundAll reference (by simp)
        simp only [List.mapM_cons,
          induction (fun member within => unboundAll member (List.mem_cons_of_mem _ within))]
        simp [NumericComputationEvaluationContext.readGroupCountOperand,
          NumericComputationEvaluationContext.readGroupContent, head]
  simp only [NumericComputationEvaluationContext.readCheckedNumericComputationAtom,
    ScalarComputationContext.readNumericComputationAtomWith,
    NumericComputationEvaluationContext.readFilledGroupCount, readings groups unbound]

/-- Depth is irrelevant to the compute-arm group count: one compute-present cell **anywhere**
    in an admitted operand's subtree makes that group count as filled.

    This is the consumer-visible half of `computationDescendants_admitted_eq_subtreeFields`. A
    re-narrowing of the operand's extent to its direct children breaks it, because a shell
    group — one owning no direct field at all — would then contribute an empty cell list and
    could never be filled. -/
theorem groupPresentForComputation_of_subtreeMember
    (context : ScalarComputationContext) (model : FlatModel)
    {reference : ResolvedGroupReference} {descendants : List FlatFieldDecl}
    (admitted : reference.computationDescendants? model = some descendants)
    {declaration : FlatFieldDecl}
    (member : declaration ∈ model.groupSubtreeFields reference.path)
    (present :
      (observeCell .computation (context.read declaration.id)).presentForComputation = true) :
    groupPresentForComputation
        (descendants.map fun source =>
          observeCell .computation (context.read source.id)) = true := by
  rw [computationDescendants_admitted_eq_subtreeFields admitted]
  exact List.any_eq_true.mpr
    ⟨observeCell .computation (context.read declaration.id),
      List.mem_map_of_mem member, present⟩

/-- Wherever the established fixed-only reader answers, the widened arm answers identically.

    The addressed evaluator now answers one shape the scalar reader refuses — a group whose subtree
    carries a repeatable descendant, whose content the Kernel decides structurally and a cell-list
    projection cannot express. That widening is deliberate, so the two are no longer equal on every
    list: this states the property that survives and is the one that matters, that the new arm
    changes nothing the old one already decided.

    It is stated per operand rather than per list because the widening happens per operand; the
    earlier list-level equality was a lift of exactly this, and lifting it now would need a
    hypothesis on every element that says no more than the conjunction of these. -/
theorem readGroupCountOperand_fixed_eq_scalarDescendants
    {model : FlatModel} (context : NumericComputationEvaluationContext)
    (reference : ResolvedGroupReference) (descendants : List FlatFieldDecl)
    (admitted : reference.computationDescendants? model = some descendants) :
    context.readGroupCountOperand model (.fixed reference) =
      .ok (.fixed (descendants.map fun declaration =>
        observeCell .computation (context.scalar.read declaration.id)) false) := by
  simp [NumericComputationEvaluationContext.readGroupCountOperand,
    NumericComputationEvaluationContext.readGroupContent, admitted, Except.map]

/-- The refusal survives too: a group outside every admitted shape still refuses, naming its path. -/
theorem readGroupCountOperand_fixed_refuses_outside_admitted_shapes
    {model : FlatModel} (context : NumericComputationEvaluationContext)
    (reference : ResolvedGroupReference)
    (noCells : reference.computationDescendants? model = none)
    (noRows : reference.repeatableDescendantShape? model = none)
    (noInstance : reference.boundInstanceOperand model = false) :
    context.readGroupCountOperand model (.fixed reference) =
      .error (NumericComputationFault.unsupportedGroupCount reference.path) := by
  simp [NumericComputationEvaluationContext.readGroupCountOperand,
    NumericComputationEvaluationContext.readGroupContent, noCells, noRows, noInstance, Except.map]

/-- The compute arm's row constituent **is** the validation arm's, on the shape only it admits.

    Both arms decide whether a group has an instantiated row somewhere beneath it, and until now
    they did so through two independent tests — the validation arm's `rowWithinGroup`, and the
    compute arm's own scan over the repeatable groups its shape query returns. The Kernel was
    measured to answer the same on this shape at any repetition depth and with only the outer row
    instantiated ([checkpoints](../../docs/sources/group-and-iteration-probes.md#src-group-count-row-domains)), so the two
    tests agreeing is the property that must not quietly lapse: without it one arm could count a
    shell the other calls empty, on a document neither arm's own cases exercise.

    The hypothesis is the unique level identity model validation establishes, which is exactly what
    `repeatableGroupAtLevel?` is documented to assume. -/
theorem groupCount_rowConstituent_eq_validationArm
    {model : FlatModel} (rows : List RowAddr)
    (reference : ResolvedGroupReference) (repeatables : List RepeatableGroupDecl)
    (shape : reference.repeatableDescendantShape? model = some repeatables)
    (levels : ∀ group ∈ model.repeatableGroups,
      model.repeatableGroupAtLevel? group.level = some group) :
    (repeatables.any fun group => rows.any fun row => row.group == group.level) =
      rows.any (CheckedDocument.rowWithinGroup model reference.path []) := by
  have hrep : repeatables =
      model.repeatableGroups.filter fun group => reference.path.isPrefixOf group.path := by
    simp only [ResolvedGroupReference.repeatableDescendantShape?] at shape
    split at shape
    · simp at shape
    · split at shape
      · simp at shape
      · exact (Option.some.inj shape).symm
  subst hrep
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, List.mem_filter, CheckedDocument.rowWithinGroup]
  constructor
  · rintro ⟨g, ⟨hgmem, hpre⟩, r, hrmem, hlevel⟩
    refine ⟨r, hrmem, ?_⟩
    have : r.group = g.level := by simpa using hlevel
    rw [this, levels g hgmem]
    simpa using hpre
  · rintro ⟨r, hrmem, hrow⟩
    revert hrow
    cases hlook : model.repeatableGroupAtLevel? r.group with
    | none => simp
    | some g =>
        intro hrow
        have hgmem : g ∈ model.repeatableGroups := by
          simpa using List.mem_of_find?_eq_some hlook
        have hglevel : g.level = r.group := by
          have := List.find?_some hlook
          simpa using this
        refine ⟨g, ⟨hgmem, ?_⟩, r, hrmem, by simp [hglevel]⟩
        simpa using hrow

/-- The pre-read structural gate and the operand reader raise the `unsupportedGroupCount` refusal
    exactly together.

    The law covers that refusal only. An admitted bound-instance operand still faults with
    `repeatableAddressing` when `outer` does not bind the group's scope, which the gate does not
    see. Elaboration refuses such an operand as `unboundOperandLevel` at a fixed target and at a target
    of an unrelated repeatable level, the two shapes `Conformance/RepeatableNumberPlanRowGroups.lean`
    locks, but no law states that it is unreachable.

    Two sites decide whether a fixed group-count operand is admitted, and only one of them runs on
    every route, so a widening that reaches the reader alone leaves the gate rejecting an operand
    the reader would have counted — which is how the repeatable-descendant shell stayed refused
    end to end after its reader already answered. Both now decide through
    `computationOperandAdmitted`, and this states that the equivalence is the shared predicate
    rather than a coincidence of two matches. -/
theorem readGroupCountOperand_fixed_error_iff_notAdmitted
    {model : FlatModel} (context : NumericComputationEvaluationContext)
    (reference : ResolvedGroupReference) :
    context.readGroupCountOperand model (.fixed reference) =
        .error (NumericComputationFault.unsupportedGroupCount reference.path) ↔
      reference.computationOperandAdmitted model = false := by
  simp only [NumericComputationEvaluationContext.readGroupCountOperand,
    NumericComputationEvaluationContext.readGroupContent,
    ResolvedGroupReference.computationOperandAdmitted]
  cases cells : reference.computationDescendants? model <;>
    cases rows : reference.repeatableDescendantShape? model <;>
      cases bound : reference.boundInstanceOperand model <;>
        simp [Except.map, NumericComputationEvaluationContext.readGroupInstanceAt,
          FlatModel.computationGroupSource, ResolvedComputationGroupSource.read,
          ResolvedComputationGroupSource.readWith] <;>
        cases path : context.outer.pathForScope (model.repeatableScopeForGroupPath reference.path) <;>
        simp [Except.mapError, Functor.map, Except.map, bind, Except.bind, pure, Except.pure,
          Function.comp_def]
  all_goals
    have pureRead (Error : Type) (fields : List FlatFieldDecl) :
        (fields.mapM fun declaration =>
          (Except.ok (observeCell .computation (context.starRead context.outer declaration.id)) :
            Except Error CellObservation)) =
          Except.ok (fields.map fun declaration => observeCell .computation (context.starRead context.outer declaration.id)) := by
      induction fields with
      | nil => rfl
      | cons first rest ih => simp [List.mapM_cons, ih, bind, Except.bind, Functor.map, Except.map, pure, Except.pure]
    simp [pureRead]


/-- The two group-count atom shapes gate an all-fixed operand list identically.

    The companion to the reading law below, at the other site that can refuse an operand. Without
    it the mixed atom could stay ungated, and `evalOrdered`'s left-poison short circuit would then
    hide its structural fault behind a branch that is never reached — the fault reported for one
    atom and swallowed for the other over the identical operand. -/
theorem numericComputationFault_filledGroupCount_eq_mixed
    {model : FlatModel} (groups : List ResolvedGroupReference) :
    CheckedNumericComputationAtom.numericComputationFault?
        (model := model) (.numeric (.filledGroupCount groups)) =
      CheckedNumericComputationAtom.numericComputationFault?
        (model := model) (.filledGroupCountMixed (groups.map .fixed)) := by
  simp [CheckedNumericComputationAtom.numericComputationFault?, List.findSome?_map,
    Function.comp_def]

/-- The two group-count atom shapes read an all-fixed operand list identically.

    An authored list reaches `filledGroupCountMixed` only when some operand carries a star, so
    without this law an operand's admissibility could depend on a **sibling's** form: the addressed
    evaluator delegated the starless atom to the scalar reader, which necessarily refuses a
    repeatable-descendant operand, while the mixed atom answered the identical operand from the
    document. This states the invariant that closes that seam — atom shape is a routing detail and
    carries no semantics of its own. -/
theorem readCheckedNumericComputationAtom_filledGroupCount_eq_mixed
    {model : FlatModel} (context : NumericComputationEvaluationContext)
    (groups : List ResolvedGroupReference) :
    context.readCheckedNumericComputationAtom (model := model)
        (.numeric (.filledGroupCount groups)) =
      context.readCheckedNumericComputationAtom (model := model)
        (.filledGroupCountMixed (groups.map .fixed)) := by
  simp [NumericComputationEvaluationContext.readCheckedNumericComputationAtom,
    ScalarComputationContext.readNumericComputationAtomWith,
    NumericComputationEvaluationContext.readFilledGroupCount, List.mapM_map,
    Function.comp_def]

end A12Kernel
