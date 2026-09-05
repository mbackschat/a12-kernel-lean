import A12Kernel.Elaboration.CheckedStarDocument
import A12Kernel.Proofs.StarAddressing

namespace A12Kernel

/-- The immutable starred-field projection is exactly the caller-view projection specialized to the checked document's base read. -/
theorem resolveCheckedField_delegates_to_base_read
    (source : CheckedStarFieldPath model) (checked : CheckedDocument model)
    (outer : Env) :
    source.resolveCheckedField checked outer =
      source.resolveCheckedFieldWithRead checked checked.read outer := by
  rfl

/-- An unknown field remains a field-resolution failure before any environment or document read. -/
theorem checkedDocument_addressedCell_field_error
    (checked : CheckedDocument model) (environment : Env)
    (field : FieldId) (cause : ResolveError)
    (failed : model.lookupUniqueId field = .error cause) :
    checked.addressedCell environment field =
      .error (.field field cause) := by
  unfold CheckedDocument.addressedCell CheckedDocument.addressedCellWithRead
    CheckedDocument.cellAddress
  rw [failed]
  simp only [Except.mapError, bind, Except.bind]

/-- A model-owned field with an incomplete environment retains the exact binding failure before any document read. -/
theorem checkedDocument_addressedCell_environment_error
    (checked : CheckedDocument model) (environment : Env)
    (field : FieldId) (declaration : FlatFieldDecl)
    (cause : EnvBindingError)
    (lookup : model.lookupUniqueId field = .ok declaration)
    (failed :
      environment.pathForScope declaration.repeatableScope = .error cause) :
    checked.addressedCell environment field =
      .error (.environment cause) := by
  unfold CheckedDocument.addressedCell CheckedDocument.addressedCellWithRead
    CheckedDocument.cellAddress
  rw [lookup]
  simp only [Except.mapError, bind, Except.bind]
  rw [failed]

/-- A topology failure is preserved exactly and prevents every checked-document read. -/
theorem resolveCheckedField_addressing_error
    (source : CheckedStarFieldPath model) (checked : CheckedDocument model)
    (outer : Env) (cause : StarAddressingError)
    (failed :
      source.path.resolve checked.source.toDocument outer = .error cause) :
    source.resolveCheckedField checked outer = .error (.addressing cause) := by
  unfold CheckedStarFieldPath.resolveCheckedField
    CheckedStarFieldPath.resolveCheckedFieldWithRead
  rw [failed]
  simp only [Except.mapError, bind, Except.bind]

/-- The common rich-operand construction preserves a topology failure before filtering or addressed reads. -/
theorem resolveCheckedValidationEntityOperandCore_addressing_error
    (source : CheckedStarFieldPath model) (checked : CheckedDocument model)
    (outer : Env) (having : Option CorrelatedHaving)
    (cause : StarAddressingError)
    (failed :
      source.path.resolve checked.source.toDocument outer = .error cause) :
    source.resolveCheckedValidationEntityOperandCore checked outer having =
      .error (.addressing cause) := by
  unfold CheckedStarFieldPath.resolveCheckedValidationEntityOperandCore
  rw [failed]
  rfl

/-- A topology with no concrete leaf produces no addressed cell; an omitted declared tail remains only in the retained hierarchical domain. -/
theorem resolveCheckedField_empty_topology
    (source : CheckedStarFieldPath model) (checked : CheckedDocument model)
    (outer : Env) (topology : ResolvedStarTopology)
    (resolved :
      source.path.resolve checked.source.toDocument outer = .ok topology)
    (empty : topology.environments = []) :
    match source.resolveCheckedField checked outer with
    | .ok projected =>
        projected.topology = topology ∧ projected.cells = []
    | .error _ => False := by
  unfold CheckedStarFieldPath.resolveCheckedField
    CheckedStarFieldPath.resolveCheckedFieldWithRead
  rw [resolved]
  simp only [Except.mapError, bind, Except.bind]
  rw [empty]
  simp [pure, Except.pure]

/-- **The declared-capacity extent only ever removes cells, and it removes exactly the over-limit
ones.** Every consumer that reads the in-capacity projection inherits this: it can never see a cell
the complete view does not have, in an order the complete view does not have, so no answer the
extent produces is one the whole topology could not have produced from some sub-selection. Stated at
the owning mechanism rather than per carrier, because the consumers reading it differ only in what
they fold over the cells. The temporal extremum is the consumer for which that generality earns its
place: it *aborts* on a formally unavailable operand rather than skipping one, so it is the first
whose answer the two views genuinely separate, and it needed no law of its own.

The second conjunct is what makes the first informative — a selection that removed *nothing*
satisfies the sublist alone, and a selection that removed everything would too. -/
theorem resolvedCheckedEntityOperandCore_inCapacity_sublist
    (resolved : ResolvedCheckedEntityOperandCore) :
    resolved.inCapacityAddressedCells.Sublist resolved.addressedCells ∧
      ∀ addressed ∈ resolved.addressedCells,
        addressed ∈ resolved.inCapacityAddressedCells ↔
          addressed.cell.findings.contains .overRepetition = false := by
  refine ⟨List.filter_sublist, ?_⟩
  intro addressed member
  unfold ResolvedCheckedEntityOperandCore.inCapacityAddressedCells
  simp [List.mem_filter, member]

/-- A field's address depends on its environment **only** at its own declared repeatable scope, so
    two environments agreeing there address the same cell whatever else they bind. Together with
    `starPath_resolve_agreeOutsideReopened` this is why a filter's `$` marker changes nothing on a
    level the starred operand does not reopen: candidate and captured environments agree at exactly
    the levels such a field's scope can name. -/
theorem cellAddress_congr_onScope (checked : CheckedDocument model)
    (left right : Env) (field : FieldId) (declaration : FlatFieldDecl)
    (lookup : model.lookupUniqueId field = .ok declaration)
    (agree : ∀ level ∈ declaration.repeatableScope,
      left.bindingAt level = right.bindingAt level) :
    checked.cellAddress left field = checked.cellAddress right field := by
  unfold CheckedDocument.cellAddress
  rw [lookup]
  simp only [Except.mapError, bind, Except.bind]
  rw [env_pathForScope_congr left right declaration.repeatableScope agree]

end A12Kernel
