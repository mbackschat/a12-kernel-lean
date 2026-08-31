import A12Kernel.Elaboration.CheckedStarDocument

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
the owning mechanism rather than per carrier, because the five consumers reading it differ only in
what they fold over the cells.

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

end A12Kernel
