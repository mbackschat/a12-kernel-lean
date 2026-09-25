import A12Kernel.Elaboration.TableEnumeration

/-! # Table-enumeration inertness laws

One constant decides the family, and the laws below say exactly what it decides. In an A12 document model the construct's table check refuses every field that reaches it, so the construct never succeeds, its four later classes are unreachable, and its mirror in the field-value operator never fires. Each is stated separately because a later model version could break them independently.
-/

namespace A12Kernel

/-- No A12 document-model enumeration is a table enumeration. Everything else here follows. -/
@[simp] theorem a12TableView_not_table (values : List String) :
    isTableEnumeration (a12TableView values) = false := by
  rfl

/-- `ValueNotConsistent` refuses every A12 candidate, whatever its shape and parameters. The
construct is therefore inert rather than merely restricted: no operand, no parameter list, and no
model content makes it succeed. -/
theorem valueNotConsistent_a12_always_refuses (isField hasWildcard : Bool)
    (values : List String) (parameters : List TableConsistencyParameter) :
    (valueNotConsistentRefusal
        { isField := isField, hasWildcard := hasWildcard,
          declaration := a12TableView values } parameters).isSome = true := by
  cases isField <;> cases hasWildcard <;> simp [valueNotConsistentRefusal, tableEnumChainRefusal]

/-- **Every field operand draws one class**, the family's first, whatever its parameters. The shape
arms ahead of it answer in their own classes for a group or a starred selector, so "always the same
class" holds of a field and not of every operand. -/
theorem valueNotConsistent_a12_field_class (values : List String)
    (parameters : List TableConsistencyParameter) :
    valueNotConsistentRefusal { declaration := a12TableView values } parameters =
      some (.family .tableEnumExpected) := by
  simp [valueNotConsistentRefusal, tableEnumChainRefusal]

/-- The four classes behind the table check are unreachable from an A12 model, on any operand
shape. Stated as one disequality per class rather than as a set membership, so that a model version
making any single one live breaks exactly the law that named it. -/
theorem valueNotConsistent_a12_unreachable_classes (isField hasWildcard : Bool)
    (values : List String) (parameters : List TableConsistencyParameter)
    (refusal : TableEnumRefusal)
    (h : valueNotConsistentRefusal
        { isField := isField, hasWildcard := hasWildcard,
          declaration := a12TableView values } parameters = some (.family refusal)) :
    refusal ≠ .dependentColumnSizeMismatch ∧ refusal ≠ .onlyEnumsAllowed ∧
      refusal ≠ .stringValueNotInColumn ∧ refusal ≠ .enumValuesNotInColumn ∧
      refusal ≠ .invalidTableEnum := by
  cases isField <;> cases hasWildcard <;>
    simp [valueNotConsistentRefusal, tableEnumChainRefusal] at h
  subst h
  exact ⟨by simp, by simp, by simp, by simp, by simp⟩

/-- The mirror class never fires either: the field-value operator refuses a table enumeration, and
an A12 model has none. -/
theorem fieldValueOperand_a12_admits (values : List String) :
    fieldValueOperandRefusal (a12TableView values) = none := by
  simp [fieldValueOperandRefusal]

/-- The mirror class fires on exactly the declarations the predicate accepts. -/
theorem fieldValueOperand_invalidTableEnum_iff (declaration : TableEnumerationDeclaration) :
    fieldValueOperandRefusal declaration = some .invalidTableEnum ↔
      isTableEnumeration declaration = true := by
  unfold fieldValueOperandRefusal
  cases h : isTableEnumeration declaration <;> simp_all

/-- And `ValueNotConsistent` refuses on exactly the declarations it rejects. The two together make
the pair a partition of the enumeration declarations rather than two independent checks: whichever
way the one predicate falls, exactly one of the two classes is live. -/
theorem valueNotConsistent_tableEnumExpected_of_nonTable
    (declaration : TableEnumerationDeclaration) (parameters : List TableConsistencyParameter)
    (h : isTableEnumeration declaration = false) :
    tableEnumChainRefusal declaration parameters = some .tableEnumExpected := by
  simp [tableEnumChainRefusal, h]

/-- An absent dependent column checks nothing rather than refusing, so a table whose column is
missing is silently skipped. A consumer treating an empty column as "no value is allowed" would
refuse every parameter the Kernel admits. -/
theorem parameterValueRefusal_absent_column (parameter : TableConsistencyParameter) (name : String) :
    parameterValueRefusal parameter { name := name, allowedValues := [] } = none := by
  simp [parameterValueRefusal]

/-- **The downstream guard never opens for an A12 document model.** One constant decides seventeen
further classes across two stages, and this is the law that says so. -/
theorem tableEnumCheckRuns_a12 (values : List (List String)) :
    tableEnumCheckRuns (values.map a12TableView) = false := by
  induction values with
  | nil => rfl
  | cons _ rest ih => simp [tableEnumCheckRuns, List.any_cons] at ih ⊢

/-- **No A12 model draws a downstream class**, whatever its enumerations declare. Stated over the
whole set rather than per class, because the guard is what they share: a model version that made any
one of them live would have to open the guard, and would then make all seventeen live at once. -/
theorem downstreamRefusals_a12_empty (values : List (List String)) :
    downstreamRefusals (values.map a12TableView) = [] := by
  simp [downstreamRefusals, tableEnumCheckRuns_a12]

/-- The guard is not vacuous in the other direction: one declaration carrying a table name opens it
and every downstream class becomes reachable together. Without this the law above would also hold of a
guard that never opens for anything. -/
theorem downstreamRefusals_open (name : String) (values : List String) :
    downstreamRefusals [{ values := values, tableName := some name }] =
      TableEnumDownstreamRefusal.all := by
  simp [downstreamRefusals, tableEnumCheckRuns, isTableEnumeration]

/-- The two stages partition the downstream vocabulary, so a consumer can tell a code-generation
diagnostic from a file-parser one by class alone. -/
theorem downstream_stage_partition :
    (TableEnumDownstreamRefusal.all.filter (·.stage == .codegenTableCheck)).length = 6 ∧
      (TableEnumDownstreamRefusal.all.filter (·.stage == .csvLoad)).length = 11 ∧
      (TableEnumDownstreamRefusal.all.filter (·.stage == .declaration)).length = 0 := by
  decide

end A12Kernel
