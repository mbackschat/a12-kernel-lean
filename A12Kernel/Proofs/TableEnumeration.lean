import A12Kernel.Elaboration.TableEnumeration

/-! # Table-enumeration inertness laws

One constant decides the family, and the laws below say exactly what it decides. In an A12 document model the construct's first arm refuses every candidate, so the construct never succeeds, its four later classes are unreachable, and its mirror in the field-value operator never fires. Each is stated separately because a later model version could break them independently.
-/

namespace A12Kernel

/-- No A12 document-model enumeration is a table enumeration. Everything else here follows. -/
@[simp] theorem a12TableView_not_table (values : List String) :
    isTableEnumeration (a12TableView values) = false := by
  rfl

/-- `ValueNotConsistent` refuses every A12 candidate, whatever its parameters, and always with the
same class. The construct is therefore inert rather than merely restricted: no operand, no parameter
list, and no model content makes it succeed. -/
theorem valueNotConsistent_a12_always_refuses (isField hasWildcard : Bool)
    (values : List String) (parameters : List TableConsistencyParameter) :
    valueNotConsistentRefusal
        { isField := isField, hasWildcard := hasWildcard,
          declaration := a12TableView values } parameters =
      some .tableEnumExpected := by
  simp [valueNotConsistentRefusal]

/-- The four classes behind the first arm are unreachable from an A12 model. Stated as one
disequality per class rather than as a set membership, so that a model version making any single
one live breaks exactly the law that named it. -/
theorem valueNotConsistent_a12_unreachable_classes (isField hasWildcard : Bool)
    (values : List String) (parameters : List TableConsistencyParameter)
    (refusal : TableEnumRefusal)
    (h : valueNotConsistentRefusal
        { isField := isField, hasWildcard := hasWildcard,
          declaration := a12TableView values } parameters = some refusal) :
    refusal ≠ .dependentColumnSizeMismatch ∧ refusal ≠ .onlyEnumsAllowed ∧
      refusal ≠ .stringValueNotInColumn ∧ refusal ≠ .enumValuesNotInColumn ∧
      refusal ≠ .invalidTableEnum := by
  rw [valueNotConsistent_a12_always_refuses] at h
  cases h
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
theorem valueNotConsistent_tableEnumExpected_of_nonTable (operand : TableConsistencyOperand)
    (parameters : List TableConsistencyParameter)
    (h : isTableEnumeration operand.declaration = false) :
    valueNotConsistentRefusal operand parameters = some .tableEnumExpected := by
  simp [valueNotConsistentRefusal, h]

/-- An absent dependent column checks nothing rather than refusing, so a table whose column is
missing is silently skipped. A consumer treating an empty column as "no value is allowed" would
refuse every parameter the Kernel admits. -/
theorem parameterValueRefusal_absent_column (parameter : TableConsistencyParameter) (name : String) :
    parameterValueRefusal parameter { name := name, allowedValues := [] } = none := by
  simp [parameterValueRefusal]

end A12Kernel
