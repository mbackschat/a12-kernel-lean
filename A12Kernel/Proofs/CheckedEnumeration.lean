import A12Kernel.Elaboration.Flat
import A12Kernel.Proofs.ScalarEquality

/-! # A12Kernel.Proofs.CheckedEnumeration — checked observation laws -/

namespace A12Kernel

@[simp]
theorem checkedEnumeration_empty_is_empty
    (checked : CheckedEnumerationDeclaration) :
    checked.classifyValue (.enum "") = .ok none := by
  simp [CheckedEnumerationDeclaration.classifyValue]

theorem checkedEnumeration_stored_admitted
    (checked : CheckedEnumerationDeclaration) (stored : String)
    (nonempty : stored.isEmpty = false)
    (member : checked.declaration.storedTokens.contains stored = true) :
    checked.classifyValue (.enum stored) = .ok (some (.enum stored)) := by
  have member' : stored ∈ checked.declaration.storedTokens := by simpa using member
  simp [CheckedEnumerationDeclaration.classifyValue, nonempty, member']

theorem checkedEnumeration_stored_rejected
    (checked : CheckedEnumerationDeclaration) (stored : String)
    (nonempty : stored.isEmpty = false)
    (absent : checked.declaration.storedTokens.contains stored = false) :
    checked.classifyValue (.enum stored) = .error .declaredConstraint := by
  have absent' : stored ∉ checked.declaration.storedTokens := by simpa using absent
  simp [CheckedEnumerationDeclaration.classifyValue, nonempty, absent']

/-- A present admitted token reaches the existing resolved evaluator unchanged. -/
theorem checkedEnumeration_evalRaw_present
    (comparison : CheckedEnumerationLiteralComparison) (stored : String)
    (nonempty : stored.isEmpty = false)
    (member : comparison.operand.declaration.declaration.storedTokens.contains stored = true) :
    comparison.evalRaw (.parsed (.enum stored)) =
      comparison.operand.projection.evalLiteral comparison.op
        (.value (.enum stored)) comparison.expected := by
  have member' : stored ∈ comparison.operand.declaration.declaration.storedTokens := by
    simpa using member
  simp [CheckedEnumerationLiteralComparison.evalRaw,
    CheckedEnumerationLiteralComparison.evalCheckedCell,
    CheckedEnumerationDeclaration.checkRaw,
    CheckedEnumerationDeclaration.classifyValue,
    nonempty, member', observeCell]

/-- An out-of-domain stored token stays formal UNKNOWN rather than becoming an ordinary literal mismatch. -/
theorem checkedEnumeration_evalRaw_outOfDomain
    (comparison : CheckedEnumerationLiteralComparison) (stored : String)
    (nonempty : stored.isEmpty = false)
    (absent : comparison.operand.declaration.declaration.storedTokens.contains stored = false) :
    comparison.evalRaw (.parsed (.enum stored)) = .unknown := by
  have absent' : stored ∉ comparison.operand.declaration.declaration.storedTokens := by
    simpa using absent
  simp [CheckedEnumerationLiteralComparison.evalRaw,
    CheckedEnumerationLiteralComparison.evalCheckedCell,
    CheckedEnumerationDeclaration.checkRaw,
    CheckedEnumerationDeclaration.classifyValue,
    nonempty, absent', observeCell,
    ResolvedEnumerationProjection.evalLiteral,
    ResolvedEnumerationProjection.resolveOperand,
    EqualityOp.evalSimple, BaseFormalCause.toFormalCause]

/-- A flat Enumeration declaration delegates raw admission to the exact checked source retained by that declaration. -/
theorem flatEnumeration_checkRaw_exact (declaration : FlatFieldDecl)
    (source : EnumerationDeclaration) (checked : CheckedEnumerationDeclaration)
    (raw : RawCell) (ordinary : declaration.customType = none)
    (kind : declaration.policy.kind = .enumeration)
    (metadata : declaration.enumeration = some source)
    (accepted : elaborateEnumeration source = .ok checked) :
    declaration.checkRaw raw = checked.checkRaw raw := by
  simp [FlatFieldDecl.checkRaw, ordinary, kind, metadata, accepted]

/-- Masking the one Enumeration leaf suppresses its checked comparison before projection or equality evaluation. -/
@[simp]
theorem flatEnumeration_irrelevant_unknown (op : EqualityOp)
    (operand : FlatEnumerationOperand) (expected : String)
    (context : FlatContext) :
    (FlatCondition.compare (.enumeration op operand expected)).evalSelected
      context (fun _ => false) = .unknown := by
  simp [FlatCondition.evalSelected, FlatComparison.allRelevant,
    FlatComparison.fieldIds, FlatComparison.fields, FlatField.id]

/-- Direct String/Enumeration equality is operand-order invariant after both checked field reads have been resolved. -/
theorem flatTextFields_swapped (op : EqualityOp)
    (left right : FlatTextFieldOperand) (context : FlatContext) :
    (FlatComparison.textFields op left right).eval context =
      (FlatComparison.textFields op right left).eval context := by
  simp [FlatComparison.eval, EqualityOp.evalSymmetric_swapped,
    Bool.beq_comm]

end A12Kernel
