import A12Kernel.Elaboration.Enumeration
import A12Kernel.Semantics.Observation

/-! # A12Kernel.Semantics.CheckedEnumeration — checked literal evaluation

This capsule connects one admitted ordinary closed Enumeration declaration to heterogeneous raw-cell checking and the existing stored/category token evaluator. It retains literal admission as a checked construction step; the general flat condition spine consumes the resulting checked projection without adding another Enumeration evaluator.
-/

namespace A12Kernel

inductive EnumerationProjectionRef where
  | stored
  | category (name : String)
  deriving Repr, DecidableEq

inductive EnumerationOperandError where
  | unknownCategory (name : String)
  | invalidLiteral (literal : String)
  deriving Repr, DecidableEq

def CheckedEnumerationDeclaration.resolveProjection
    (checked : CheckedEnumerationDeclaration) :
    EnumerationProjectionRef → Except EnumerationOperandError ResolvedEnumerationProjection
  | .stored => .ok .stored
  | .category name =>
      match checked.categoryProjection? name with
      | some projection => .ok projection
      | none => .error (.unknownCategory name)

/-- Literal membership is checked against the exact selected stored or category domain. -/
def CheckedEnumerationDeclaration.literalAllowed
    (checked : CheckedEnumerationDeclaration)
    (projection : ResolvedEnumerationProjection) (literal : String) : Bool :=
  match projection with
  | .stored => checked.declaration.storedTokens.contains literal
  | .category mapping => mapping.categoryTokens.contains literal

inductive EnumerationLiteralAdmission where
  | accepted (projection : ResolvedEnumerationProjection)
  | rejected (error : EnumerationOperandError)
  deriving Repr, DecidableEq

/-- Classify exact category resolution before checking the selected literal domain. Equality and inequality share this admission boundary. -/
def classifyEnumerationLiteral (checked : CheckedEnumerationDeclaration)
    (projectionRef : EnumerationProjectionRef) (_op : EqualityOp)
    (literal : String) : EnumerationLiteralAdmission :=
  match checked.resolveProjection projectionRef with
  | .error error => .rejected error
  | .ok projection =>
      if checked.literalAllowed projection literal then .accepted projection
      else .rejected (.invalidLiteral literal)

/-- One checked stored/category selection shared by literal, value-list, and repetition-key consumers. -/
structure CheckedEnumerationProjection where
  declaration : CheckedEnumerationDeclaration
  projectionRef : EnumerationProjectionRef
  projection : ResolvedEnumerationProjection
  projectionChecked : declaration.resolveProjection projectionRef = .ok projection

def checkEnumerationProjection (checked : CheckedEnumerationDeclaration)
    (projectionRef : EnumerationProjectionRef) :
    Except EnumerationOperandError CheckedEnumerationProjection :=
  match resolved : checked.resolveProjection projectionRef with
  | .error error => .error error
  | .ok projection =>
      .ok {
        declaration := checked
        projectionRef
        projection
        projectionChecked := resolved }

/-- A proof-bearing direct Enumeration/category comparison with an admitted literal. -/
structure CheckedEnumerationLiteralComparison where
  operand : CheckedEnumerationProjection
  op : EqualityOp
  expected : String
  literalChecked : operand.declaration.literalAllowed operand.projection expected = true

def checkEnumerationLiteralComparison (checked : CheckedEnumerationDeclaration)
    (projectionRef : EnumerationProjectionRef) (op : EqualityOp)
    (literal : String) :
    Except EnumerationOperandError CheckedEnumerationLiteralComparison :=
  match checkEnumerationProjection checked projectionRef with
  | .error error => .error error
  | .ok operand =>
      if allowed : operand.declaration.literalAllowed operand.projection literal = true then
        .ok {
          operand
          op
          expected := literal
          literalChecked := allowed }
      else
        .error (.invalidLiteral literal)

/-- Admit one parsed Enumeration value against the checked stored-token domain. Empty stays empty; an out-of-domain stored token is the declaration's formal constraint failure. -/
def CheckedEnumerationDeclaration.classifyValue
    (checked : CheckedEnumerationDeclaration) :
    Value → Except BaseFormalCause (Option Value)
  | .enum stored =>
      if stored.isEmpty then
        .ok none
      else if checked.declaration.storedTokens.contains stored then
        .ok (some (.enum stored))
      else
        .error .declaredConstraint
  | _ => .error .malformed

def CheckedEnumerationDeclaration.checkRaw
    (checked : CheckedEnumerationDeclaration) (raw : RawCell) : CheckedCell :=
  checkRawCellWith checked.classifyValue raw

/-- Evaluate one checked cell through the already-resolved stored/category literal semantics. -/
def CheckedEnumerationLiteralComparison.evalCheckedCell
    (comparison : CheckedEnumerationLiteralComparison)
    (cell : CheckedCell) : Verdict :=
  comparison.operand.projection.evalLiteral comparison.op
    (observeCell .validation cell) comparison.expected

/-- Convenience boundary joining raw admission and literal evaluation without changing either owner. -/
def CheckedEnumerationLiteralComparison.evalRaw
    (comparison : CheckedEnumerationLiteralComparison) (raw : RawCell) : Verdict :=
  comparison.evalCheckedCell (comparison.operand.declaration.checkRaw raw)

end A12Kernel
