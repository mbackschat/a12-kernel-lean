import A12Kernel.Elaboration.Enumeration
import A12Kernel.Semantics.Observation

/-! # A12Kernel.Semantics.CheckedEnumeration — checked literal evaluation

This capsule connects one admitted ordinary closed Enumeration declaration to heterogeneous raw-cell checking and the existing stored/category token evaluator. It retains literal admission as a checked construction step and does not add Enumeration to the general flat condition AST.
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

/-- A proof-bearing direct Enumeration/category comparison with an admitted literal. -/
structure CheckedEnumerationLiteralComparison where
  declaration : CheckedEnumerationDeclaration
  projectionRef : EnumerationProjectionRef
  projection : ResolvedEnumerationProjection
  op : EqualityOp
  expected : String
  projectionChecked : declaration.resolveProjection projectionRef = .ok projection
  literalChecked : declaration.literalAllowed projection expected = true

def checkEnumerationLiteralComparison (checked : CheckedEnumerationDeclaration)
    (projectionRef : EnumerationProjectionRef) (op : EqualityOp)
    (literal : String) :
    Except EnumerationOperandError CheckedEnumerationLiteralComparison :=
  match resolved : checked.resolveProjection projectionRef with
  | .error error => .error error
  | .ok projection =>
      if allowed : checked.literalAllowed projection literal = true then
        .ok {
          declaration := checked
          projectionRef
          projection
          op
          expected := literal
          projectionChecked := resolved
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
  comparison.projection.evalLiteral comparison.op
    (observeCell .validation cell) comparison.expected

/-- Convenience boundary joining raw admission and literal evaluation without changing either owner. -/
def CheckedEnumerationLiteralComparison.evalRaw
    (comparison : CheckedEnumerationLiteralComparison) (raw : RawCell) : Verdict :=
  comparison.evalCheckedCell (comparison.declaration.checkRaw raw)

end A12Kernel
