import A12Kernel.Semantics.CheckedEnumeration
import A12Kernel.Semantics.ValueList

/-! # A12Kernel.Semantics.EnumerationValueList — checked token-side bridge

This bridge converts the existing resolved Enumeration operand classification into the existing token-domain value-list cell. It performs no second category lookup or stored-value check.
-/

namespace A12Kernel

/-- Preserve the exact resolved Enumeration classification while changing only the consumer-specific cell vocabulary. -/
def ResolvedEnumerationProjection.asValueListCell
    (projection : ResolvedEnumerationProjection)
    (observation : CellObservation) : ValueListCell .token :=
  match projection.resolveOperand observation with
  | .value token _ => .present token
  | .notEvaluated => .empty
  | .unknown cause => .unknown cause

/-- Value lists consume the shared checked stored/category selection without another wrapper. -/
abbrev CheckedEnumerationValueListOperand := CheckedEnumerationProjection

def checkEnumerationValueListOperand (checked : CheckedEnumerationDeclaration)
    (projectionRef : EnumerationProjectionRef) :
    Except EnumerationOperandError CheckedEnumerationValueListOperand :=
  checkEnumerationProjection checked projectionRef

/-- Check one raw Enumeration value once, then project the resulting validation observation into the token-domain list cell. -/
def CheckedEnumerationValueListOperand.classifyRaw
    (operand : CheckedEnumerationValueListOperand)
    (raw : RawCell) : ValueListCell .token :=
  operand.projection.asValueListCell
    (observeCell .validation (operand.declaration.checkRaw raw))

/-- Build one already-expanded side while retaining the caller-owned tail and `Having` facts. -/
def CheckedEnumerationValueListOperand.classifyRawSide
    (operand : CheckedEnumerationValueListOperand) (rawCells : List RawCell)
    (hasUninstantiatedTail hasHaving : Bool) : ResolvedValueListSide .token :=
  { cells := rawCells.map operand.classifyRaw
    hasUninstantiatedTail
    hasHaving }

end A12Kernel
