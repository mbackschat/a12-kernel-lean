import A12Kernel.Elaboration.NumericComputation.OperationTyping

namespace A12Kernel

/-- Comparison gates distinguish literal values from an operation's result policy. Grouping
preserves policy and constantness. -/
structure ScalarComparisonOperand where
  type : NumericOperandType
  literal : Option (Sum String Bool) := none

private def ScalarComparisonOperand.booleanLiteral? (source : ScalarComparisonOperand) : Option Bool :=
  source.literal.bind fun | .inr value => some value | _ => none

private def ScalarComparisonOperand.isBooleanResult (source : ScalarComparisonOperand) : Bool :=
  source.type.surfaceKind == .boolean && source.booleanLiteral?.isNone

private def NumericOperandType.isText : NumericOperandType → Bool
  | .stringLike | .enumeration .. => true
  | _ => false

/-- An Enumeration side opposite a written-out value must be one of its tokens; opposite another
operand its display labels decide nothing (kernel 31.1.1). -/
private def checkEnumerationSide (left right : ScalarComparisonOperand) : Except KernelStaticDiagnostic Unit := do
  let .enumeration tokens := left.type | return
  if let some (.inl literal) := right.literal then
    if !tokens.contains literal then throw .invalidStringConstantForEnumComparison

/-- Complete Boolean/Confirm and textual comparison gates after comparison entry. `false`
leaves Number, temporal and DateRange continuation with their existing owners. Constants do not
acquire a Boolean declaration's kind gate; selectors' String results carry no Enumeration domain. -/
def checkScalarComparison (op : SurfaceComparisonOp) (left right : ScalarComparisonOperand) :
    Except KernelStaticDiagnostic Bool := do
  let leftKind := left.type.surfaceKind
  let rightKind := right.type.surfaceKind
  if leftKind == .confirm || rightKind == .confirm then
    let comparable (source : ScalarComparisonOperand) :=
      source.type.surfaceKind == .confirm || source.booleanLiteral? == some true
    if !comparable left || !comparable right ||
        (leftKind == .confirm && rightKind == .confirm && op != .notEqual) then
      throw .invalidCompareToYes
    return true
  if left.isBooleanResult || right.isBooleanResult then
    if leftKind != .boolean || rightKind != .boolean then throw .invalidCompareToYesNo
    return true
  if left.booleanLiteral?.isSome || right.booleanLiteral?.isSome then
    let other := if left.booleanLiteral?.isSome then rightKind else leftKind
    if let some diagnostic := literalComparisonDiagnostic? .booleanLike other then throw diagnostic
    return true
  if (match leftKind, rightKind with | .temporal _, _ | _, .temporal _ | .dateRange, _ | _, .dateRange => true | _, _ => false) then
    return false
  if left.type.isText || right.type.isText then
    if !left.type.isText || !right.type.isText then throw .invalidCompareToEnumOrString
    checkEnumerationSide left right
    checkEnumerationSide right left
    return true
  return false

end A12Kernel
