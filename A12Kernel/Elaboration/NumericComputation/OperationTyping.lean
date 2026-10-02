import A12Kernel.Elaboration.LiteralComparisonDiagnostic
import A12Kernel.Elaboration.NumericExpression

/-! # The operand typing of a Number computation's operation

A Number computation's operation is typed bottom-up before it is evaluated, and each node's check is
raised where that node closes. The Kernel reads every operand as its bracket closes and judges every
operator when its own production ends, so the first failure in one post-order walk, left subtree before
right and both before their parent, is the class it reports: `{[N] + [S]} - [Nope]` draws the addition's
class while `[S] - [Nope]` draws the unknown name's
([checkpoint](../../../docs/sources/computation-placement-and-constant-probes.md#src-number-operation-typing)).

An operator judges its operands' result types, as [`spec/06`](../../../spec/06-strings-and-enumerations.md)
states for `+`. Addition admits two Numbers or two string-like sides, a concatenation that types as a
String, and refuses a mixed pair; subtraction, multiplication, division and power demand two Numbers;
`Abs` demands a Number; and an extrema call's first operand fixes the family every later operand must
join ([`kf263`](../../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf263)). A well-typed operation whose
result is not a Number then meets the Number target through the comparison every computation generates
([`spec/09`](../../../spec/09-computations.md) §6), so its class is the copied field's arm. Rounding
and a node over an unmeasured shape claim no class.
-/

namespace A12Kernel

/-- The result type one operand or operation contributes to the typing walk. String-like is a String,
including a custom declaration, or an Enumeration without display labels
([`spec/06`](../../../spec/06-strings-and-enumerations.md)); a temporal side keeps its components,
which the extrema compare. -/
inductive NumericOperandType where
  | number
  | stringLike
  | temporal (kind : TemporalKind) (components : TemporalComponents)
  | other (kind : SurfaceScalarKind)
  deriving Repr, DecidableEq

namespace NumericOperandType

/-- The type a declared field contributes. -/
def ofDeclaration (declaration : FlatFieldDecl) : NumericOperandType :=
  match declaration.policy.kind with
  | .number _ => .number
  | .string => .stringLike
  | .enumeration =>
      if (declaration.enumeration.map (·.displayFacts.isEmpty)).getD true then .stringLike
      else .other .enumeration
  | .temporal kind components => .temporal kind components
  | .boolean => .other .boolean
  | .confirm => .other .confirm
  | .dateRange => .other .dateRange

/-- The surface kind the generated comparison sees for a result of this type. -/
def surfaceKind : NumericOperandType → SurfaceScalarKind
  | .number => .number
  | .stringLike => .string
  | .temporal kind _ => .temporal kind
  | .other kind => kind

/-- Whether this type may follow an extrema call led by `leader`, or the class refusing it. -/
def extremaFollower? (leader : NumericOperandType) :
    NumericOperandType → Option KernelStaticDiagnostic
  | follower =>
      match leader, follower with
      | .number, .number => none
      | .number, _ => some .notSortable
      | .temporal _ leading, .temporal _ components =>
          if leading == components then none else some .dateFormatsNotCompatible
      | .temporal _ _, _ => some .dateAndNonDate
      | _, _ => some .notSortable

end NumericOperandType

/-- One typing failure: an operand's own refusal, or a node's class, `none` where the node is one whose
class is not measured. -/
inductive NumericOperationTypingFault (Error : Type) where
  | operand (error : Error)
  | typing (diagnostic : Option KernelStaticDiagnostic)
  deriving Repr, DecidableEq

/-- Judge an extrema call's typed operands, every later one against the first. -/
private def judgeExtrema {Error : Type} (types : List NumericOperandType) :
    Except (NumericOperationTypingFault Error) NumericOperandType :=
  match types with
  | [] => throw (.typing none)
  | leader :: followers =>
      match followers.findSome? leader.extremaFollower? with
      | some diagnostic => throw (.typing (some diagnostic))
      | none => pure leader

/-- One node's typing: its own result type, and the operand types it contributes to an enclosing
extrema call of each operator, a chain of that operator flattened into its operands. Both are kept so
one structural pass serves a node whether or not a call encloses it. -/
private structure NumericNodeTyping (Error : Type) where
  type : Except (NumericOperationTypingFault Error) NumericOperandType
  maximumOperands : Except (NumericOperationTypingFault Error) (List NumericOperandType)
  minimumOperands : Except (NumericOperationTypingFault Error) (List NumericOperandType)

private def NumericNodeTyping.ofType {Error : Type}
    (type : Except (NumericOperationTypingFault Error) NumericOperandType) : NumericNodeTyping Error :=
  { type, maximumOperands := type.map ([·]), minimumOperands := type.map ([·]) }

private def NumericNodeTyping.operands {Error : Type} (node : NumericNodeTyping Error) :
    NumericExtremumOp → Except (NumericOperationTypingFault Error) (List NumericOperandType)
  | .maximum => node.maximumOperands
  | .minimum => node.minimumOperands

private def numberOr {Error : Type} (types : List NumericOperandType)
    (diagnostic : Option KernelStaticDiagnostic) :
    Except (NumericOperationTypingFault Error) NumericOperandType :=
  if types.all (· == .number) then pure .number else throw (.typing diagnostic)

/-- Type every node in post-order, each operand typed by `atomType`. -/
private def typeNumericNode {Atom Error : Type} (atomType : Atom → Except Error NumericOperandType) :
    AuthoredNumericExpr Atom → NumericNodeTyping Error
  | .atom atom => .ofType ((atomType atom).mapError .operand)
  | .literal _ => .ofType (pure .number)
  | .group body => .ofType (typeNumericNode atomType body).type
  | .binary op left right =>
      let leftNode := typeNumericNode atomType left
      let rightNode := typeNumericNode atomType right
      .ofType do
        let leftType ← leftNode.type
        let rightType ← rightNode.type
        match op, leftType, rightType with
        | _, .number, .number => pure .number
        | .add, .stringLike, .stringLike => pure .stringLike
        | .add, _, _ => throw (.typing (some .noStringOrNumberForAdd))
        | _, _, _ => throw (.typing (some .noNumberForCalc))
  | .power base exponent =>
      let baseNode := typeNumericNode atomType base
      let exponentNode := typeNumericNode atomType exponent
      .ofType do numberOr [← baseNode.type, ← exponentNode.type] (some .noNumberForCalc)
  | .abs body =>
      let bodyNode := typeNumericNode atomType body
      .ofType do numberOr [← bodyNode.type] (some .noNumber)
  | .round _ _ body =>
      let bodyNode := typeNumericNode atomType body
      .ofType do numberOr [← bodyNode.type] none
  | .extremum op left right =>
      let leftNode := typeNumericNode atomType left
      let rightNode := typeNumericNode atomType right
      let chain : Except (NumericOperationTypingFault Error) (List NumericOperandType) := do
        pure ((← leftNode.operands op) ++ (← rightNode.operands op))
      let type := chain >>= judgeExtrema
      match op with
      | .maximum => { type, maximumOperands := chain, minimumOperands := type.map ([·]) }
      | .minimum => { type, maximumOperands := type.map ([·]), minimumOperands := chain }
  | .extremumCall op body =>
      .ofType ((typeNumericNode atomType body).operands op >>= judgeExtrema)

/-- Type one operation in post-order: the first failing node's class, or the result type. -/
def typeNumericOperation {Atom Error : Type} (atomType : Atom → Except Error NumericOperandType)
    (expression : AuthoredNumericExpr Atom) :
    Except (NumericOperationTypingFault Error) NumericOperandType :=
  (typeNumericNode atomType expression).type

/-- The class a well-typed operation's result draws against a Number target: the generated comparison's
arm for a copied field of that kind, `none` for a Number. -/
def NumericOperandType.numberTargetDiagnostic? (result : NumericOperandType) :
    Option KernelStaticDiagnostic :=
  (copyComparisonKindArm? .number result.surfaceKind).map (·.diagnostic)

end A12Kernel
