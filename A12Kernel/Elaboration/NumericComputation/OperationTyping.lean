import A12Kernel.Elaboration.LiteralComparisonDiagnostic
import A12Kernel.Elaboration.NumericExpression

/-! # The post-order node check of a Number computation's operation

A Number computation's operation is checked bottom-up before it is evaluated, and each node's check is
raised where that node closes. The Kernel reads every operand as its bracket closes and judges every
operator when its own production ends, so the first failure in one post-order walk, left subtree before
right and both before their parent, is the class it reports: `{[N] + [S]} - [Nope]` draws the addition's
class while `[S] - [Nope]` draws the unknown name's
([checkpoint](../../../docs/sources/computation-placement-and-constant-probes.md#src-number-operation-typing)).

A node first types its operands' results, as [`spec/06`](../../../spec/06-strings-and-enumerations.md)
states for `+`. Addition admits two Numbers or two string-like sides, a concatenation that types as a
String, and refuses a mixed pair; subtraction, multiplication, division and power demand two Numbers;
`Abs` demands a Number; and an extrema call's first operand must be sortable and fixes the family
every later operand must join ([`kf263`](../../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf263)). A
well-typed node then asks its own authoring gates, measured in this order
([checkpoint](../../../docs/sources/computation-placement-and-constant-probes.md#src-number-operation-node-gates)):
a power its exponent's derived scale and then a power directly on its left, and a multiplication or
division the divisions its region exposes. A region crosses `Abs`, rounding and every operand of an
extrema call, which exposes the largest count among its operands, and grouping, addition, subtraction
and power close it. A well-typed operation whose result is not a Number then meets the Number target
through the comparison every computation generates ([`spec/09`](../../../spec/09-computations.md) §6),
so its class is the copied field's arm. Rounding over a non-Number and a node over an unmeasured shape
claim no class.
-/

namespace A12Kernel

/-- The result type one operand or operation contributes to the walk. A Number carries its derived
scale, which a power's exponent gate reads. String-like is a String, including a custom declaration,
or an Enumeration without display labels ([`spec/06`](../../../spec/06-strings-and-enumerations.md));
a temporal side keeps its components, which the extrema compare. -/
inductive NumericOperandType where
  | number (scale : NumericScaleSummary)
  | stringLike
  | temporal (kind : TemporalKind) (components : TemporalComponents)
  | other (kind : SurfaceScalarKind)
  deriving Repr, DecidableEq

namespace NumericOperandType

/-- The type a declared field contributes. -/
def ofDeclaration (declaration : FlatFieldDecl) : NumericOperandType :=
  match declaration.policy.kind with
  | .number info => .number (.field info.scale)
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
  | .number _ => .number
  | .stringLike => .string
  | .temporal kind _ => .temporal kind
  | .other kind => kind

/-- Whether this type may lead an extrema call: a lone String leader is refused as unsortable just as
one followed by any operand is (rows `Y03`, `Y09` and `Y12` of the
[checkpoint](../../../docs/sources/computation-placement-and-constant-probes.md#src-number-operation-node-gates)). -/
def isSortable : NumericOperandType → Bool
  | .number _ | .temporal _ _ => true
  | .stringLike | .other _ => false

/-- Whether this type may follow an extrema call led by a sortable `leader`, or the class refusing
it. -/
def extremaFollower? (leader : NumericOperandType) :
    NumericOperandType → Option KernelStaticDiagnostic
  | follower =>
      match leader, follower with
      | .number _, .number _ => none
      | .number _, _ => some .notSortable
      | .temporal _ leading, .temporal _ components =>
          if leading == components then none else some .dateFormatsNotCompatible
      | .temporal _ _, _ => some .dateAndNonDate
      | _, _ => some .notSortable

/-- An extrema call's result once a follower has joined: Numbers take the union of their scales, as
`AuthoredNumericExpr.summary?` does, and a temporal call keeps its leader. -/
def joinExtremum : NumericOperandType → NumericOperandType → NumericOperandType
  | .number leading, .number scale => .number (leading.union scale)
  | leader, _ => leader

end NumericOperandType

/-- One failure of the walk: an operand's own refusal, or a node's class, `none` where the node is one
whose class is not measured. -/
inductive NumericOperationNodeFault (Error : Type) where
  | operand (error : Error)
  | node (diagnostic : Option KernelStaticDiagnostic)
  deriving Repr, DecidableEq

/-- A closed node: its result type and the divisions it exposes to an enclosing multiplication or
division region. -/
private structure NumericNode where
  type : NumericOperandType
  divisions : Nat

/-- Judge an extrema call's closed operands, a sortable first one and every later one against it. The
call exposes its largest operand's divisions (rows `g1` and `g2`), not their sum (row `c10`). -/
private def judgeExtrema {Error : Type} (operands : List NumericNode) :
    Except (NumericOperationNodeFault Error) NumericNode :=
  match operands with
  | [] => throw (.node none)
  | leader :: followers =>
      if !leader.type.isSortable then throw (.node (some .notSortable))
      else
        match followers.findSome? (leader.type.extremaFollower? ·.type) with
        | some diagnostic => throw (.node (some diagnostic))
        | none =>
            pure {
              type := followers.foldl (fun joined operand => joined.joinExtremum operand.type)
                leader.type
              divisions := followers.foldl (fun most operand => max most operand.divisions)
                leader.divisions }

/-- One node's walk: its own closed result, and the operands it contributes to an enclosing extrema
call of each operator, a chain of that operator flattened into its operands. Both are kept so one
structural pass serves a node whether or not a call encloses it. -/
private structure NumericNodeWalk (Error : Type) where
  result : Except (NumericOperationNodeFault Error) NumericNode
  maximumOperands : Except (NumericOperationNodeFault Error) (List NumericNode)
  minimumOperands : Except (NumericOperationNodeFault Error) (List NumericNode)

private def NumericNodeWalk.ofResult {Error : Type}
    (result : Except (NumericOperationNodeFault Error) NumericNode) : NumericNodeWalk Error :=
  { result, maximumOperands := result.map ([·]), minimumOperands := result.map ([·]) }

private def NumericNodeWalk.operands {Error : Type} (node : NumericNodeWalk Error) :
    NumericExtremumOp → Except (NumericOperationNodeFault Error) (List NumericNode)
  | .maximum => node.maximumOperands
  | .minimum => node.minimumOperands

/-- Walk every node in post-order, each operand typed by `atomType`. -/
private def walkNumericNode {Atom Error : Type} (atomType : Atom → Except Error NumericOperandType) :
    AuthoredNumericExpr Atom → NumericNodeWalk Error
  | .atom atom => .ofResult ((atomType atom).mapError .operand |>.map ({ type := ·, divisions := 0 }))
  | .literal decoded =>
      .ofResult (pure { type := .number (.constant decoded.authoredScale), divisions := 0 })
  | .group body =>
      .ofResult do pure { type := (← (walkNumericNode atomType body).result).type, divisions := 0 }
  | .binary op left right =>
      let leftWalk := walkNumericNode atomType left
      let rightWalk := walkNumericNode atomType right
      .ofResult do
        let leftNode ← leftWalk.result
        let rightNode ← rightWalk.result
        let type ← match op, leftNode.type, rightNode.type with
          | _, .number leftScale, .number rightScale =>
              pure (.number (NumericScaleSummary.binary op leftScale rightScale))
          | .add, .stringLike, .stringLike => pure .stringLike
          | .add, _, _ => throw (.node (some .noStringOrNumberForAdd))
          | _, _, _ => throw (.node (some .noNumberForCalc))
        match op with
        | .add | .subtract => pure { type, divisions := 0 }
        | .multiply | .divide =>
            let divisions :=
              leftNode.divisions + rightNode.divisions + (if op = .divide then 1 else 0)
            if 1 < divisions then throw (.node (some .tooManyDivisionsInRegion))
            pure { type, divisions }
  | .power base exponent =>
      let baseWalk := walkNumericNode atomType base
      let exponentWalk := walkNumericNode atomType exponent
      .ofResult do
        let baseNode ← baseWalk.result
        let exponentNode ← exponentWalk.result
        match baseNode.type, exponentNode.type with
        | .number baseScale, .number exponentScale =>
            match NumericScaleSummary.power? baseScale exponentScale
                exponent.isSimpleNonnegativeConstant with
            | none => throw (.node (some .exponentScaleNotWhole))
            | some scale =>
                -- The exponent's gate answers ahead of the nesting one (rows `c15` and `Y25`).
                if let .power _ _ := base then throw (.node (some .nestedPowerOnLeft))
                pure { type := .number scale, divisions := 0 }
        | _, _ => throw (.node (some .noNumberForCalc))
  | .abs body =>
      let bodyWalk := walkNumericNode atomType body
      .ofResult do
        let bodyNode ← bodyWalk.result
        match bodyNode.type with
        | .number _ => pure bodyNode
        | _ => throw (.node (some .noNumber))
  | .round _ places body =>
      let bodyWalk := walkNumericNode atomType body
      .ofResult do
        let bodyNode ← bodyWalk.result
        match bodyNode.type with
        | .number _ => pure { bodyNode with type := .number (.rounded places.val) }
        | _ => throw (.node none)
  | .extremum op left right =>
      let leftWalk := walkNumericNode atomType left
      let rightWalk := walkNumericNode atomType right
      let chain : Except (NumericOperationNodeFault Error) (List NumericNode) := do
        pure ((← leftWalk.operands op) ++ (← rightWalk.operands op))
      let result := chain >>= judgeExtrema
      match op with
      | .maximum => { result, maximumOperands := chain, minimumOperands := result.map ([·]) }
      | .minimum => { result, maximumOperands := result.map ([·]), minimumOperands := chain }
  | .extremumCall op body =>
      .ofResult ((walkNumericNode atomType body).operands op >>= judgeExtrema)

/-- Check one operation's nodes in post-order: the first failing node's class, or the result type. -/
def checkNumericOperationNodes {Atom Error : Type} (atomType : Atom → Except Error NumericOperandType)
    (expression : AuthoredNumericExpr Atom) :
    Except (NumericOperationNodeFault Error) NumericOperandType :=
  (walkNumericNode atomType expression).result.map (·.type)

/-- The class a well-typed operation's result draws against a Number target: the generated comparison's
arm for a copied field of that kind, `none` for a Number. -/
def NumericOperandType.numberTargetDiagnostic? (result : NumericOperandType) :
    Option KernelStaticDiagnostic :=
  (copyComparisonKindArm? .number result.surfaceKind).map (·.diagnostic)

end A12Kernel
