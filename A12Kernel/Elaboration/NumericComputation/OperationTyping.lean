import A12Kernel.Elaboration.LiteralComparisonDiagnostic
import A12Kernel.Elaboration.NumericExpression
import A12Kernel.Semantics.TemporalDistinctCount

/-! # The post-order node check of a Number computation's operation

A Number computation's operation is checked bottom-up before it is evaluated, and each node's check is
raised where that node closes. The Kernel reads every operand as its bracket closes and judges every
operator when its own production ends, so the first failure in one post-order walk, left subtree before
right and both before their parent, is the class it reports: `{[N] + [S]} - [Nope]` draws the addition's
class while `[S] - [Nope]` draws the unknown name's
([checkpoint](../../../docs/sources/computation-placement-and-constant-probes.md#src-number-operation-typing)).

A node first types its operands' results, as [`spec/06`](../../../spec/06-strings-and-enumerations.md)
states for `+`. Addition admits two Numbers or two string-like sides, a concatenation that types as a
String, and refuses a mixed pair; a grouped Enumeration bypasses the direct display-remapping gate
([source-derived boundary](../../../spec/06-strings-and-enumerations.md#part-a--7-strings-and-patterns), externally unverified); subtraction, multiplication, division and power demand two Numbers;
`Abs` demands a Number; and an extrema call's first operand must be sortable and fixes the family
every later operand must join ([`kf263`](../../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf263)). A
well-typed operator or power then asks its own authoring gates, measured in this order
([checkpoint](../../../docs/sources/computation-placement-and-constant-probes.md#src-number-operation-node-gates)):
a power its exponent's derived scale, then every operator and power the shared division walk over its
own subtree, then a power a power directly on its left. A call, a wrapper and a brace ask no gate of
their own ([walk checkpoint](../../../docs/sources/computation-placement-and-constant-probes.md#src-number-operation-division-walk)). A well-typed operation whose result is not a Number then meets the Number target
through the comparison every computation generates ([`spec/09`](../../../spec/09-computations.md) §6),
so its class is the copied field's arm. Rounding over a non-Number and a node over an unmeasured shape
claim no class.
-/

namespace A12Kernel

/-- The result type one operand or operation contributes to the walk. A Number carries its derived
scale, which a power's exponent gate reads. Enumeration retains its selected domain and display
profile until a String-producing operation consumes it ([`spec/06`](../../../spec/06-strings-and-enumerations.md));
a temporal side keeps its components, which the extrema compare. DateRange retains its exact
component set for comparison without BaseYear supplementation (spec/05 §8). -/
inductive NumericOperandType where
  | number (scale : NumericScaleSummary)
  | stringLike
  | enumeration (profile : DirectComparableField) (tokens : List String)
  | temporal (kind : TemporalKind) (components : TemporalComponents)
  | dateRange (components : TemporalComponents)
  | other (kind : SurfaceScalarKind)
  deriving Repr, DecidableEq

namespace NumericOperandType

/-- The type a declared field contributes. -/
def ofDeclaration (declaration : FlatFieldDecl) : NumericOperandType :=
  match declaration.policy.kind with
  | .number info => .number (.field info.scale)
  | .string => .stringLike
  | .enumeration =>
      match declaration.enumeration with
      | some source => .enumeration (.enumeration { facts := source.displayFacts }) source.storedTokens
      | none => .other .enumeration
  | .temporal kind components => .temporal kind components
  | .boolean => .other .boolean
  | .confirm => .other .confirm
  | .dateRange => declaration.toDateRangeDeclarationPolicy?.map
      (fun policy => .dateRange (TemporalComponents.ofFormat policy.format)) |>.getD (.other .dateRange)

/-- The surface kind the generated comparison sees for a result of this type. -/
def surfaceKind : NumericOperandType → SurfaceScalarKind
  | .number _ => .number
  | .stringLike => .string
  | .enumeration .. => .enumeration
  | .temporal kind _ => .temporal kind
  | .dateRange _ => .dateRange
  | .other kind => kind

/-- Whether this type may lead an extrema call: a lone String leader is refused as unsortable just as
one followed by any operand is (rows `Y03`, `Y09` and `Y12` of the
[checkpoint](../../../docs/sources/computation-placement-and-constant-probes.md#src-number-operation-node-gates)). -/
def isSortable : NumericOperandType → Bool
  | .number _ | .temporal _ _ => true
  | .stringLike | .enumeration .. | .dateRange _ | .other _ => false

/-- Whether this type may follow an extrema call led by a sortable `leader`, or the refusing class.
Base Year supplements the compatibility test, not the returned type (CheckEntityListenUtils;
retained date-components capture). -/
def extremaFollower? (leader follower : NumericOperandType) (hasBaseYear : Bool := false) :
    Option KernelStaticDiagnostic :=
  match leader, follower with
  | .number _, .number _ => none
  | .number _, _ => some .notSortable
  | .temporal _ leading, .temporal _ components =>
      if leading.supplementedByBaseYear hasBaseYear == components.supplementedByBaseYear hasBaseYear then
        none else some .dateFormatsNotCompatible
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

/-- Judge an extrema call's closed operands, a sortable first one and every later one against it. -/
private def judgeExtrema {Error : Type} (hasBaseYear : Bool) (operands : List NumericOperandType) :
    Except (NumericOperationNodeFault Error) NumericOperandType :=
  match operands with
  | [] => throw (.node none)
  | leader :: followers =>
      if !leader.isSortable then throw (.node (some .notSortable))
      else
        match followers.findSome? (fun follower => leader.extremaFollower? follower hasBaseYear) with
        | some diagnostic => throw (.node (some diagnostic))
        | none => pure (followers.foldl NumericOperandType.joinExtremum leader)

/-- One node's walk: its own closed result, and the operands it contributes to an enclosing extrema
call of each operator, a chain of that operator flattened into its operands. Both are kept so one
structural pass serves a node whether or not a call encloses it. -/
private structure NumericNodeWalk (Error : Type) where
  result : Except (NumericOperationNodeFault Error) NumericOperandType
  maximumOperands : Except (NumericOperationNodeFault Error) (List NumericOperandType)
  minimumOperands : Except (NumericOperationNodeFault Error) (List NumericOperandType)

private def NumericNodeWalk.ofResult {Error : Type}
    (result : Except (NumericOperationNodeFault Error) NumericOperandType) : NumericNodeWalk Error :=
  { result, maximumOperands := result.map ([·]), minimumOperands := result.map ([·]) }

private def NumericNodeWalk.operands {Error : Type} (node : NumericNodeWalk Error) :
    NumericExtremumOp → Except (NumericOperationNodeFault Error) (List NumericOperandType)
  | .maximum => node.maximumOperands
  | .minimum => node.minimumOperands

/-- The division gate a closed operator or power asks of its own subtree. -/
private def divisionGate {Atom Error : Type} (node : AuthoredNumericExpr Atom) :
    Except (NumericOperationNodeFault Error) Unit :=
  if node.divisionGateRefuses then throw (.node (some .tooManyDivisionsInRegion)) else pure ()

private def isStringAdditionOperand {Atom : Type} (expression : AuthoredNumericExpr Atom) :
    NumericOperandType → Bool
  | .stringLike => true
  | .enumeration profile _ =>
      match profile with
      | .category | .plainString => true
      | .enumeration display => !display.hasEffectiveDisplay || (match expression with | .group _ => true | _ => false)
  | .other .enumeration =>
      -- CheckOperationImpl.checkWithoutDisplayValues inspects only an immediate field read;
      -- grouping exempts this addition gate while retaining the operand's Enumeration type.
      match expression with
      | .group _ => true
      | _ => false
  | _ => false

/-- Walk every node in post-order, each operand typed by `atomType`. -/
private def walkNumericNode {Atom Error : Type} (atomType : Atom → Except Error NumericOperandType)
    (hasBaseYear : Bool) :
    AuthoredNumericExpr Atom → NumericNodeWalk Error
  | .atom atom => .ofResult ((atomType atom).mapError .operand)
  | .literal decoded => .ofResult (pure (.number (.constant decoded.authoredScale)))
  | .group body => .ofResult (walkNumericNode atomType hasBaseYear body).result
  | node@(.binary op left right) =>
      let leftWalk := walkNumericNode atomType hasBaseYear left
      let rightWalk := walkNumericNode atomType hasBaseYear right
      .ofResult do
        let leftType ← leftWalk.result
        let rightType ← rightWalk.result
        let type ← match op, leftType, rightType with
          | _, .number leftScale, .number rightScale =>
              pure (.number (NumericScaleSummary.binary op leftScale rightScale))
          | .add, _, _ =>
              if isStringAdditionOperand left leftType && isStringAdditionOperand right rightType then
                pure .stringLike
              else throw (.node (some .noStringOrNumberForAdd))
          | _, _, _ => throw (.node (some .noNumberForCalc))
        divisionGate node
        pure type
  | node@(.power base exponent) =>
      let baseWalk := walkNumericNode atomType hasBaseYear base
      let exponentWalk := walkNumericNode atomType hasBaseYear exponent
      .ofResult do
        let baseType ← baseWalk.result
        let exponentType ← exponentWalk.result
        match baseType, exponentType with
        | .number baseScale, .number exponentScale =>
            match NumericScaleSummary.power? baseScale exponentScale
                exponent.isSimpleNonnegativeConstant with
            | none => throw (.node (some .exponentScaleNotWhole))
            | some scale =>
                divisionGate node
                -- The exponent's gate answers ahead of the nesting one (rows `c15` and `Y25`).
                if node.directLeftNestedPowerAt then throw (.node (some .nestedPowerOnLeft))
                pure (.number scale)
        | _, _ => throw (.node (some .noNumberForCalc))
  | .abs body =>
      .ofResult do
        match ← (walkNumericNode atomType hasBaseYear body).result with
        | type@(.number _) => pure type
        | _ => throw (.node (some .noNumber))
  | .round _ places body =>
      .ofResult do
        match ← (walkNumericNode atomType hasBaseYear body).result with
        | .number _ => pure (.number (.rounded places.val))
        | _ => throw (.node none)
  | .extremum op left right =>
      let leftWalk := walkNumericNode atomType hasBaseYear left
      let rightWalk := walkNumericNode atomType hasBaseYear right
      let chain : Except (NumericOperationNodeFault Error) (List NumericOperandType) := do
        pure ((← leftWalk.operands op) ++ (← rightWalk.operands op))
      let result := chain >>= judgeExtrema hasBaseYear
      match op with
      | .maximum => { result, maximumOperands := chain, minimumOperands := result.map ([·]) }
      | .minimum => { result, maximumOperands := result.map ([·]), minimumOperands := chain }
  | .extremumCall op body =>
      .ofResult ((walkNumericNode atomType hasBaseYear body).operands op >>= judgeExtrema hasBaseYear)

/-- Check one operation's nodes in post-order: the first failing node's class, or the result type. -/
def checkNumericOperationNodes {Atom Error : Type} (atomType : Atom → Except Error NumericOperandType)
    (expression : AuthoredNumericExpr Atom) (hasBaseYear : Bool := false) :
    Except (NumericOperationNodeFault Error) NumericOperandType :=
  (walkNumericNode atomType hasBaseYear expression).result

/-- The class a well-typed operation's result draws against a Number target: the generated comparison's
arm for a copied field of that kind, `none` for a Number. -/
def NumericOperandType.numberTargetDiagnostic? (result : NumericOperandType) :
    Option KernelStaticDiagnostic :=
  (copyComparisonKindArm? .number result.surfaceKind).map (·.diagnostic)

end A12Kernel
