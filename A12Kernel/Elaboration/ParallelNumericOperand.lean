import A12Kernel.Elaboration.ParallelNumericGuard
import A12Kernel.Elaboration.ParallelComputationClearing

/-! Parallel numeric operands retain the ordinary typed atoms and evaluator. The join supplies
field carriers; each atom's existing fold still owns empty substitution and poison (spec/09 §5). -/
namespace A12Kernel

inductive ParallelNumericDirectPlanError where
  | route (error : ParallelComputationPlanError)
  | guardNotLimitedToOperand
  | expressionResolve (error : ResolveError)
  | expressionNotLimitedToOperand
  | unsupportedExpression
  | authoring (result : NumericAuthoringCheck)
  | operandFrameOutsideTarget (scope : List RepeatableLevel)
  | operationScaleMismatch
      (targetScale : Nat) (operation : NumericScaleSummary)
  deriving Repr, DecidableEq

/-- A declaration whose repeatable scope is bound by the target row needs no index join. Model
identity is retained, and the complete operation separately excludes the target itself (spec/09 §1). -/
def CheckedParallelTargetJoin.admitsBoundDeclaration
    (join : CheckedParallelTargetJoin model) (declaration : FlatFieldDecl) : Bool :=
  match model.lookupUniqueId declaration.id with
  | .ok admitted => admitted == declaration &&
      declaration.repeatableScope.isPrefixOf join.targetDeclaration.repeatableScope
  | .error _ => false

/-- A presence guard can read a model-owned field from the target environment or the route's matched environment. Presence remains kind-neutral, as on the ordinary condition route. -/
def CheckedParallelTargetJoin.admitsGuardField
    (join : CheckedParallelTargetJoin model)
    (field : FieldId) : Bool :=
  match model.lookupUniqueId field with
  | .ok declaration =>
      join.admitsBoundDeclaration declaration ||
        (declaration.repeatableScope == join.sourceDeclaration.repeatableScope &&
          join.groups.rightGroup.path.isPrefixOf declaration.groupPath)
  | .error _ => false

/-- Preserve the original Number-specialized admission surface as the kind-neutral route projection. -/
def CheckedParallelNumericClearingPlan.admitsGuardField
    (route : CheckedParallelNumericClearingPlan model)
    (field : FieldId) : Bool :=
  route.asTargetRoute.join.admitsGuardField field

def parallelNumericGuardFields (condition : Option (ParallelNumericGuard model)) : List FieldId :=
  model.fields.filterMap fun declaration =>
    if condition.any (·.readsField declaration.id) then some declaration.id else none

/-- Admit one expression field exactly when it is a model-owned Number declaration addressable from the route's observed-group environment. Nested nonrepeatable groups remain legal; another repeatable or indexed scope does not. -/
def CheckedParallelNumericTargetRoute.admitsExpressionDeclaration
    (route : CheckedParallelNumericTargetRoute model)
    (declaration : FlatFieldDecl) : Bool :=
  match model.lookupUniqueId declaration.id with
  | .ok admitted =>
      admitted == declaration &&
        declaration.toNumberField?.isSome &&
        declaration.repeatableScope ==
          route.sourceDeclaration.repeatableScope &&
        route.groups.rightGroup.path.isPrefixOf declaration.groupPath
  | .error _ => false

def CheckedParallelNumericClearingPlan.admitsExpressionDeclaration
    (route : CheckedParallelNumericClearingPlan model)
    (declaration : FlatFieldDecl) : Bool :=
  route.asTargetRoute.admitsExpressionDeclaration declaration


/-- Addressability is checked independently of each numeric atom's kind and scale. -/
def parallelNumericDeclarationAdmitted (routes : List (CheckedParallelNumericTargetRoute model))
    (declaration : FlatFieldDecl) : Bool :=
  (model.lookupUniqueId declaration.id).toOption == some declaration &&
    routes.any (·.join.admitsGuardField declaration.id)

def parallelNumericAtomAdmitted (routes : List (CheckedParallelNumericTargetRoute model)) :
    NumericComputationAtom → Bool
  | .field declaration => parallelNumericDeclarationAdmitted routes declaration && declaration.toNumberField?.isSome
  | .temporalFieldPart source part format =>
      (model.lookupUniqueId source.id).toOption.any (fun declaration =>
        parallelNumericDeclarationAdmitted routes declaration && declaration.toTemporalField? == some source &&
          declaration.admitsTemporalPartPrecision part) && model.admitsTemporalNumericPart source part format
  | .aggregate _ source => source.hasMultipleFields && source.hasUniqueFields &&
      source.fields.all (fun field => (model.lookupUniqueId field.id).toOption.any (fun declaration =>
        parallelNumericDeclarationAdmitted routes declaration && declaration.toNumberField? == some field))
  | _ => false

/-- One atom of a joined Number operation. A joined atom reads the joined row's cells through the
route machinery; an ordinary atom, such as a starred aggregate, is checked against the model at the
target row and evaluated there, which is what the Kernel's values show for a star spanning the
partner group (joined-carrier capture, row `j11`, 2026-10-14). -/
inductive ParallelNumericOperationAtomOf (Joined : Type) (model : FlatModel) where
  | joined (atom : Joined)
  | ordinary (atom : CheckedNumericComputationAtom model)

abbrev ParallelNumericOperationAtom (model : FlatModel) :=
  ParallelNumericOperationAtomOf NumericComputationAtom model

namespace ParallelNumericOperationAtomOf

def joined? : ParallelNumericOperationAtomOf Joined model → Option Joined
  | .joined atom => some atom
  | .ordinary _ => none

end ParallelNumericOperationAtomOf

namespace ParallelNumericOperationAtom

def referencesField (field : FieldId) : ParallelNumericOperationAtom model → Bool
  | .joined atom => atom.referencesField model field
  | .ordinary atom => atom.references model field

/-- A filter's read inventory is no target ban, as on the ordinary carrier. -/
def forbidsTarget (field : FieldId) : ParallelNumericOperationAtom model → Bool
  | .joined atom => atom.referencesField model field
  | .ordinary atom => atom.forbidsTarget model field

def requiresProducer (consumer producer : FieldId) (protectedGroup : ResolvedGroupReference → Bool) :
    ParallelNumericOperationAtom model → Bool
  | .joined atom => atom.referencesField model producer
  | .ordinary atom => atom.requiresProducer model consumer producer protectedGroup

def scaleSummary : ParallelNumericOperationAtom model → NumericScaleSummary
  | .joined atom => ResolvedNumericAtom.summary FlatFieldDecl.numericScaleSummary atom
  | .ordinary atom => atom.numericScaleSummary

def numericComputationFault? : ParallelNumericOperationAtom model → Option NumericComputationFault
  | .joined atom => NumericComputationAtom.numericComputationFault? atom
  | .ordinary atom => atom.numericComputationFault?

/-- A joined atom reads the joined cells, an ordinary one the document at the target row. -/
def read (context : ParallelNumericGuardContext) : ParallelNumericOperationAtom model →
    Except NumericComputationFault NumericComputationResult
  | .joined atom => context.joinedScalar.readNumericComputationAtom atom
  | .ordinary atom => context.ordinary.readCheckedNumericComputationAtom atom

end ParallelNumericOperationAtom

/-- A joined atom meets the route admission; an ordinary one was checked against the model at the
target row and needs no route. -/
def parallelNumericOperationAtomAdmitted (routes : List (CheckedParallelNumericTargetRoute model)) :
    ParallelNumericOperationAtom model → Bool
  | .joined atom => parallelNumericAtomAdmitted routes atom
  | .ordinary _ => true

/-- Whether every cell the guard reads belongs to one statically participating checked route. -/
def parallelNumericDirectGuardAdmitted
    (joins : List (CheckedParallelTargetJoin model)) :
    Option (ParallelNumericGuard model) → Bool
  | none => true
  | some guard => guard.admitted fun field => joins.any (·.admitsGuardField field)

/-- Only authored direct fields participate here; a wildcard would need its own extent. -/
def SurfaceNumericAtom.parallelFields : SurfaceNumericAtom → List SurfaceFieldPath
  | .field path | .temporalFieldPart path _ => [path]
  | .aggregate _ source => source.first :: source.rest
  | _ => []

/-- Preserve the shared entity-list arity and direct-field order when entering the parallel route. -/
def SurfaceNumericComputationAtom.parallelAtom? : SurfaceNumericComputationAtom → Option SurfaceNumericAtom
  | .numeric (.field path) => some (.field path)
  | .numeric (.temporalFieldPart path part) => some (.temporalFieldPart path part)
  | .numeric (.aggregate op source) => do
      let paths ← (source.first :: source.rest).mapM fun
        | .field path .stored => some path
        | _ => none
      match paths with
      | first :: rest => some (.aggregate op { first, rest })
      | [] => none
  | _ => none

/-- Name resolution retains computation group-read precedence; route certification supplies the
otherwise-unbound indexed scope without changing the model or its declaration scopes. -/
def FlatModel.resolveParallelNumericDeclaration (model : FlatModel)
    (group targetGroup : GroupPath) (path : SurfaceFieldPath) :
    Except ParallelNumericDirectPlanError FlatFieldDecl := do
  let declaration ← (displaceGroupRead
    (model.resolveFieldDeclarationUnchecked group path)
    (model.computationGroupRead group targetGroup path)).mapError .expressionResolve
  if let some refusal := declaration.fieldValueReadRefusal? then throw (.expressionResolve refusal)
  pure declaration

def FlatModel.resolveParallelNumericAtom (model : FlatModel) (group targetGroup : GroupPath) :
    SurfaceNumericAtom → Except ParallelNumericDirectPlanError NumericComputationAtom
  | .field path => do
      let declaration ← model.resolveParallelNumericDeclaration group targetGroup path
      if !declaration.toNumberField?.isSome then throw (.route (.operandNotNumber declaration.path))
      pure (.field declaration)
  | .temporalFieldPart path part => do
      let declaration ← model.resolveParallelNumericDeclaration group targetGroup path
      let some source := declaration.toTemporalField? | throw .unsupportedExpression
      let format := model.temporalNumericPartialFormat source.id
      if !declaration.admitsTemporalPartPrecision part || !model.admitsTemporalNumericPart source part format then
        throw .unsupportedExpression
      pure (.temporalFieldPart source part format)
  | .aggregate op source => do
      let fields ← (source.first :: source.rest).mapM fun path => do
        let declaration ← model.resolveParallelNumericDeclaration group targetGroup path
        let some field := declaration.toNumberField? | throw (.route (.operandNotNumber declaration.path))
        pure field
      match fields with
      | first :: rest =>
          let resolved : ResolvedNumericAggregateFields := { first, rest }
          if !resolved.hasMultipleFields || !resolved.hasUniqueFields then throw .unsupportedExpression
          pure (.aggregate op resolved)
      | [] => throw .unsupportedExpression
  | _ => throw .unsupportedExpression

end A12Kernel
