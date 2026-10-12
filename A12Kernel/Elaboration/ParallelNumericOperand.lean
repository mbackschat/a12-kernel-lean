import A12Kernel.Elaboration.ComputationNumericGuard
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
def CheckedParallelNumericTargetRoute.admitsBoundDeclaration
    (route : CheckedParallelNumericTargetRoute model) (declaration : FlatFieldDecl) : Bool :=
  match model.lookupUniqueId declaration.id with
  | .ok admitted => admitted == declaration &&
      declaration.repeatableScope.isPrefixOf route.targetDeclaration.repeatableScope
  | .error _ => false

/-- A presence guard can read a model-owned field from the target environment or the route's matched environment. Presence remains kind-neutral, as on the ordinary condition route. -/
def CheckedParallelNumericTargetRoute.admitsGuardField
    (route : CheckedParallelNumericTargetRoute model)
    (field : FieldId) : Bool :=
  match model.lookupUniqueId field with
  | .ok declaration =>
      route.admitsBoundDeclaration declaration ||
        (declaration.repeatableScope == route.sourceDeclaration.repeatableScope &&
          route.groups.rightGroup.path.isPrefixOf declaration.groupPath)
  | .error _ => false

/-- Preserve the original Number-specialized admission surface as the kind-neutral route projection. -/
def CheckedParallelNumericClearingPlan.admitsGuardField
    (route : CheckedParallelNumericClearingPlan model)
    (field : FieldId) : Bool :=
  route.asTargetRoute.admitsGuardField field

def parallelNumericGuardFields (condition : Option (CheckedComputationCondition model)) : List FieldId :=
  model.fields.filterMap fun declaration =>
    if condition.any (·.referencesField declaration.id) then some declaration.id else none

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
    routes.any (·.admitsGuardField declaration.id)

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

/-- Whether every guard leaf belongs to one statically participating checked route. -/
def parallelNumericDirectGuardAdmitted
    (routes : List (CheckedParallelNumericTargetRoute model)) :
    Option (CheckedComputationCondition model) → Bool
  | none => true
  | some condition => referencesOnly condition
where
  referencesOnly : CheckedComputationCondition model → Bool
    | .leaf (.fieldFilled field) | .leaf (.fieldNotFilled field) =>
        routes.any fun route => route.admitsGuardField field
    | .leaf (.numeric comparison) => comparison.admittedWith
        (fun atom => match atom with
          | .numeric (.field declaration) => parallelNumericAtomAdmitted routes (.field declaration)
          | .numeric (.temporalFieldPart source part format) =>
              parallelNumericAtomAdmitted routes (.temporalFieldPart source part format)
          | .numeric (.aggregate op source) => source.directAggregateFields?.any fun fields =>
              parallelNumericAtomAdmitted routes (.aggregate op fields)
          | _ => false)
        CheckedNumericComputationAtom.numericScaleSummary
    | .leaf (.predicate _) | .leaf (.text _) | .leaf (.scalar _) | .leaf (.fieldFill _ _) | .leaf (.groupPresence _ _) => false
    | .and left right | .or left right =>
        referencesOnly left && referencesOnly right

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

/-- Guard aggregates retain the ordinary checked list and scan. Their sibling scopes are bound
by the parallel route certificate, not by a synthetic ordinary target scope (spec/09 §5). -/
def FlatModel.resolveParallelNumericGuardAtom (model : FlatModel) (group targetGroup : GroupPath)
    (atom : SurfaceNumericComputationAtom) :
    Except ParallelNumericDirectPlanError (CheckedNumericComputationAtom model) := do
  let some direct := atom.parallelAtom? | throw .guardNotLimitedToOperand
  match ← model.resolveParallelNumericAtom group targetGroup direct with
  | .field declaration => pure (.numeric (.field declaration))
  | .temporalFieldPart source part format => pure (.numeric (.temporalFieldPart source part format))
  | .aggregate op fields =>
      let operands ← fields.fields.mapM fun field => do
        let declaration ← model.lookupUniqueId field.id |>.mapError .expressionResolve
        pure (ResolvedFieldEntityOperand.field declaration .stored (model := model))
      let first :: rest := operands | throw .unsupportedExpression
      if valid : model.validate.isOk = true then
        if multiple : (EntityListArity.manyRequired.allowsSole || first.isAlreadyMany || !rest.isEmpty) = true then
          if unique : firstDuplicateResolvedEntityOperand? (first :: rest) = none then
            if disjoint : firstResolvedOperandOverlap? (first :: rest) = none then
              let source ← certifyNumberEntityShape model group {
                first, rest, modelWellFormed := valid, arity := .manyRequired
                requiredMultiplicity := multiple, uniqueExactOperands := unique, disjointOperands := disjoint
              } targetGroup |>.mapError fun _ => .unsupportedExpression
              return .numeric (.aggregate op source)
      throw .unsupportedExpression
  | _ => throw .unsupportedExpression

end A12Kernel
