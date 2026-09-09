import A12Kernel.Elaboration.AddressedNumericLeaf

namespace A12Kernel

/-- Source admission retains model-owned fields and structural paths separately. Computation row
    bindings come from the checked target; scalar-only operations keep their existing owners. -/
def CheckedAddressedNumericTarget.admitsRepetitionOperand
    (target : CheckedAddressedNumericTarget model) : NumericComputationAtom → Bool
  | .field declaration =>
      match model.lookupUniqueId declaration.id with
      | .ok owned => owned == declaration && declaration.toNumberField?.isSome &&
          declaration.id != target.targetField &&
          declaration.repetitionBoundBy target.targetDeclaration.repeatableScope
      | .error _ => false
  | .fixedCurrentRepetition reference => reference.scalarRepetitionWellFormedBool model
  | .boundCurrentRepetition source =>
      source.wellFormedIn model target.targetDeclaration.repeatableScope
  | _ => false

abbrev AddressedRepetitionOperand (target : CheckedAddressedNumericTarget model) :=
  { atom : NumericComputationAtom // target.admitsRepetitionOperand atom = true }

private def hasRepetition (expression : AuthoredNumericExpr (AddressedRepetitionOperand target)) : Bool :=
  expression.anyAtom fun atom => match atom.val with
    | .fixedCurrentRepetition _ | .boundCurrentRepetition _ => true
    | _ => false

private def repetitionOperandSummary (atom : AddressedRepetitionOperand target) : NumericScaleSummary :=
  atom.val.summary FlatFieldDecl.numericScaleSummary

inductive AddressedRepetitionComputationElabError where
  | target (cause : AddressedNumericPlacementElabError)
  | source (cause : ResolveError)
  | repetition (cause : FixedGroupReferenceError)
  | unsupportedExpression
  | authoring (result : NumericAuthoringCheck)
  | operationScaleMismatch (targetScale : Nat) (operation : NumericScaleSummary)
  deriving Repr, DecidableEq

/-- One repetition-bearing Number expression. Each atom is certified against the same target;
    the shared expression tree retains authored grouping, literal scale, and evaluation lowering. -/
structure CheckedAddressedRepetitionComputation (model : FlatModel) where
  private mk ::
  target : CheckedAddressedNumericTarget model
  expression : AuthoredNumericExpr (AddressedRepetitionOperand target)
  suppressExactScaleWarning : Bool
  expressionAdmitted : expression.isAdmittedResolvedNumericOperation = true
  authoringAdmitted : expression.numericOperationAuthoringCheck = .accepted
  repetitionPresent : hasRepetition expression = true
  scaleAdmitted : (expression.summary? repetitionOperandSummary).any
    (exactNumericScaleComparisonAllowedWithSuppression suppressExactScaleWarning
      (.field target.targetPolicy.info.scale)) = true

private def resolveRepetitionOperand (target : CheckedAddressedNumericTarget model)
    (surface : SurfaceNumericAtom) :
    Except AddressedRepetitionComputationElabError (AddressedRepetitionOperand target) := do
  let atom ← match surface with
    | .field reference => do
        let declaration ← model.resolveFieldDeclarationUnchecked target.declaringGroup reference
          |>.mapError .source
        pure (.field declaration)
    | .currentRepetition reference =>
        model.resolveNumericCurrentRepetition target.declaringGroup
          target.targetDeclaration.repeatableScope reference |>.mapError .repetition
    | _ => throw .unsupportedExpression
  if admitted : target.admitsRepetitionOperand atom = true then
    pure ⟨atom, admitted⟩
  else throw .unsupportedExpression

def checkAddressedRepetitionComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (expression : AuthoredNumericExpr SurfaceNumericAtom)
    (suppressExactScaleWarning : Bool := false) :
    Except AddressedRepetitionComputationElabError
      (CheckedAddressedRepetitionComputation model) := do
  let target ← checkAddressedNumericTarget model declaringGroup targetField |>.mapError .target
  let resolved ← expression.mapM (resolveRepetitionOperand target)
  if repetitionPresent : hasRepetition resolved = true then
    if expressionAdmitted : resolved.isAdmittedResolvedNumericOperation = true then
      match authoringAdmitted : resolved.numericOperationAuthoringCheck with
      | .accepted =>
          if scaleAdmitted : (resolved.summary? repetitionOperandSummary).any
              (exactNumericScaleComparisonAllowedWithSuppression suppressExactScaleWarning
                (.field target.targetPolicy.info.scale)) = true then
            pure {
              target, expression := resolved, suppressExactScaleWarning
              repetitionPresent, expressionAdmitted, authoringAdmitted, scaleAdmitted }
          else
            match resolved.summary? repetitionOperandSummary with
            | some summary => throw (.operationScaleMismatch target.targetPolicy.info.scale summary)
            | none => throw .unsupportedExpression
      | result => throw (.authoring result)
    else throw .unsupportedExpression
  else throw .unsupportedExpression

/-- Structural coordinates and addressed fields reuse one ordered arithmetic evaluator while
    preserving the addressed source's own error domain. Rejected atom kinds are unconstructible. -/
def AddressedRepetitionOperand.readAt (source : AddressedRepetitionOperand target)
    (read : CellAddr → Except CheckedDocumentError CheckedCell) (environment : Env) :
    Except AddressedNumericLeafFault NumericComputationResult := by
  rcases source with ⟨atom, admitted⟩
  cases atom
  case field declaration =>
    exact do
      let path ← environment.pathForScope declaration.repeatableScope |>.mapError .environment
      let cell ← read { field := declaration.id, path } |>.mapError .sourceRead
      let context : ScalarComputationContext := { read := fun _ => cell }
      context.readNumeric declaration |>.mapError .evaluation
  case fixedCurrentRepetition reference => exact .ok (.value 1)
  case boundCurrentRepetition source =>
    exact (source.coordinateAt environment).map (fun coordinate => .value coordinate)
      |>.mapError .environment
  all_goals simp [CheckedAddressedNumericTarget.admitsRepetitionOperand] at admitted

namespace CheckedAddressedRepetitionComputation

def referencesField (operation : CheckedAddressedRepetitionComputation model)
    (field : FieldId) : Bool :=
  operation.expression.anyAtom fun atom => match atom.val with
    | .field declaration => declaration.id == field
    | _ => false

def evaluateAtEnvironmentWithRead
    (operation : CheckedAddressedRepetitionComputation model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell) (environment : Env) :
    Except AddressedNumericLeafFault NumericComputationResult :=
  operation.expression.lowerForEvaluation.evalComputation (·.readAt read environment)

def executeWithRead (operation : CheckedAddressedRepetitionComputation model)
    (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell) :
    Except AddressedNumericLeafFault (List (SourcedNumericTargetOutcome CellAddr)) :=
  if operation.suppressExactScaleWarning then
    operation.target.executeAtEnvironmentScaleWarningSuppressed input
      (operation.evaluateAtEnvironmentWithRead read)
  else
    operation.target.executeAtEnvironment input (operation.evaluateAtEnvironmentWithRead read)

def execute (operation : CheckedAddressedRepetitionComputation model)
    (input : CheckedDocument model) :
    Except AddressedNumericLeafFault (List (SourcedNumericTargetOutcome CellAddr)) :=
  operation.executeWithRead input input.read

end CheckedAddressedRepetitionComputation
end A12Kernel
