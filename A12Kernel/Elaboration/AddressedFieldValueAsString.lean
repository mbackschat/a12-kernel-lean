import A12Kernel.Elaboration.StringComputationRunApplication

/-! # Repeatable `FieldValueAsString`

This capsule admits one ordinary repeatable String target whose sole expression is `FieldValueAsString` over a Number declaration whose repetition scope is bound by the target. Execution enumerates physically instantiated target environments, reads the Number at its own scope through the checked document's storage-regime-preserving text boundary, and retains the exact target address through result classification and application.

Other String expressions, sibling or deeper reads, guards, cascades, and scheduling remain separate.
-/

namespace A12Kernel

/-- Fail-closed errors for the bounded repeatable placement. These are library diagnostics, not claims about kernel diagnostic precedence. -/
inductive AddressedFieldValueAsStringElabError where
  | model (cause : ResolveError)
  | target (cause : ResolveError)
  | source (cause : ResolveError)
  | targetOutsideDeclaringGroup (path declaringGroup : GroupPath)
  | targetKindMismatch (path : List String) (actual : SurfaceScalarKind)
  | rawStringTarget (path : List String)
  | customStringTarget (path : List String)
  | enumeratedStringTarget (path : List String)
  | targetNotRepeatable (path : List String)
  | sourceKindMismatch (path : List String) (actual : SurfaceScalarKind)
  | scopeMismatch (target source : List String)
  deriving Repr, DecidableEq

/-- One exact repeatable Number-to-String operation certified against a validated model. -/
structure CheckedAddressedFieldValueAsString (model : FlatModel) where
  private mk ::
  declaringGroup : GroupPath
  sourceReference : SurfaceFieldPath
  targetField : FieldId
  targetDeclaration : FlatFieldDecl
  sourceDeclaration : FlatFieldDecl
  modelWellFormed : model.validate.isOk = true
  targetOwned :
    model.lookupUniqueId targetField = .ok targetDeclaration
  sourceResolved :
    model.resolveFieldDeclarationUnchecked declaringGroup sourceReference =
      .ok sourceDeclaration
  declaringGroupValid : GroupPath.isValid declaringGroup = true
  targetContainedInDeclaringGroup :
    GroupPath.isPrefixOf declaringGroup targetDeclaration.groupPath = true
  targetString :
    targetDeclaration.policy.kind = .string
  targetEvaluated :
    targetDeclaration.stringValueMode = .evaluated
  targetOrdinary :
    targetDeclaration.customType = none
  targetNotEnumerated :
    targetDeclaration.enumeration = none
  sourceNumber :
    ∃ info, sourceDeclaration.policy.kind = .number info
  targetRepeatable : targetDeclaration.repeatableScope ≠ []
  /-- The target's own scope binds every repeatable level the source crosses, so an outer-scope
  source reads once at its own shorter path and reaches every target row. -/
  sourceScopeBound :
    sourceDeclaration.repetitionBoundBy
      targetDeclaration.repeatableScope = true

/-- Validate the exact repeatable placement without widening the existing nonrepeatable String-expression elaborator. -/
def checkAddressedFieldValueAsString
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (sourceReference : SurfaceFieldPath) :
    Except AddressedFieldValueAsStringElabError
      (CheckedAddressedFieldValueAsString model) :=
  match hModel : model.validate with
  | .error cause => .error (.model cause)
  | .ok () =>
    match hTargetOwned : model.lookupUniqueId targetField with
    | .error cause => .error (.target cause)
    | .ok targetDeclaration =>
      if hValid : GroupPath.isValid declaringGroup = true then
        if hGroup : GroupPath.isPrefixOf
            declaringGroup targetDeclaration.groupPath = true then
          match hKind : targetDeclaration.policy.kind with
          | .string =>
            match hMode : targetDeclaration.stringValueMode with
            | .raw => .error (.rawStringTarget targetDeclaration.path)
            | .evaluated =>
              match hCustom : targetDeclaration.customType with
              | some _ =>
                  .error (.customStringTarget targetDeclaration.path)
              | none =>
                match hEnumeration : targetDeclaration.enumeration with
                | some _ =>
                    .error (.enumeratedStringTarget targetDeclaration.path)
                | none =>
                  if hRepeatable :
                      targetDeclaration.repeatableScope.isEmpty then
                    .error (.targetNotRepeatable targetDeclaration.path)
                  else
                    match hSourceResolved :
                        model.resolveFieldDeclarationUnchecked
                          declaringGroup sourceReference with
                    | .error cause => .error (.source cause)
                    | .ok sourceDeclaration =>
                      match hSourceKind :
                          sourceDeclaration.policy.kind with
                      | .number info =>
                        if hScope :
                            sourceDeclaration.repetitionBoundBy
                              targetDeclaration.repeatableScope = true then
                          .ok {
                            declaringGroup
                            sourceReference
                            targetField
                            targetDeclaration
                            sourceDeclaration
                            modelWellFormed := by
                              rw [hModel]
                              rfl
                            targetOwned := hTargetOwned
                            sourceResolved := hSourceResolved
                            declaringGroupValid := hValid
                            targetContainedInDeclaringGroup := hGroup
                            targetString := hKind
                            targetEvaluated := hMode
                            targetOrdinary := hCustom
                            targetNotEnumerated := hEnumeration
                            sourceNumber := ⟨info, hSourceKind⟩
                            targetRepeatable := by
                              intro empty
                              simp [empty] at hRepeatable
                            sourceScopeBound := hScope
                          }
                        else
                          .error (.scopeMismatch
                            targetDeclaration.path sourceDeclaration.path)
                      | actual =>
                          .error (.sourceKindMismatch
                            sourceDeclaration.path actual.surfaceKind)
          | actual =>
              .error (.targetKindMismatch
                targetDeclaration.path actual.surfaceKind)
        else
          .error (.targetOutsideDeclaringGroup
            targetDeclaration.path declaringGroup)
      else
        .error (.target (.invalidRuleGroup declaringGroup))

inductive AddressedFieldValueAsStringFault where
  | targetRows (cause : ActualRowEnvironmentError)
  | environment (cause : EnvBindingError)
  | sourceRead (cause : CheckedDocumentError)
  | evaluation (cause : StringComputationFault)
  deriving Repr, DecidableEq

namespace CheckedAddressedFieldValueAsString

/-- The physically instantiated environments at the operation's exact target scope, over-limit rows included. -/
def targetEnvironments
    (operation : CheckedAddressedFieldValueAsString model)
    (input : CheckedDocument model) :
    Except ActualRowEnvironmentError (List Env) :=
  input.actualRowEnvironments operation.targetDeclaration.repeatableScope

private def stringCell (cell : CheckedCell String) : CheckedCell := {
  rawPresent := cell.rawPresent
  parsed := cell.parsed.map Value.str
  findings := cell.findings
}

/-- Project the immutable Number source through the storage-regime-preserving text boundary consumed by `FieldValueAsString`. -/
def readSource (input : CheckedDocument model) (address : CellAddr) :
    Except CheckedDocumentError CheckedCell := do
  pure (stringCell (← input.readNumberFormalText address))

/-- Execute one addressed instance per physical target environment through a caller-supplied exact-address Number-text view and retain the exact row key. Target iteration and prior-target classification remain owned by the immutable checked document. -/
def executeWithRead (operation : CheckedAddressedFieldValueAsString model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell) :
    Except AddressedFieldValueAsStringFault
      (List (SourcedStringTargetOutcome CellAddr)) := do
  let matcher ← match patterns.targetMatcher? operation.targetField with
    | some matcher => pure matcher
    | none =>
        throw (.evaluation
          (.targetPatternUnavailable operation.targetField))
  let addressAt (environment : Env) : Except AddressedFieldValueAsStringFault CellAddr := do
    let path ←
      (environment.pathForScope
        operation.targetDeclaration.repeatableScope).mapError .environment
    pure { field := operation.targetField, path }
  input.computationRowOutcomes operation.targetDeclaration.repeatableScope .targetRows
    (fun environment => do
      let targetAddress ← addressAt environment
      pure {
        targetField := targetAddress
        outcome := .noValue
        source := input.sourceStringTargetStateAt targetAddress
      })
    (fun environment => do
    let targetAddress ← addressAt environment
    let sourcePath ←
      (environment.pathForScope
        operation.sourceDeclaration.repeatableScope).mapError .environment
    let sourceAddress : CellAddr := {
      field := operation.sourceDeclaration.id
      path := sourcePath
    }
    let sourceCell ← (read sourceAddress).mapError .sourceRead
    let context : StringComputationContext := {
      read := fun field =>
        if field == operation.sourceDeclaration.id then
          sourceCell
        else
          malformedCheckedCell
    }
    let store ←
      ((StringExpr.fieldValueAsString operation.sourceDeclaration.id).evaluate
        context).mapError .evaluation
    pure {
      targetField := targetAddress
      outcome :=
        operation.targetDeclaration.stringPolicy.checkTargetWithPattern
          matcher store
      source := input.sourceStringTargetStateAt targetAddress
    })

/-- Execute through the immutable checked document's Number-text projection. -/
def execute (operation : CheckedAddressedFieldValueAsString model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model) :
    Except AddressedFieldValueAsStringFault
      (List (SourcedStringTargetOutcome CellAddr)) :=
  operation.executeWithRead patterns input (readSource input)

/-- Classify the addressed rich outcomes against the immutable source document without collapsing their exact row keys. -/
def executeResult
    (operation : CheckedAddressedFieldValueAsString model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (residualMessages : List ResidualMessage) :
    Except AddressedFieldValueAsStringFault
      (StringComputationRunView ResidualMessage CellAddr) := do
  let outcomes ← operation.execute patterns input
  pure (StringComputationRunView.fromSourcedOutcomes
    residualMessages outcomes)

end CheckedAddressedFieldValueAsString

end A12Kernel
