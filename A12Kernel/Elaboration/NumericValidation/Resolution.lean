import A12Kernel.Elaboration.NumericValidation.Ordered

/-! # Numeric-validation source resolution

This module resolves surface numeric operands against a validated flat model and builds
the checked comparison carriers owned by `NumericValidation.Core`. Runtime evaluation
remains in `NumericValidation.Evaluation`.
-/

namespace A12Kernel

private def resolveTemporalNumericField (model : FlatModel) (rowGroup : GroupPath)
    (reference : SurfaceFieldPath) (accepts : FlatTemporalField → Bool) :
    Except NumericValidationElabError FlatTemporalField := do
  let declaration ← (model.resolveField rowGroup reference).mapError .resolve
  if declaration.groupPath != rowGroup then
    throw (.fieldOutsideRowGroup declaration.path rowGroup)
  match declaration.toTemporalField? with
  | some field =>
      if accepts field then pure field
      else throw (.incompatibleTemporalSource declaration.path)
  | none => throw (.incompatibleTemporalSource declaration.path)

private def resolveDateDifferenceOperandWith
    (model : FlatModel)
    (resolveField : SurfaceFieldPath →
      Except NumericValidationElabError FlatTemporalField) :
    SurfaceDateDifferenceOperand →
      Except NumericValidationElabError ResolvedDateDifferenceOperand
  | .field reference => return .field (← resolveField reference)
  | .baseYear source =>
      match model.baseYear with
      | some year => pure (.baseYear year source)
      | none => throw .baseYearNotDeclared
  | .now => throw .incompatibleDateDifference

private def FlatModel.ensureNumericAggregateRowGroup (model : FlatModel)
    (rowGroup : GroupPath) :
    List FlatNumberField → Except NumericValidationElabError Unit
  | [] => pure ()
  | field :: remaining =>
      match model.lookupUniqueId field.id with
      | .error _ => throw .incoherentCore
      | .ok declaration => do
          if declaration.groupPath != rowGroup then
            throw (.fieldOutsideRowGroup declaration.path rowGroup)
          model.ensureNumericAggregateRowGroup rowGroup remaining

private def NumericValidationElabError.ofFixedGroupReferenceError :
    FixedGroupReferenceError → NumericValidationElabError
  | .reference error => .groupReference error
  | .unknownGroup path => .unknownGroupInCount path
  | .repeatableGroupRequiresAddress path =>
      .repeatableGroupCountRequiresStar path

private def resolveFieldValueAsNumberAtom
    (declaration : FlatFieldDecl) (projectionRef : EnumerationProjectionRef) :
    Except NumericValidationElabError NumericValidationAtom :=
  match declaration.resolveFieldValueAsNumberSource projectionRef with
  | .ok source => pure (.fieldValueAsNumber source)
  | .error .notConvertible =>
      throw (.fieldValueAsNumberNotConvertible declaration.path)
  | .error (.enumeration error) =>
      throw (.fieldValueAsNumberEnumeration declaration.path error)
  | .error .incoherentEnumeration => throw .incoherentCore

private def resolveNumericAtom (model : FlatModel) (rowGroup : GroupPath) :
    SurfaceNumericAtom → Except NumericValidationElabError NumericValidationAtom
  | .field reference => do
      let declaration ←
        (model.resolveField rowGroup reference).mapError .resolve
      if declaration.groupPath != rowGroup then
        throw (.fieldOutsideRowGroup declaration.path rowGroup)
      match declaration.toNumberField? with
      | some field => pure (.field field)
      | none => throw (.fieldNotNumber declaration.path)
  | .baseYear =>
      match model.baseYear with
      | some year => pure (.baseYear year)
      | none => throw .baseYearNotDeclared
  | .baseYearDatePart source part =>
      match model.baseYear with
      | some year => pure (.baseYearDatePart year source part)
      | none => throw .baseYearNotDeclared
  | .temporalFieldPart reference part => do
      let field ← resolveTemporalNumericField model rowGroup reference
        (fun source => part.admittedBy source model.hasBaseYear)
      pure (.temporalFieldPart field part)
  | .stringLength reference => do
      let declaration ← (model.resolveField rowGroup reference).mapError .resolve
      if declaration.groupPath != rowGroup then
        throw (.fieldOutsideRowGroup declaration.path rowGroup)
      match declaration.toStringValueField? with
      | some field => pure (.stringLength field)
      | none => throw (.lengthOperandNotEvaluatedString declaration.path)
  | .stringRange reference start finish => do
      let declaration ← (model.resolveField rowGroup reference).mapError .resolve
      if declaration.groupPath != rowGroup then
        throw (.fieldOutsideRowGroup declaration.path rowGroup)
      if !validStringRange start finish then
        throw (.invalidStringRange start finish)
      match declaration.toStringValueField? with
      | some field => pure (.stringRange field start finish)
      | none => throw (.rangeOperandNotString declaration.path)
  | .fieldValueAsNumber surface => do
      let declaration ←
        (model.resolveField rowGroup surface.reference).mapError .resolve
      if declaration.groupPath != rowGroup then
        throw (.fieldOutsideRowGroup declaration.path rowGroup)
      resolveFieldValueAsNumberAtom declaration surface.projectionRef
  | .dateDifference unit left right => do
      let resolveOperand := resolveDateDifferenceOperandWith model
        (fun reference =>
          resolveTemporalNumericField model rowGroup reference
            (fun source => source.kind == .date &&
              unit.admittedBy model.hasBaseYear source.components))
      let resolvedLeft ← resolveOperand left
      let resolvedRight ← resolveOperand right
      if unit.compatible model.hasBaseYear
          resolvedLeft.components resolvedRight.components then
        pure (.dateDifference unit resolvedLeft resolvedRight)
      else
        throw .incompatibleDateDifference
  | .dateTimeDifference unit left right => do
      let resolveOperand (reference : SurfaceDateDifferenceOperand) :
          Except NumericValidationElabError FlatTemporalOperand :=
        match reference with
        | .baseYear _ => throw .incompatibleDateDifference
        | .now => pure .nowValue
        | .field path => do
            let field ← resolveTemporalNumericField model rowGroup path
              (fun source =>
                source.kind == .dateTime &&
                  unit.admittedBy source.components)
            pure (.fieldValue field)
      let resolvedLeft ← resolveOperand left
      let resolvedRight ← resolveOperand right
      match resolvedLeft.dateTimeDifferenceComponents?,
          resolvedRight.dateTimeDifferenceComponents? with
      | some leftComponents, some rightComponents =>
          if unit.compatible leftComponents rightComponents then
            pure (.dateTimeDifference unit resolvedLeft resolvedRight)
          else
            throw .incompatibleDateDifference
      | _, _ => throw .incompatibleDateDifference
  | .dayDifference left right => do
      let profile ← match ModelZone.ConcreteProfile.ofId? model.timeZoneId with
        | some profile => pure profile
        | none => throw (.unsupportedCalendarProfile model.timeZoneId)
      let resolveOperand := resolveDateDifferenceOperandWith model
        (fun reference =>
          resolveTemporalNumericField model rowGroup reference
            (fun source =>
              CalendarDayDifference.admittedBy
                source.kind source.components))
      let resolvedLeft ← resolveOperand left
      let resolvedRight ← resolveOperand right
      if CalendarDayDifference.yearCompatible model.hasBaseYear
          resolvedLeft.components resolvedRight.components then
        pure (.dayDifference profile resolvedLeft resolvedRight)
      else
        throw .incompatibleDateDifference
  | .aggregate op source => do
      let checked ← (elaborateNumericAggregateFields model rowGroup source).mapError
        NumericValidationElabError.aggregate
      model.ensureNumericAggregateRowGroup rowGroup checked.fields
      pure (.aggregate op checked.resolvedFields)
  | .filledGroupCount surfaces => do
      let groups ← model.resolveFixedGroupReferences rowGroup surfaces
        |>.mapError NumericValidationElabError.ofFixedGroupReferenceError
      if groups.length < 2 then
        throw .groupCountNeedsMultipleOperands
      match ResolvedGroupReferences.firstOverlap? groups with
      | some (left, right) =>
          throw (.overlappingGroupCountOperands left right)
      | none =>
          match groups.find? ResolvedGroupReference.isRoot with
          | some root => throw (.rootGroupInGroupCount root.path)
          | none => pure (.filledGroupCount groups)

private def resolveAddressedNumericDeclaration (model : FlatModel)
    (rowGroup : GroupPath) (reference : SurfaceFieldPath) :
    Except NumericValidationElabError FlatFieldDecl := do
  let declaration ←
    (model.resolveFieldDeclarationUnchecked rowGroup reference).mapError .resolve
  if !declaration.repeatableScope.isPrefixOf
      (model.repeatableScopeForGroupPath rowGroup) then
    throw (.fieldOutsideRowGroup declaration.path rowGroup)
  pure declaration

private def resolveAddressedNumericAtom (model : FlatModel)
    (rowGroup : GroupPath) :
    SurfaceNumericAtom → Except NumericValidationElabError NumericValidationAtom
  | .field reference => do
      let declaration ←
        resolveAddressedNumericDeclaration model rowGroup reference
      match declaration.toNumberField? with
      | some field => pure (.field field)
      | none => throw (.fieldNotNumber declaration.path)
  | .temporalFieldPart reference part => do
      let declaration ←
        resolveAddressedNumericDeclaration model rowGroup reference
      match declaration.toTemporalField? with
      | some field =>
          if part.admittedBy field model.hasBaseYear then
            pure (.temporalFieldPart field part)
          else
            throw (.incompatibleTemporalSource declaration.path)
      | none => throw (.incompatibleTemporalSource declaration.path)
  | .stringLength reference => do
      let declaration ←
        resolveAddressedNumericDeclaration model rowGroup reference
      match declaration.toStringValueField? with
      | some field => pure (.stringLength field)
      | none => throw (.lengthOperandNotEvaluatedString declaration.path)
  | .stringRange reference start finish => do
      let declaration ←
        resolveAddressedNumericDeclaration model rowGroup reference
      if !validStringRange start finish then
        throw (.invalidStringRange start finish)
      match declaration.toStringValueField? with
      | some field => pure (.stringRange field start finish)
      | none => throw (.rangeOperandNotString declaration.path)
  | .fieldValueAsNumber surface => do
      let declaration ←
        resolveAddressedNumericDeclaration model rowGroup surface.reference
      resolveFieldValueAsNumberAtom declaration surface.projectionRef
  | .dateDifference unit left right => do
      let resolveOperand := resolveDateDifferenceOperandWith model
        (fun reference => do
          let declaration ←
            resolveAddressedNumericDeclaration model rowGroup reference
          match declaration.toTemporalField? with
          | some field =>
              if field.kind == .date &&
                  unit.admittedBy model.hasBaseYear field.components then
                pure field
              else
                throw (.incompatibleTemporalSource declaration.path)
          | none => throw (.incompatibleTemporalSource declaration.path))
      let resolvedLeft ← resolveOperand left
      let resolvedRight ← resolveOperand right
      if unit.compatible model.hasBaseYear
          resolvedLeft.components resolvedRight.components then
        pure (.dateDifference unit resolvedLeft resolvedRight)
      else
        throw .incompatibleDateDifference
  | .dateTimeDifference unit left right => do
      let resolveOperand (operand : SurfaceDateDifferenceOperand) :
          Except NumericValidationElabError FlatTemporalOperand :=
        match operand with
        | .baseYear _ => throw .incompatibleDateDifference
        | .now => pure .nowValue
        | .field reference => do
            let declaration ←
              resolveAddressedNumericDeclaration model rowGroup reference
            match declaration.toTemporalField? with
            | some field =>
                if field.kind == .dateTime &&
                    unit.admittedBy field.components then
                  pure (.fieldValue field)
                else
                  throw (.incompatibleTemporalSource declaration.path)
            | none => throw (.incompatibleTemporalSource declaration.path)
      let resolvedLeft ← resolveOperand left
      let resolvedRight ← resolveOperand right
      match resolvedLeft.dateTimeDifferenceComponents?,
          resolvedRight.dateTimeDifferenceComponents? with
      | some leftComponents, some rightComponents =>
          if unit.compatible leftComponents rightComponents then
            pure (.dateTimeDifference unit resolvedLeft resolvedRight)
          else
            throw .incompatibleDateDifference
      | _, _ => throw .incompatibleDateDifference
  | .dayDifference left right => do
      let profile ← match ModelZone.ConcreteProfile.ofId? model.timeZoneId with
        | some profile => pure profile
        | none => throw (.unsupportedCalendarProfile model.timeZoneId)
      let resolveOperand := resolveDateDifferenceOperandWith model
        (fun reference => do
          let declaration ←
            resolveAddressedNumericDeclaration model rowGroup reference
          match declaration.toTemporalField? with
          | some field =>
              if CalendarDayDifference.admittedBy
                  field.kind field.components then
                pure field
              else
                throw (.incompatibleTemporalSource declaration.path)
          | none => throw (.incompatibleTemporalSource declaration.path))
      let resolvedLeft ← resolveOperand left
      let resolvedRight ← resolveOperand right
      if CalendarDayDifference.yearCompatible model.hasBaseYear
          resolvedLeft.components resolvedRight.components then
        pure (.dayDifference profile resolvedLeft resolvedRight)
      else
        throw .incompatibleDateDifference
  | source => resolveNumericAtom model rowGroup source

/-- Resolve one ordinary same-group numeric atom through the established validation source boundary. -/
def resolveNumericValidationAtom
    (model : FlatModel) (rowGroup : GroupPath)
    (surface : SurfaceNumericAtom) :
    Except NumericValidationElabError NumericValidationAtom :=
  resolveNumericAtom model rowGroup surface

/-- Resolve and certify one standalone same-group numeric operation. Comparison-only data-dependency and cross-side scale rules do not apply to an operation-valued consumer. -/
def elaborateNumericValidationExpression
    (model : FlatModel) (rowGroup : GroupPath)
    (surface : AuthoredNumericExpr SurfaceNumericAtom) :
    Except NumericValidationElabError
      (CheckedNumericValidationExpression model) := do
  match hModel : model.validate with
  | .error error => throw (.resolve error)
  | .ok () =>
      if !GroupPath.isValid rowGroup then
        throw (.resolve (.invalidRuleGroup rowGroup))
      let core ← surface.mapM
        (resolveNumericValidationAtom model rowGroup)
      if !core.isAdmittedResolvedNumericOperation then
        throw .unsupportedExpression
      match core.numericOperationAuthoringCheck with
      | .accepted => pure ()
      | result => throw (.authoring result)
      if (core.summary? numericValidationSummary).isNone then
        throw .unsupportedExpression
      if hCore :
          NumericValidationExpression.wellFormedInBool
            core model rowGroup .sameGroup = true then
        pure {
          rowGroup
          core
          modelWellFormed := by
            rw [hModel]
            rfl
          wellFormed := hCore
        }
      else
        throw .incoherentCore

private def elaborateNumericComparisonWith
    (model : FlatModel) (rowGroup : GroupPath)
    (scope : NumericOperandScope)
    (resolveAtom : SurfaceNumericAtom →
      Except NumericValidationElabError NumericValidationAtom)
    (surface : SurfaceNumericComparison) :
    Except NumericValidationElabError (CheckedNumericComparison model) := do
  match hModel : model.validate with
  | .error error => throw (.resolve error)
  | .ok () =>
      if !GroupPath.isValid rowGroup then
        throw (.resolve (.invalidRuleGroup rowGroup))
      let left ← surface.left.mapM resolveAtom
      let right ← surface.right.mapM resolveAtom
      if !(left.anyAtom ResolvedNumericAtom.isDataDependent ||
          right.anyAtom ResolvedNumericAtom.isDataDependent) then
        throw .constantExpression
      if !left.isAdmittedResolvedNumericOperation then
        throw .unsupportedExpression
      if !right.isAdmittedResolvedNumericOperation then
        throw .unsupportedExpression
      match left.numericOperationAuthoringCheck with
      | .accepted => pure ()
      | result => throw (.authoring result)
      match right.numericOperationAuthoringCheck with
      | .accepted => pure ()
      | result => throw (.authoring result)
      let leftSummary ← match left.summary? numericValidationSummary with
        | some summary => pure summary
        | none => throw .unsupportedExpression
      let rightSummary ← match right.summary? numericValidationSummary with
        | some summary => pure summary
        | none => throw .unsupportedExpression
      if !surface.op.acceptsScalesWithSuppression
          surface.suppressExactScaleWarning leftSummary rightSummary then
        throw (.exactScaleMismatch leftSummary rightSummary)
      let core : NumericComparison := {
        op := surface.op
        left
        right
        suppressExactScaleWarning := surface.suppressExactScaleWarning }
      if hCore : core.wellFormedInBool model rowGroup scope = true then
        pure {
          rowGroup
          operandScope := scope
          core
          modelWellFormed := by
            rw [hModel]
            rfl
          wellFormed := hCore
        }
      else
        throw .incoherentCore

/-- Resolve and check both nonrepeatable operands before performing their one-pass lowering at evaluation time. -/
def elaborateNumericComparison (model : FlatModel) (rowGroup : GroupPath)
    (surface : SurfaceNumericComparison) :
    Except NumericValidationElabError (CheckedNumericComparison model) :=
  elaborateNumericComparisonWith model rowGroup .sameGroup
    (resolveNumericAtom model rowGroup) surface

/-- Admit ordinary addressed field operands through the existing ordered-numeric carrier. Each atom retains its typed declaration certificates while only repeatable reads change from scalar to addressed. -/
def elaborateRepeatableNumericComparison
    (model : FlatModel) (rowGroup : GroupPath)
    (surface : SurfaceNumericComparison) :
    Except NumericValidationElabError
      (CheckedOrderedNumericComparison model) := do
  let checked ← elaborateNumericComparisonWith model rowGroup
    .sameGroupAddressed (resolveAddressedNumericAtom model rowGroup) surface
  let core : OrderedNumericComparison model := {
    op := checked.core.op
    left := checked.core.left.map .ordinary
    right := checked.core.right.map .ordinary
    suppressExactScaleWarning := checked.core.suppressExactScaleWarning }
  if !core.requiresAddressedValidation then
    throw .unsupportedExpression
  if hCore : core.wellFormedInBool rowGroup .sameGroupAddressed = true then
    pure {
      rowGroup
      operandScope := .sameGroupAddressed
      core
      modelWellFormed := checked.modelWellFormed
      wellFormed := hCore }
  else
    throw .incoherentCore

end A12Kernel
