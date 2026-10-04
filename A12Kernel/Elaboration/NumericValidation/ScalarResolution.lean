import A12Kernel.Elaboration.NumericValidation.Core

/-! # Numeric-validation source resolution

This module resolves surface numeric operands against a validated flat model and builds
the checked comparison carriers owned by `NumericValidation.Core`. Runtime evaluation
remains in `NumericValidation.Evaluation`.
-/

namespace A12Kernel

private def resolveTemporalNumericField (model : FlatModel) (rowGroup writtenGroup : GroupPath)
    (reference : SurfaceFieldPath) (accepts : FlatTemporalField → Bool) :
    Except NumericValidationElabError FlatTemporalField := do
  let declaration ← (model.resolveField rowGroup reference writtenGroup).mapError .resolve
  if declaration.groupPath != rowGroup then
    throw (.fieldOutsideRowGroup declaration.path rowGroup)
  match declaration.toTemporalField? with
  | some field =>
      if accepts field then pure field
      else throw (.incompatibleTemporalSource declaration.path)
  | none => throw (.incompatibleTemporalSource declaration.path)

/-- Scalar and addressed validation resolve declarations under different locus rules but share the same extractor gate and diagnostic split, so the common certification begins only after resolution. -/
private def checkTemporalNumericPartField (model : FlatModel)
    (declaration : FlatFieldDecl) (part : TemporalNumericPart) :
    Except NumericValidationElabError FlatTemporalField :=
  match declaration.toTemporalField? with
  | some field =>
      if part.admittedBy field model.hasBaseYear then
        pure field
      else
        throw (.temporalFieldPartNotExposed declaration.path part
          field.kind field.components)
  | none =>
      throw (.temporalFieldPartSourceNotTemporal declaration.path part)

private def resolveDateDifferenceOperandWith
    (model : FlatModel)
    (resolveField : SurfaceFieldPath →
      Except NumericValidationElabError FlatTemporalField) :
    SurfaceDateDifferenceOperand →
      Except NumericValidationElabError ResolvedDateDifferenceOperand
  | .literal source =>
      if source.valid then pure (.literal source model.baseYearOrDefault)
      else throw .incompatibleDateDifference
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

private def resolveFieldValueAsNumberAtom
    (declaration : FlatFieldDecl) (projectionRef : EnumerationProjectionRef) :
    Except NumericValidationElabError NumericValidationAtom :=
  match declaration.resolveFieldValueAsNumberSource projectionRef with
  | .ok source => pure (.fieldValueAsNumber source)
  | .error error => throw (.fieldValueAsNumberSource declaration.path error)

private def resolveNumericAtom (model : FlatModel) (rowGroup writtenGroup : GroupPath) :
    SurfaceNumericAtom → Except NumericValidationElabError NumericValidationAtom
  | .field reference => do
      let declaration ← (do
        model.validate
        model.resolveFieldValueRead rowGroup reference writtenGroup).mapError .resolve
      if declaration.groupPath != rowGroup then
        throw (.fieldOutsideRowGroup declaration.path rowGroup)
      match declaration.toNumberField? with
      | some field => pure (.field field)
      | none => throw (.fieldNotNumber declaration.path)
  | .baseYear =>
      match model.baseYear with
      | some year => pure (.baseYear year)
      | none => throw .baseYearNotDeclared
  | .currentRepetition path => do
      if let some (group, fieldPath) := model.currentRepetitionNamedField? rowGroup path then
        let _ ← model.resolveFixedGroupReference rowGroup (.path group) (some writtenGroup)
          |>.mapError .currentRepetitionSource
        throw (.currentRepetitionSource (.fieldNamedAsGroup fieldPath))
      let reference ← model.resolveFixedGroupReference rowGroup (.path path) (some writtenGroup)
        |>.mapError .currentRepetitionSource
      pure (.fixedCurrentRepetition reference)
  | .baseYearDatePart source part =>
      match model.baseYear with
      | some year => pure (.baseYearDatePart year source part)
      | none => throw .baseYearNotDeclared
  | .temporalFieldPart reference part => do
      let declaration ←
        (model.resolveField rowGroup reference writtenGroup).mapError .resolve
      if declaration.groupPath != rowGroup then
        throw (.fieldOutsideRowGroup declaration.path rowGroup)
      let field ← checkTemporalNumericPartField model declaration part
      pure (.temporalFieldPart field part)
  | .dateRangeBoundPart reference bound part => do
      let declaration ← (do
        model.validate
        model.resolveEntityRead rowGroup reference writtenGroup).mapError .resolve
      if declaration.groupPath != rowGroup then
        throw (.fieldOutsideRowGroup declaration.path rowGroup)
      let source : FlatDateRangeField := { id := declaration.id }
      if model.exposesDateRangeBoundPart source part then
        pure (.dateRangeBoundPart source bound part)
      else
        throw (.dateRangeBoundPartNotExposed declaration.path part)
  | .stringLength reference => do
      let declaration ← (do
        model.validate
        model.resolveEntityRead rowGroup reference writtenGroup).mapError .resolve
      if declaration.groupPath != rowGroup then
        throw (.fieldOutsideRowGroup declaration.path rowGroup)
      match declaration.toStringValueField? with
      | some field => pure (.stringLength field)
      | none => throw (.lengthOperandNotEvaluatedString declaration.path)
  | .stringRange reference start finish => do
      let declaration ← (do
        model.validate
        model.resolveEntityRead rowGroup reference writtenGroup).mapError .resolve
      if declaration.groupPath != rowGroup then
        throw (.fieldOutsideRowGroup declaration.path rowGroup)
      if !validStringRange start finish then
        throw (.invalidStringRange start finish)
      match declaration.toStringValueField? with
      | some field => pure (.stringRange field start finish)
      | none => throw (.rangeOperandNotString declaration.path)
  | .fieldValueAsNumber surface => do
      let declaration ← (do
        model.validate
        model.resolveEntityRead rowGroup surface.reference writtenGroup).mapError .resolve
      if declaration.groupPath != rowGroup then
        throw (.fieldOutsideRowGroup declaration.path rowGroup)
      resolveFieldValueAsNumberAtom declaration surface.projectionRef
  | .dateDifference unit left right => do
      let resolveOperand := resolveDateDifferenceOperandWith model
        (fun reference =>
          resolveTemporalNumericField model rowGroup writtenGroup reference
            (fun source =>
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
        | .baseYear _ | .literal _ => throw .incompatibleDateDifference
        | .now => pure .nowValue
        | .field path => do
            let field ← resolveTemporalNumericField model rowGroup writtenGroup path
              (fun source => unit.admittedBy source.components)
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
          resolveTemporalNumericField model rowGroup writtenGroup reference
            (fun source =>
              CalendarDayDifference.admittedBy source.components))
      let resolvedLeft ← resolveOperand left
      let resolvedRight ← resolveOperand right
      if CalendarDayDifference.yearCompatible model.hasBaseYear
          resolvedLeft.components resolvedRight.components then
        pure (.dayDifference profile resolvedLeft resolvedRight)
      else
        throw .incompatibleDateDifference
  | .aggregate op source => do
      let checked ← (elaborateNumericAggregateFields model rowGroup source writtenGroup).mapError
        NumericValidationElabError.aggregate
      model.ensureNumericAggregateRowGroup rowGroup checked.fields
      pure (.aggregate op checked.resolvedFields)
  | .filledGroupCount operands => do
      let surfaces ←
        match SurfaceGroupCountOperand.fixedOnly? operands with
        | some surfaces => pure surfaces
        | none =>
            throw (NumericValidationElabError.starredGroupCountOperand
              ((SurfaceGroupCountOperand.firstStarred? operands).getD
                { base := .absolute, groups := [] }))
      -- A lone repeatable group meets the count's arity as a lone fixed group does wherever the
      -- rule's error field lies at or below it and inside the rule group, whichever group declares
      -- the rule, as a root too
      -- ([checkpoint](../../../docs/sources/group-list-and-capacity-probes.md#src-count-placement-by-error-field)).
      -- The arity answers ahead of the refusal such a placement otherwise meets: the rule's row
      -- binding the group, the walk passing it, or an enclosing rule leaving its level unbound. An
      -- error field outside the rule group keeps the resolver's containment class, which the Kernel
      -- raises first.
      let soleArityMeasured (path : GroupPath) : Bool :=
        GroupPath.isPrefixOf path writtenGroup && GroupPath.isPrefixOf rowGroup writtenGroup
      let groups ←
        match model.resolveValidationBoundFixedGroupReferences rowGroup writtenGroup surfaces with
        | .ok groups => pure groups
        | .error (.walkedRepeatableGroupUnsupported path) =>
            if surfaces.length == 1 && soleArityMeasured path then
              throw .groupCountNeedsMultipleOperands
            else throw (.groupReference (.walkedRepeatableGroupUnsupported path))
        | .error (.unboundOperandLevel path unbound) =>
            if surfaces.length == 1 && soleArityMeasured path then
              throw .groupCountNeedsMultipleOperands
            else throw (.groupReference (.unboundOperandLevel path unbound))
        | .error error => throw (.groupReference error)
      if let [sole] := groups then
        if model.repeatableGroups.any (·.path == sole.path) && !soleArityMeasured sole.path then
          throw (.groupReference (.walkedRepeatableGroupUnsupported sole.path))
      if groups.length < 2 then
        throw .groupCountNeedsMultipleOperands
      match ResolvedGroupReferences.firstOverlap? groups with
      | some (left, right) =>
          throw (.overlappingGroupCountOperands left right)
      | none =>
          match groups.find? ResolvedGroupReference.isRoot with
          | some root => throw (.rootGroupInGroupCount root.path)
          | none => pure (.filledGroupCount groups)

/-- Resolve an addressed operand with `resolved`, then refuse a field the row group's scope does not
    cover as this fragment's boundary. -/
private def resolveAddressedNumericDeclaration (model : FlatModel)
    (rowGroup : GroupPath) (reference : SurfaceFieldPath)
    (resolved : Except ResolveError FlatFieldDecl :=
      model.resolveFieldDeclarationUnchecked rowGroup reference) :
    Except NumericValidationElabError FlatFieldDecl := do
  let declaration ← resolved.mapError .resolve
  if !declaration.repeatableScope.isPrefixOf
      (model.repeatableScopeForGroupPath rowGroup) then
    throw (.fieldOutsideRowGroup declaration.path rowGroup)
  pure declaration

/-- The group gate a field read and an operator's field parameter ask first here: a bracket read's value gates follow it,
    while an operator parameter meets its operator's own gates instead
    ([checkpoint](../../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-predictions)). -/
private def addressedEntityResolution (model : FlatModel) (declaringGroup rowGroup : GroupPath)
    (reference : SurfaceFieldPath) : Except ResolveError FlatFieldDecl :=
  displaceGroupRead (model.resolveFieldDeclarationUnchecked declaringGroup reference)
    (model.ruleGroupRead declaringGroup rowGroup reference)

private def resolveAddressedNumericAtomIn (model : FlatModel)
    (declaringGroup rowGroup : GroupPath) :
    SurfaceNumericAtom → Except NumericValidationElabError NumericValidationAtom
  | .currentRepetition reference =>
      model.resolveNumericCurrentRepetition declaringGroup
        (model.repeatableScopeForGroupPath rowGroup) reference
        |>.mapError .currentRepetitionSource
  | .field reference => do
      -- The bracket's group gate answers ahead of this fragment's scope boundary and its value
      -- gates after it, as the walk and then the value gates do on a same-group read.
      let declaration ← resolveAddressedNumericDeclaration model rowGroup reference
        (addressedEntityResolution model declaringGroup rowGroup reference)
      if let some refusal := declaration.fieldValueReadRefusal? then
        throw (.resolve refusal)
      match declaration.toNumberField? with
      | some field => pure (.field field)
      | none => throw (.fieldNotNumber declaration.path)
  | .temporalFieldPart reference part => do
      let declaration ←
        resolveAddressedNumericDeclaration model rowGroup reference
          (model.resolveFieldDeclarationUnchecked declaringGroup reference)
      let field ← checkTemporalNumericPartField model declaration part
      pure (.temporalFieldPart field part)
  | .dateRangeBoundPart reference bound part => do
      let declaration ←
        resolveAddressedNumericDeclaration model rowGroup reference
          (addressedEntityResolution model declaringGroup rowGroup reference)
      let source : FlatDateRangeField := { id := declaration.id }
      if model.exposesDateRangeBoundPart source part then
        pure (.dateRangeBoundPart source bound part)
      else
        throw (.dateRangeBoundPartNotExposed declaration.path part)
  | .stringLength reference => do
      let declaration ←
        resolveAddressedNumericDeclaration model rowGroup reference
          (addressedEntityResolution model declaringGroup rowGroup reference)
      match declaration.toStringValueField? with
      | some field => pure (.stringLength field)
      | none => throw (.lengthOperandNotEvaluatedString declaration.path)
  | .stringRange reference start finish => do
      let declaration ←
        resolveAddressedNumericDeclaration model rowGroup reference
          (addressedEntityResolution model declaringGroup rowGroup reference)
      if !validStringRange start finish then
        throw (.invalidStringRange start finish)
      match declaration.toStringValueField? with
      | some field => pure (.stringRange field start finish)
      | none => throw (.rangeOperandNotString declaration.path)
  | .fieldValueAsNumber surface => do
      let declaration ←
        resolveAddressedNumericDeclaration model rowGroup surface.reference
          (addressedEntityResolution model declaringGroup rowGroup surface.reference)
      resolveFieldValueAsNumberAtom declaration surface.projectionRef
  | .dateDifference unit left right => do
      let resolveOperand := resolveDateDifferenceOperandWith model
        (fun reference => do
          let declaration ←
            resolveAddressedNumericDeclaration model rowGroup reference
              (model.resolveFieldDeclarationUnchecked declaringGroup reference)
          match declaration.toTemporalField? with
          | some field =>
              if unit.admittedBy model.hasBaseYear field.components then
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
        | .baseYear _ | .literal _ => throw .incompatibleDateDifference
        | .now => pure .nowValue
        | .field reference => do
            let declaration ←
              resolveAddressedNumericDeclaration model rowGroup reference
                (model.resolveFieldDeclarationUnchecked declaringGroup reference)
            match declaration.toTemporalField? with
            | some field =>
                if unit.admittedBy field.components then
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
              (model.resolveFieldDeclarationUnchecked declaringGroup reference)
          match declaration.toTemporalField? with
          | some field =>
              if CalendarDayDifference.admittedBy field.components then
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
  | source => resolveNumericAtom model declaringGroup rowGroup source

private def resolveAddressedNumericAtom (model : FlatModel) (rowGroup : GroupPath) :=
  resolveAddressedNumericAtomIn model rowGroup rowGroup

/-- Resolve one ordinary same-group numeric atom through the established validation source boundary. -/
def resolveNumericValidationAtom
    (model : FlatModel) (rowGroup : GroupPath)
    (surface : SurfaceNumericAtom) (writtenGroup : GroupPath := rowGroup) :
    Except NumericValidationElabError NumericValidationAtom :=
  resolveNumericAtom model rowGroup writtenGroup surface

/-- Resolve one ordinary operand of an addressed comparison, the reading
`elaborateRepeatableNumericComparison` gives each of its atoms. -/
def resolveAddressedNumericValidationAtom
    (model : FlatModel) (rowGroup : GroupPath) (surface : SurfaceNumericAtom)
    (declaringGroup : GroupPath := rowGroup) :
    Except NumericValidationElabError NumericValidationAtom :=
  resolveAddressedNumericAtomIn model declaringGroup rowGroup surface

private def elaborateNumericValidationExpressionWith
    (model : FlatModel) (rowGroup : GroupPath)
    (scope : NumericOperandScope)
    (resolveAtom : SurfaceNumericAtom →
      Except NumericValidationElabError NumericValidationAtom)
    (surface : AuthoredNumericExpr SurfaceNumericAtom) :
    Except NumericValidationElabError
      (CheckedNumericValidationExpression model) := do
  match hModel : model.validate with
  | .error error => throw (.resolve error)
  | .ok () =>
      if !GroupPath.isValid rowGroup then
        throw (.resolve (.invalidRuleGroup rowGroup))
      let core ← surface.mapM resolveAtom
      if !core.isAdmittedResolvedNumericOperation then
        throw .unsupportedExpression
      match core.numericOperationAuthoringCheck with
      | .accepted => pure ()
      | result => throw (.authoring result)
      if (core.summary? numericValidationSummary).isNone then
        throw .unsupportedExpression
      if hCore :
          NumericValidationExpression.wellFormedInBool
            core model rowGroup scope = true then
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

/-- Resolve and certify one standalone same-group numeric operation. Comparison-only data-dependency and cross-side scale rules do not apply to an operation-valued consumer. -/
def elaborateNumericValidationExpression
    (model : FlatModel) (rowGroup : GroupPath)
    (surface : AuthoredNumericExpr SurfaceNumericAtom) :
    Except NumericValidationElabError
      (CheckedNumericValidationExpression model) :=
  elaborateNumericValidationExpressionWith model rowGroup .sameGroup
    (resolveNumericValidationAtom model rowGroup) surface

/-- Resolve one standalone numeric operation at a repeatable authoring group. Each direct field may live at that group or an outer scope, while runtime addressing remains a consumer responsibility. -/
def elaborateRepeatableNumericValidationExpression
    (model : FlatModel) (rowGroup : GroupPath)
    (surface : AuthoredNumericExpr SurfaceNumericAtom) (declaringGroup : GroupPath := rowGroup) :
    Except NumericValidationElabError
      (CheckedNumericValidationExpression model) :=
  elaborateNumericValidationExpressionWith model rowGroup .sameGroupAddressed
    (resolveAddressedNumericAtomIn model declaringGroup rowGroup) surface

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
      if left.isImmediateLiteral && right.isImmediateLiteral then
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
    (surface : SurfaceNumericComparison) (writtenGroup : GroupPath := rowGroup) :
    Except NumericValidationElabError (CheckedNumericComparison model) :=
  elaborateNumericComparisonWith model rowGroup .sameGroup
    (resolveNumericAtom model rowGroup writtenGroup) surface

/-- Resolve the scalar numeric core at a bound scope before an addressed consumer chooses its leaf carrier. -/
def elaborateAddressedNumericComparisonCore
    (model : FlatModel) (rowGroup : GroupPath)
    (surface : SurfaceNumericComparison) (declaringGroup : GroupPath := rowGroup) :
    Except NumericValidationElabError (CheckedNumericComparison model) :=
  elaborateNumericComparisonWith model rowGroup .sameGroupAddressed
    (resolveAddressedNumericAtomIn model declaringGroup rowGroup) surface

end A12Kernel
