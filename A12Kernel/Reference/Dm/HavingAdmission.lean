import A12Kernel.Reference.Dm.LowerHaving
import A12Kernel.Reference.Dm.FilterReferenceInventory

namespace A12Kernel.Dm

mutual
/-- Select the ordered admission route for an entire expression, including earlier operands
and separate argument lists; a filter can also belong to a recursive key (spec/07 §3). -/
partial def Expr.hasHaving : Expr → Bool
  | .entity reference | .value reference => reference.hasHaving
  | .arith _ left right | .compare _ left right => left.hasHaving || right.hasHaving
  | .braces body | .parens body => body.hasHaving
  | .logic _ parts => parts.any Expr.hasHaving
  | .call _ arguments listed scope =>
      arguments.any Argument.hasHaving || (listed.getD []).any Argument.hasHaving ||
        scope.any Reference.hasHaving
  | _ => false

partial def Reference.hasHaving (reference : Reference) : Bool :=
  reference.filter.isSome || match reference.index with
    | some (.reference key) => key.hasHaving
    | _ => false

partial def Argument.hasHaving : Argument → Bool
  | .mk expression rangeEnd => expression.hasHaving || rangeEnd.any Expr.hasHaving
end

private def checkedHaving (result : Except CorrelationElabError α)
    (insideSemanticIndexKey : Bool := false) : Lowering α :=
  result.mapError fun error =>
    let capturedRead := match error with
      | .fieldOutsideEnvironment .outer .. | .repetitionOutsideEnvironment .outer ..
      | .outerLevelUnbound .. => true
      | _ => false
    { construct := "Having"
      detail := match error.diagnostic? with
        | some diagnostic =>
            if insideSemanticIndexKey && capturedRead && diagnostic == .noWildcard then
              KernelStaticDiagnostic.semanticIndexKeyInvalidIteration.kernelCode
            else diagnostic.kernelCode
        | none => oneLine ((repr error).pretty 100000) }

mutual
/-- An entity key finishes its own read before its parent's semantic-index gates.
Inside an unmarked filter read, index and scope restrictions belong to the later body walk;
key applicability still precedes that walk. A reference's category follows its own index
cascade, so a nested index can refuse before that category (spec/07 §3, spec/08 §4). -/
private partial def admitEntityRead (model : FlatModel) (group bindingGroup : GroupPath)
    (reference : Reference) (insideSemanticIndexKey : Bool)
    (compilePattern : StringPatternCompiler) : Lowering (Sum FlatFieldDecl GroupPath) := do
  let plain : Path := { reference.path with
    correlated := false
    segments := reference.path.segments.map fun segment => { segment with star := false } }
  let some field := plain.toFieldPath? | refuse "Having" "unsupported indexed entity path"
  let entity ← match model.groupNamedBy? group field with
    | some path => pure (.inr path)
    | none => do
        let source : SurfaceStarFieldPath := {
          base := reference.path.base, turningPoint := reference.path.turningPoint
          groups := reference.path.starGroups.dropLast, field := field.field }
        let declaration ← checkedHaving ((resolveStarFieldDeclaration model group source).mapError
          (CorrelationElabError.fieldFill ∘ FieldEntityShapeElabError.starPath))
        pure (.inl declaration)
  let targetPath := match entity with | .inl declaration => declaration.path | .inr path => path
  let basePath := targetPath.take (targetPath.length - reference.path.segments.length)
  if (firstStarOnNamedNonrepeatable? model basePath reference.path.starGroups).isSome then
    refuse "Having" KernelStaticDiagnostic.invalidWildcard.kernelCode
  let containingGroup := match entity with | .inl declaration => declaration.groupPath | .inr path => path
  let starredAt := fun position =>
    let offset := targetPath.length - reference.path.segments.length
    position >= offset && (reference.path.segments[position - offset]?).any (·.star)
  if let some key := reference.index then
    let checkedKey : Sum String ((Sum FlatFieldDecl GroupPath) × SemanticIndexAdmissionKeyRef) ← match key with
      | .literal spelling => pure (.inl spelling)
      | .reference keyReference => do
          let keyEntity ← admitEntityRead model group bindingGroup keyReference true compilePattern
          pure (.inr (keyEntity, {
            resolvesToField := keyEntity.isLeft
            starred := keyReference.path.segments.any (·.star)
            expandsToNoValueValidation := match keyEntity with
              | .inl declaration => declaration.isRawString | .inr _ => false
            carriesCategory := keyReference.category.isSome }))
    let shapeKey : SemanticIndexAdmissionKey := match checkedKey with
      | .inl spelling => .constant spelling true
      | .inr (_, shape) => .reference shape
    if let some diagnostic := keyShapeRefusal shapeKey then
      refuse "Having" diagnostic.kernelCode
    if insideSemanticIndexKey then
      if let some diagnostic := semanticIndexAdmissionRefusal
          { valueSpecIsSemanticIndex := true } shapeKey then
        refuse "Having" diagnostic.kernelCode
    let groups := ((model.repeatableScopeForGroupPath containingGroup).filterMap
      model.repeatableGroupAtLevel?).reverse
    let indexPath := groups.map fun candidate => ({
      declaredNames := if candidate.indexField.isSome then 1 else 0
      nameResolvesToField := candidate.indexField.any fun id =>
        (model.lookupUniqueId id).toOption.any (·.groupPath == candidate.path) } : IndexDeclaringGroup)
    match indexResolution indexPath with
    | .error diagnostic => refuse "Having" diagnostic.kernelCode
    | .ok none => refuse "Having" KernelStaticDiagnostic.noIndexField.kernelCode
    | .ok (some _) => pure ()
    let some selected := groups.find? (·.indexField.isSome) | refuse "Having" "unresolved index group"
    let some id := selected.indexField | refuse "Having" "unresolved index field"
    let index ← checkedHaving ((model.lookupUniqueId id).mapError .resolve)
    let admissionKey ← match checkedKey with
      | .inl authored => do
          let matcher ← match index.stringPatternSource with
            | none => pure (fun (_ : String) => true)
            | some pattern => match compilePattern pattern with
                | some matcher => pure matcher
                | none => refuse "Having" "unsupported index pattern"
          let spelling := normalizeLinebreaks authored
          let some applicable := index.indexKeyFits? matcher spelling | refuse "Having" "unsupported index kind"
          pure (SemanticIndexAdmissionKey.constant spelling applicable)
      | .inr (.inl keyDeclaration, shape) => pure (.reference { shape with
          baseTypeMatchesIndexField :=
            keyDeclaration.policy.kind.surfaceKind.sharesValueListBaseType index.policy.kind.surfaceKind
          containedInIndexGroup := selected.path.isPrefixOf keyDeclaration.groupPath })
      | .inr (.inr _, shape) => pure (.reference shape)
    let starredAtIndexLevel := starredAt (selected.path.length - 1)
    if let some diagnostic := semanticIndexAdmissionRefusal { indexPath, starredAtIndexLevel } admissionKey then
      refuse "Having" diagnostic.kernelCode
  let filteredBody ← reference.filter.mapM fun expression => do
    let .inl declaration := entity | refuse "Having" KernelStaticDiagnostic.noGroupsAllowed.kernelCode
    let candidate := model.repeatableScopeForGroupPath declaration.groupPath
    let reopened := candidate.dropWhile fun level =>
      !(model.repeatableGroupAtLevel? level).any fun repeated => starredAt (repeated.path.length - 1)
    discard <| admitBody model group bindingGroup candidate reopened compilePattern insideSemanticIndexKey expression
    pure (expression, candidate, reopened)
  -- Leaving a nested filter resets to ordinary rule reads, rather than restoring the enclosing
  -- filter mode (Lenient_ConditionParser.resetFilterCondition; spec/07 §3).
  let inFilter := filteredBody.isNone
  if reference.path.correlated && !inFilter then
    refuse "Having" KernelStaticDiagnostic.invalidOuterIteration.kernelCode
  if reference.path.correlated || !inFilter then
    let mut outerWildcard := false
    for level in model.repeatableScopeForGroupPath containingGroup do
      let some repeated := model.repeatableGroupAtLevel? level | refuse "Having" "unresolved captured repetition"
      if starredAt (repeated.path.length - 1) then
        outerWildcard := true
      else
        if !group.isPrefixOf bindingGroup then
          refuse "Having" KernelStaticDiagnostic.fieldNotInRuleGroup.kernelCode
        if let some refusal := levelIterationRefusal { marker := .iteration }
            outerWildcard insideSemanticIndexKey then
          refuse "Having" refusal.catalogKey
        let unbound := model.unboundOperandLevel group bindingGroup level
        if let some diagnostic := unbound.diagnostic? then
          refuse "Having" (if diagnostic == .noWildcard && insideSemanticIndexKey then
            KernelStaticDiagnostic.semanticIndexKeyInvalidIteration else diagnostic).kernelCode
        if unbound.parallelGate == .unmeasured then refuse "Having" "unsupported captured parallel key"
  match entity with
  | .inl _ => pure ()
  | .inr path =>
      if !model.groupContributesField path then
        refuse "Having" (if path.length == 1 then KernelStaticDiagnostic.rootGroupIsEmpty
          else .groupIsEmpty).kernelCode
      if reference.category.isSome then refuse "Having" KernelStaticDiagnostic.noGroupsAllowed.kernelCode
  if let some (expression, candidate, reopened) := filteredBody then
    if reopened.isEmpty then refuse "Having" KernelStaticDiagnostic.wildcardsRequired.kernelCode
    if reference.index.isSome then refuse "Having" KernelStaticDiagnostic.semanticIndexNotAllowed.kernelCode
    let (references, forbidden) ← filterBodyInventoryAtLevels model group candidate reopened expression
    if let some diagnostic := filterBodyRefusal references forbidden then
      refuse "Having" diagnostic.kernelCode
  if let .inl declaration := entity then
    discard <| checkedHaving ((declaration.checkEntityCategoryRead (match reference.category with
      | none => .stored | some category => .projected category)).mapError .fieldFill)
  pure entity

/-- Lower and check each leaf in parse order before walking the complete body (spec/07 §3).
In particular, a later unsupported reader form cannot hide an earlier checked comparison error. -/
private partial def admitBody (model : FlatModel) (group bindingGroup : GroupPath)
    (candidateLevels reopenedLevels : List RepeatableLevel) (compilePattern : StringPatternCompiler)
    (insideSemanticIndexKey : Bool) : Expr → Lowering (Option (SurfaceCorrelatedHaving × HavingBodyAdmission))
  | .parens body => admitBody model group bindingGroup candidateLevels reopenedLevels compilePattern insideSemanticIndexKey body
  | .logic operator (first :: rest) => do
      let join : CorrelatedHaving → CorrelatedHaving → CorrelatedHaving :=
        match operator with | .and => .and | .or => .or
      let mut body ← admitBody model group bindingGroup candidateLevels reopenedLevels compilePattern insideSemanticIndexKey first
      for next in rest do
        let following ← admitBody model group bindingGroup candidateLevels reopenedLevels compilePattern insideSemanticIndexKey next
        body := do
          let (leftAuthored, left) ← body
          let (rightAuthored, right) ← following
          let authored := match operator with
            | .and => SurfaceCorrelatedHaving.and leftAuthored rightAuthored
            | .or => SurfaceCorrelatedHaving.or leftAuthored rightAuthored
          pure (authored, HavingBodyAdmission.combine join left right)
      pure body
  | expression@(.call operator [.mk (.entity reference) none] none none) => do
      if (operator == "FieldFilled" || operator == "FieldNotFilled") && reference.path.isPlain &&
          reference.category.isNone && reference.filter.isNone then
        if reference.index.isSome then
          let entity ← admitEntityRead model group bindingGroup reference insideSemanticIndexKey compilePattern
          if entity.isRight then refuse "Having" "indexed group presence"
          -- An unmarked index must fail the enclosing walk, so it has no executable filter leaf
          -- (spec/07 §3); retain the successful own checks without inventing a runtime body.
          return none
      let authored ← lowerHaving expression (some (model, group))
      let checked ← checkedHaving (elaborateHavingBodyAtLevels model group candidateLevels reopenedLevels authored bindingGroup compilePattern) insideSemanticIndexKey
      pure (some (authored, checked))
  | expression => do
      let authored ← lowerHaving expression (some (model, group))
      let checked ← checkedHaving (elaborateHavingBodyAtLevels model group candidateLevels reopenedLevels authored bindingGroup compilePattern) insideSemanticIndexKey
      pure (some (authored, checked))

end

/-- Admit a parsed body at an already checked filtered field. This entry preserves the raw
reference walk after ordered own-leaf checks, then certifies the executable body. General nested-filter state transitions outside
key reads remain unsupported
(spec/07 §3). -/
private def admitRawStarHaving (model : FlatModel) (declaringGroup : GroupPath)
    (source : CheckedStarFieldPath model) (expression : Expr)
    (bindingGroup : GroupPath := declaringGroup)
    (compilePattern : StringPatternCompiler := locallyExecutableStringPatternMatcher?) :
    Lowering (SurfaceCorrelatedHaving × CheckedStarHaving model source bindingGroup) := do
  let candidate := source.path.axes.map (·.level)
  let body ← admitBody model declaringGroup bindingGroup candidate (candidate.drop source.path.firstStar)
    compilePattern false expression
  let (references, forbidden) ← filterBodyInventory model declaringGroup source expression
  if let some diagnostic := filterBodyRefusal references forbidden then
    refuse "Having" diagnostic.kernelCode
  let some (authored, body) := body | refuse "Having" "indexed body escaped its filter walk"
  let checked ← checkedHaving (finishStarHavingBody model declaringGroup source body bindingGroup)
  pure (authored, checked)

def elaborateRawStarHaving (model : FlatModel) (declaringGroup : GroupPath)
    (source : CheckedStarFieldPath model) (expression : Expr)
    (bindingGroup : GroupPath := declaringGroup)
    (compilePattern : StringPatternCompiler := locallyExecutableStringPatternMatcher?) :
    Lowering (CheckedStarHaving model source bindingGroup) :=
  Prod.snd <$> admitRawStarHaving model declaringGroup source expression bindingGroup compilePattern

/-- A reader with a known caller binding checks the raw body before returning the existing
surface tree. Callers without that context retain their deferred typed admission. -/
def lowerAdmittedHaving (model : FlatModel) (group : GroupPath) (path : SurfaceStarFieldPath)
    (expression : Expr) (bindingGroup? : Option GroupPath) : Lowering SurfaceCorrelatedHaving := do
  match bindingGroup? with
  | none => lowerHaving expression (some (model, group))
  | some bindingGroup =>
      let source ← checkedHaving ((elaborateStarFieldPath model group path).mapError (CorrelationElabError.fieldFill ∘ FieldEntityShapeElabError.starPath))
      Prod.fst <$> admitRawStarHaving model group source expression bindingGroup

end A12Kernel.Dm
