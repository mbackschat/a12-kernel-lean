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

private def checkedHaving (result : Except CorrelationElabError α) : Lowering α :=
  result.mapError fun error => {
    construct := "Having"
    detail := match error.diagnostic? with
      | some diagnostic => diagnostic.kernelCode
      | none => oneLine ((repr error).pretty 100000) }

/-- A field key finishes its own read before its parent's semantic-index gates.
Inside an unmarked filter read, index and scope restrictions belong to the later body walk;
key applicability still precedes that walk. A reference's category follows its own index
cascade, so a nested index can refuse before that category (spec/07 §3, spec/08 §4). -/
private partial def admitFieldRead (model : FlatModel) (group : GroupPath)
    (reference : Reference) (insideSemanticIndexKey : Bool)
    (compilePattern : StringPatternCompiler) : Lowering FlatFieldDecl := do
  if reference.filter.isSome then refuse "Having" "unsupported index key filter"
  let some field := reference.path.toFieldPath? | refuse "Having" "unsupported indexed field path"
  if (model.groupNamedBy? group field).isSome then refuse "Having" "indexed group presence"
  let declaration ← checkedHaving ((model.resolveFieldDeclarationUnchecked group field).mapError .resolve)
  if let some key := reference.index then
    let checkedKey : Sum String (FlatFieldDecl × SemanticIndexAdmissionKeyRef) ← match key with
      | .literal spelling => pure (.inl spelling)
      | .reference keyReference => do
          let keyDeclaration ← admitFieldRead model group keyReference true compilePattern
          pure (.inr (keyDeclaration, {
            expandsToNoValueValidation := keyDeclaration.isRawString
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
    let groups := ((model.repeatableScopeForGroupPath declaration.groupPath).filterMap
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
      | .inr (keyDeclaration, shape) => pure (.reference { shape with
          baseTypeMatchesIndexField :=
            keyDeclaration.policy.kind.surfaceKind.sharesValueListBaseType index.policy.kind.surfaceKind
          containedInIndexGroup := selected.path.isPrefixOf keyDeclaration.groupPath })
    if let some diagnostic := semanticIndexAdmissionRefusal { indexPath } admissionKey then
      refuse "Having" diagnostic.kernelCode
  discard <| checkedHaving ((declaration.checkEntityCategoryRead (match reference.category with
    | none => .stored | some category => .projected category)).mapError .fieldFill)
  pure declaration

/-- Lower and check each leaf in parse order before walking the complete body (spec/07 §3).
In particular, a later unsupported reader form cannot hide an earlier checked comparison error. -/
private partial def admitBody (model : FlatModel) (group bindingGroup : GroupPath)
    (source : CheckedStarFieldPath model) (compilePattern : StringPatternCompiler) :
    Expr → Lowering (Option (SurfaceCorrelatedHaving × HavingBodyAdmission))
  | .parens body => admitBody model group bindingGroup source compilePattern body
  | .logic operator (first :: rest) => do
      let join : CorrelatedHaving → CorrelatedHaving → CorrelatedHaving :=
        match operator with | .and => .and | .or => .or
      let mut body ← admitBody model group bindingGroup source compilePattern first
      for next in rest do
        let following ← admitBody model group bindingGroup source compilePattern next
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
          let _ ← admitFieldRead model group reference false compilePattern
          -- An unmarked index must fail the enclosing walk, so it has no executable filter leaf
          -- (spec/07 §3); retain the successful own checks without inventing a runtime body.
          return none
      let authored ← lowerHaving expression (some (model, group))
      let checked ← checkedHaving (elaborateStarHavingBody model group source authored bindingGroup compilePattern)
      pure (some (authored, checked))
  | expression => do
      let authored ← lowerHaving expression (some (model, group))
      let checked ← checkedHaving (elaborateStarHavingBody model group source authored bindingGroup compilePattern)
      pure (some (authored, checked))

/-- Admit a parsed body at an already checked filtered field. This entry preserves the raw
reference walk after ordered own-leaf checks, then certifies the executable body. Marked or
starred keys, group keys and the parser's nested-filter state transitions remain unsupported
(spec/07 §3). -/
private def admitRawStarHaving (model : FlatModel) (declaringGroup : GroupPath)
    (source : CheckedStarFieldPath model) (expression : Expr)
    (bindingGroup : GroupPath := declaringGroup)
    (compilePattern : StringPatternCompiler := locallyExecutableStringPatternMatcher?) :
    Lowering (SurfaceCorrelatedHaving × CheckedStarHaving model source bindingGroup) := do
  let body ← admitBody model declaringGroup bindingGroup source compilePattern expression
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
