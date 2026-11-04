import A12Kernel.Reference.Dm.HavingAdmission

/-! # Entry points of the ordered raw admission walk

The walk in [`HavingAdmission`](HavingAdmission.lean) reads an authored text in the Kernel's read
order and raises the first class. Its consumers ask it through the entry points here: a completed
operation call's class, a rule's or a computation's whole-text admission with the facts that feed the
global checks, a single reference's read, and a filter body at an already checked starred field.
-/

namespace A12Kernel.Dm
open HavingListAdmission

/-- The class a completed operation call's own production raises when the parse fails after it, as the
Kernel checks each production as it completes (spec/12 §3.1): `none` for a condition call, a call that
passes, or a refusal with no Kernel class. The call is read at `group`, bound at `bindingGroup`, outside
any filter. -/
def operationCallClass? (model : FlatModel) (group : GroupPath) (call : Expr) (bindingGroup : GroupPath := group) :
    Option KernelStaticDiagnostic :=
  if call.isConditionCall then none else
  match (admitNumericAtom model group bindingGroup false false {} call).run' {} with
  | .ok _ => none
  | .error refusal => KernelStaticDiagnostic.all.find? (·.kernelCode == refusal.detail)

/-- Admit constructor/filter children before lowering and whole-rule gates. Their authored
read order precedes enclosing checks (KF532; ParserService.checkNormalRule; spec/07 §3). -/
def checkOrderedAdmission (model : FlatModel) (group bindingGroup : GroupPath)
    (expression : Expr) (suppressExactScaleWarning : Bool := false) : Lowering Unit := do
  if !expression.needsOrderedAdmission then return
  let (_, facts) ← (admitBody model group bindingGroup [] [] { suppressExactScaleWarning } false false expression).run {}
  -- Having requires a star while Length forbids stars, so this is not the standalone limiter exception (CheckFeldOpImpl; AnalyseService).
  if expression.hasHaving then
    if let some diagnostic := facts.beforeIterationRefusal? then refuse "Having" diagnostic.kernelCode

/-- Admit one fragment and retain its contribution to the generated rule's global checks.
`joinedLevels` are the levels a parallel rule's key join iterates. -/
def checkRawConditionBeforeGlobals (model : FlatModel) (group bindingGroup : GroupPath)
    (expression : Expr) (suppressExactScaleWarning : Bool) (joinedLevels : List RepeatableLevel := []) :
    Lowering FilterRuleFacts := do
  let (_, facts) ← (admitBody model group bindingGroup [] [] { suppressExactScaleWarning, joinedLevels }
    false false expression).run {}
  pure facts

/-- The generated target bracket is read before the authored operation (spec/09 §6). -/
def rawComputationTarget (target : FlatFieldDecl) : Expr :=
  .value { path := { absolute := true, segments := target.path.map fun name => { name, star := false } } }

/-- Check only the generated bracket before parsing the operation it will compare. -/
def checkRawComputationTargetRead (model : FlatModel) (group : GroupPath) (target : FlatFieldDecl) : Lowering Unit := do
  discard <| (admitNumericAtom model group target.groupPath false false {} (rawComputationTarget target)).run' {}

/-- Finish one ordinary authored reference read before advancing to another operand. The original
reference remains available to the caller's kind/shape and executable lowering stages (spec/07 §3). -/
def checkReferenceRead (model : FlatModel) (group bindingGroup : GroupPath) (reference : Reference) :
    Lowering Unit := do
  discard <| checkedHaving (model.validate.mapError .resolve)
  discard <| (admitEntityRead model group bindingGroup reference false false {}).run' {}

/-- Admit a parsed body at an already checked filtered field. This entry preserves the raw
reference walk after ordered own-leaf checks, then certifies the executable body. Parser exit
state is carried independently of executable-body availability (spec/07 §3). -/
private def admitRawStarHaving (model : FlatModel) (declaringGroup : GroupPath)
    (source : CheckedStarFieldPath model) (expression : Expr)
    (bindingGroup : GroupPath := declaringGroup)
    (compilePattern : StringPatternCompiler := builtinStringPatternCompiler) (suppress : Bool := false) :
    Lowering (SurfaceCorrelatedHaving × CheckedStarHaving model source bindingGroup) := do
  let candidate := source.path.axes.map (·.level)
  let admission : RawAdmissionContext := { compilePattern, suppressExactScaleWarning := suppress, inFilterSyntax := true }
  let (body, _) ← (admitBody model declaringGroup bindingGroup candidate (candidate.drop source.path.firstStar)
    admission false true expression).run' {}
  let (references, forbidden) ← filterBodyInventory model declaringGroup source expression
  if let some diagnostic := filterBodyRefusal references forbidden then
    refuse "Having" diagnostic.kernelCode
  let (authored, body) ← match body with
    | some checked => pure checked
    | none => do
        if expression.hasIndex || expression.hasHaving then refuse "Having" "indexed body escaped its filter walk"
        -- Certify the unchanged ordinary tree only after its complete own-read pass and filter walk.
        -- This keeps late typed restrictions behind later parse-time failures (spec/07 §3).
        admitFilterLeaf model declaringGroup bindingGroup candidate (candidate.drop source.path.firstStar)
          admission false expression
  let checked ← checkedHaving (finishStarHavingBody model declaringGroup source body bindingGroup)
  pure (if suppress then .scaleWarningSuppressed authored else authored, checked)

def elaborateRawStarHaving (model : FlatModel) (declaringGroup : GroupPath)
    (source : CheckedStarFieldPath model) (expression : Expr)
    (bindingGroup : GroupPath := declaringGroup)
    (compilePattern : StringPatternCompiler := builtinStringPatternCompiler) :
    Lowering (CheckedStarHaving model source bindingGroup) :=
  Prod.snd <$> admitRawStarHaving model declaringGroup source expression bindingGroup compilePattern

/-- A reader with a known caller binding checks the raw body before returning the existing
surface tree. Callers without that context retain their deferred typed admission. -/
def lowerAdmittedHaving (model : FlatModel) (group : GroupPath) (path : SurfaceStarFieldPath)
    (expression : Expr) (bindingGroup? : Option GroupPath) (suppress : Bool := false) :
    Lowering SurfaceCorrelatedHaving := do
  match bindingGroup? with
  | none => lowerFilter expression (some (model, group)) suppress
  | some bindingGroup =>
      let source ← checkedHaving ((elaborateStarFieldPath model group path).mapError (CorrelationElabError.fieldFill ∘ FieldEntityShapeElabError.starPath))
      Prod.fst <$> admitRawStarHaving model group source expression bindingGroup (suppress := suppress)

end A12Kernel.Dm
