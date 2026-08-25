import A12Kernel.Elaboration.SingleGroup
import A12Kernel.Semantics.NumericComparison

/-! # Checked CurrentRepetition coordinate and closed comparison domains -/

namespace A12Kernel

/-- Fail-closed errors for one repeatable structural coordinate source. -/
inductive CurrentRepetitionSourceElabError where
  | model (cause : ResolveError)
  | reference (cause : SingleGroupElabError)
  | group (cause : ResolveError)
  deriving Repr, DecidableEq

/-- One exact repeatable group coordinate certified against its owning model. It is structural and therefore has no field dependency. -/
structure CheckedCurrentRepetitionSource (model : FlatModel) where
  private mk ::
  path : GroupPath
  group : RepeatableGroupDecl
  modelWellFormed : model.validate.isOk = true
  groupOwned :
    model.lookupUniqueRepeatablePath path = .ok group

/-- Resolve one authored group path to its exact model-owned repeatable coordinate source. -/
def checkCurrentRepetitionSource
    (model : FlatModel) (declaringGroup : GroupPath)
    (reference : SurfaceGroupPath) :
    Except CurrentRepetitionSourceElabError
      (CheckedCurrentRepetitionSource model) :=
  match hModel : model.validate with
  | .error cause => .error (.model cause)
  | .ok () => do
      let path <- reference.resolveAgainst declaringGroup |>.mapError .reference
      match hGroup : model.lookupUniqueRepeatablePath path with
      | .error cause => .error (.group cause)
      | .ok group => pure {
          path
          group
          modelWellFormed := by rw [hModel]; rfl
          groupOwned := hGroup
        }

namespace CheckedCurrentRepetitionSource

/-- The complete repeatable scope containing the selected structural coordinate. -/
def completeScope (source : CheckedCurrentRepetitionSource model) :
    List RepeatableLevel :=
  model.repeatableScopeForGroupPath source.path

/-- Read the source's exact positive coordinate from the selected row environment. -/
def coordinateAt (source : CheckedCurrentRepetitionSource model)
    (environment : Env) : Except EnvBindingError Nat :=
  environment.bindingAt source.group.level

/-- Evaluate the shared fixed positive computation guard without introducing a second condition tree. The coordinate remains available to structural-failure diagnostics. -/
def evaluatePositiveGuardAt (source : CheckedCurrentRepetitionSource model)
    (environment : Env) : Except EnvBindingError (Nat × Bool) := do
  let coordinate ← source.coordinateAt environment
  pure (coordinate, NumericComparisonOp.greater.holds coordinate 0)

/-- Structural coordinates never induce a field dependency. -/
def referencesField (_source : CheckedCurrentRepetitionSource model)
    (_field : FieldId) : Bool := false

end CheckedCurrentRepetitionSource

/-- The only two comparisons established for `CurrentRepetition` over a nonrepeatable root. The compared literal is structurally fixed to one. -/
inductive RootCurrentRepetitionComparison where
  | equalOne
  | notEqualOne
  deriving Repr, DecidableEq

def RootCurrentRepetitionComparison.numericOperator :
    RootCurrentRepetitionComparison → NumericComparisonOp
  | .equalOne => .equal
  | .notEqualOne => .notEqual

/-- Evaluate the closed comparison through the shared numeric comparison owner. Both operands are structural fixed values, so a firing is VALUE. -/
def RootCurrentRepetitionComparison.eval
    (comparison : RootCurrentRepetitionComparison) : Verdict :=
  comparison.numericOperator.evalFixedRight (.value 1 .fixed) 1

/-- The three same-group repeatable comparisons retained by the maintained row-index matrix. Each tag fixes both operator and bound, so checked clients cannot widen the measured surface through a generic numeric expression. -/
inductive RepeatableCurrentRepetitionComparison where
  | greaterThanOne
  | greaterThanTwo
  | greaterEqualOne
  deriving Repr, DecidableEq

def RepeatableCurrentRepetitionComparison.numericOperator :
    RepeatableCurrentRepetitionComparison → NumericComparisonOp
  | .greaterThanOne | .greaterThanTwo => .greater
  | .greaterEqualOne => .greaterEqual

def RepeatableCurrentRepetitionComparison.bound :
    RepeatableCurrentRepetitionComparison → Rat
  | .greaterThanOne | .greaterEqualOne => 1
  | .greaterThanTwo => 2

/-- Compare one checked positive row coordinate through the shared fixed numeric owner. -/
def RepeatableCurrentRepetitionComparison.eval
    (comparison : RepeatableCurrentRepetitionComparison)
    (coordinate : Nat) : Verdict :=
  comparison.numericOperator.evalFixedRight
    (.value coordinate .fixed) comparison.bound

end A12Kernel
