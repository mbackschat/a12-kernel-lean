import A12Kernel.Elaboration.DateRangeBoundComponent
import A12Kernel.Elaboration.SemanticIndex

/-! # A keyed DateRange operand

A semantic index selects one row of a group by its declared index field's value, and the selected
cell may be a DateRange. The measured Kernel rule is that the index field's kind and the selected
target's kind are independent, so this capsule adds only the **target side**: the checked source's
selected declaration is a DateRange, and the keyed read is projected into the same retained
exact-or-fragment identity a direct read produces.

The result domain needs no new outcome class. A no-match row and a matched-but-empty cell both read
empty, and a duplicated key and a formally invalid matched cell both read UNKNOWN, which is exactly
the ordinary phase observation the direct route already uses.

The wired carrier here is the **numeric component of a selected endpoint**, because it consumes the
projected observation directly and therefore needs no second read path. The other three measured
carriers — an endpoint comparison, the overlap predicate, and stored range equality — consume the
same checked source and remain open.

Both local refusals stay **unmapped to a Kernel diagnostic**. The keyed lookup's exposure gate and
its non-DateRange target class are unmeasured rows: the admission measurement establishes that this
operand shape is accepted, not which code its rejections carry.
-/

namespace A12Kernel

inductive SemanticIndexDateRangeElabError where
  | source (error : SemanticIndexElabError)
  /-- The row selected by the key is not a DateRange declaration at all. -/
  | selectedTargetNotDateRange (path : List String)
  /-- The selected DateRange's declared profile does not expose the requested component. -/
  | boundPartNotExposed (path : List String) (part : DateNumericPart)
  deriving Repr, DecidableEq

namespace SemanticIndexDateRangeElabError

/-- Only the shared source classes project. The two local ones are unmeasured for this operand
shape, so mapping them would assert a code rather than report one. -/
def diagnostic? : SemanticIndexDateRangeElabError → Option KernelStaticDiagnostic
  | .source error => error.diagnostic?
  | .selectedTargetNotDateRange _ | .boundPartNotExposed _ _ => none

end SemanticIndexDateRangeElabError

/-- A semantic-index source whose selected target declaration is a DateRange. The index field's kind
stays unconstrained, which is the measured independence. -/
structure CheckedDateRangeSemanticIndexSource (model : FlatModel)
    extends CheckedSemanticIndexSource model where
  targetDateRange :
    toCheckedSemanticIndexSource.targetDeclaration.toDateRangeField?.isSome =
      true

/-- The two failure classes a keyed range read can reach. They stay distinct because a lookup that
could not be resolved at all is a different consumer decision from a selected cell of the wrong
kind. -/
inductive SemanticIndexDateRangeError where
  | context (error : SemanticIndexContextError)
  | payload (fault : DirectDateRangeFault)
  deriving Repr, DecidableEq

namespace CheckedDateRangeSemanticIndexSource

/-- The selected DateRange field, recovered from its own kind witness. -/
def targetField (checked : CheckedDateRangeSemanticIndexSource model) :
    FlatDateRangeField :=
  checked.targetDeclaration.toDateRangeField?.get checked.targetDateRange

/-- Read the keyed row's selected cell and project it into the retained range identity through the
direct route's own payload rule, so the two cannot disagree about emptiness, kind, or formal
unavailability. -/
def observePreliminaryRange
    (checked : CheckedDateRangeSemanticIndexSource model)
    (preliminary : CheckedIndexPreliminary model)
    (keyRaw : RawFlatContext) (phase : Phase) (outer : Env := []) :
    Except SemanticIndexDateRangeError
      (CellObservation DateRangeCellValue) := do
  let observed ← (checked.lookupPreliminaryValue preliminary keyRaw phase outer)
    |>.mapError .context
  CheckedDateRangeSource.projectRange checked.targetField.id observed
    |>.mapError .payload

end CheckedDateRangeSemanticIndexSource

/-- One numeric Date component of an endpoint selected from a keyed row. -/
structure CheckedSemanticIndexDateRangeBoundPart (model : FlatModel) where
  source : CheckedDateRangeSemanticIndexSource model
  bound : DateRangeBound
  part : DateNumericPart
  componentExposed :
    model.exposesDateRangeBoundPart source.targetField part = true

/-- Certify a keyed DateRange source: the shared semantic-index certificate plus this target's kind. -/
def elaborateDateRangeSemanticIndexSource (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceSemanticIndex) :
    Except SemanticIndexDateRangeElabError
      (CheckedDateRangeSemanticIndexSource model) := do
  let checked ← elaborateSemanticIndexSource model declaringGroup authored
    |>.mapError .source
  if hTarget : checked.targetDeclaration.toDateRangeField?.isSome = true then
    pure {
      toCheckedSemanticIndexSource := checked
      targetDateRange := hTarget }
  else
    throw (.selectedTargetNotDateRange checked.targetDeclaration.path)

/-- Certify the component read. The exposure gate is the selected declaration's own component set
supplemented by the model's Base Year, which is the direct component owner's rule reaching this
source unchanged. -/
def checkSemanticIndexDateRangeBoundPart (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceSemanticIndex)
    (bound : DateRangeBound) (part : DateNumericPart) :
    Except SemanticIndexDateRangeElabError
      (CheckedSemanticIndexDateRangeBoundPart model) := do
  let source ← elaborateDateRangeSemanticIndexSource model declaringGroup
    authored
  if hPart : model.exposesDateRangeBoundPart source.targetField part = true then
    pure { source, bound, part, componentExposed := hPart }
  else
    throw (.boundPartNotExposed source.targetDeclaration.path part)

namespace CheckedSemanticIndexDateRangeBoundPart

/-- Resolve the keyed endpoint component into the shared validation Number operand. A lookup that
could not be resolved keeps its own error, while a selected cell whose kind is not a DateRange
collapses to malformed — the same collapse the direct component read performs, because at this point
the static gate has already admitted the declaration. -/
def resolvePreliminaryNumericOperand
    (operation : CheckedSemanticIndexDateRangeBoundPart model)
    (preliminary : CheckedIndexPreliminary model)
    (keyRaw : RawFlatContext) (outer : Env := []) :
    Except SemanticIndexContextError NumericOperand :=
  match operation.source.observePreliminaryRange preliminary keyRaw .validation
      outer with
  | .error (.context error) => .error error
  | .error (.payload _) => .ok (.unknown .malformed)
  | .ok observed =>
      .ok (operation.part.fromDateRangeBoundObservation operation.bound
        observed)

end CheckedSemanticIndexDateRangeBoundPart

end A12Kernel
