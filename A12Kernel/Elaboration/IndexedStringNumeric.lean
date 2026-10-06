import A12Kernel.Elaboration.SemanticIndex
import A12Kernel.Elaboration.NumericSource
import A12Kernel.Semantics.NumericExpression

namespace A12Kernel

inductive IndexedStringNumericOperation where
  | length
  | range (start finish : Nat)
  | asNumber (projection : EnumerationProjectionRef)
  deriving Repr, DecidableEq

inductive IndexedStringNumericElabError where
  | index (error : SemanticIndexElabError)
  | notString (path : List String)
  | invalidRange (start finish : Nat)
  | conversion (path : List String) (error : FieldValueAsNumberSourceError)
  deriving Repr, DecidableEq

def IndexedStringNumericElabError.diagnostic? : IndexedStringNumericElabError → Option KernelStaticDiagnostic
  | .index error => error.diagnostic?
  | .conversion _ error => error.diagnostic?
  | _ => none

/-- Selection retains identity; this projection reuses the scalar operation's admission and observations. -/
inductive StringNumericProjection where
  | length
  | range (start finish : Nat)
  | asNumber (source : ResolvedFieldValueAsNumberSource)
  deriving Repr, DecidableEq

def StringNumericProjection.scale : StringNumericProjection → Nat
  | .length | .range .. => 0
  | .asNumber source => source.scale

def StringNumericProjection.observe : StringNumericProjection → CellObservation → NumericOperand
  | .length => CellObservation.asStringLengthOperand
  | .range start finish => CellObservation.asStringRangeOperand start finish
  | .asNumber source => source.observeOperand

/-- Numeric interpretation retains its checked selector independently of the target field's own kind. -/
structure CheckedIndexedStringNumericSource (model : FlatModel) where
  private mk ::
  selection : CheckedSemanticIndexSource model
  projection : StringNumericProjection

def elaborateIndexedStringNumericSource (model : FlatModel) (declaringGroup : GroupPath)
    (surface : SurfaceSemanticIndex) (operation : IndexedStringNumericOperation) :
    Except IndexedStringNumericElabError (CheckedIndexedStringNumericSource model) := do
  let selection ← (elaborateSemanticIndexSource model declaringGroup surface).mapError .index
  let declaration := selection.targetDeclaration
  let projection ← match operation with
    | .length => do
        if declaration.toStringValueField?.isNone then throw (.notString declaration.path)
        pure StringNumericProjection.length
    | .range start finish => do
        if !validStringRange start finish then throw (.invalidRange start finish)
        if declaration.toStringValueField?.isNone then throw (.notString declaration.path)
        pure (.range start finish)
    | .asNumber projection =>
        StringNumericProjection.asNumber <$>
          (declaration.resolveFieldValueAsNumberSource projection).mapError (.conversion declaration.path)
  pure { selection, projection }

namespace CheckedIndexedStringNumericSource

def boundFieldIds (source : CheckedIndexedStringNumericSource model) : List FieldId :=
  match source.selection.key with
  | .field declaration => [declaration.id]
  | .literal .. => []

def referencesField (source : CheckedIndexedStringNumericSource model) (field : FieldId) : Bool :=
  source.selection.referencesField field

/-- A forged value-kind or token read is a context fault, while an observed formal cause remains poison. -/
def computationResult (source : CheckedIndexedStringNumericSource model) (observation : CellObservation) :
    Except FieldId NumericComputationResult :=
  match observation, source.projection.observe observation with
  | .value _, .unknown _ => .error source.selection.targetDeclaration.id
  | _, operand => .ok operand.toComputationResult

end CheckedIndexedStringNumericSource
end A12Kernel
