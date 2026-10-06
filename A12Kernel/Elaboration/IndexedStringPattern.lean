import A12Kernel.Elaboration.StringPattern
import A12Kernel.Elaboration.SemanticIndex

namespace A12Kernel

structure SurfaceIndexedStringPatternCondition where
  op : StringPatternOp
  field : SurfaceSemanticIndex
  source : String
  deriving Repr, DecidableEq

inductive IndexedStringPatternElabError where
  | selection (error : SemanticIndexElabError)
  | pattern (error : StringPatternConditionElabError)
  | incoherent
  deriving Repr, DecidableEq

def IndexedStringPatternElabError.diagnostic? : IndexedStringPatternElabError → Option KernelStaticDiagnostic
  | .selection error => error.diagnostic?
  | .pattern error => error.diagnostic?
  | .incoherent => none

/-- Selection retains the original String admission and compiler-associated matcher; its target
cannot diverge from the certified field (spec/06 patterns and spec/08 §4). -/
structure CheckedIndexedStringPatternLeaf (model : FlatModel) where
  selection : CheckedSemanticIndexSource model
  leaf : CheckedStringPatternLeaf model
  sameTarget : selection.targetDeclaration.id = leaf.condition.field.id

def elaborateIndexedStringPattern (compilePattern : StringPatternCompiler)
    (model : FlatModel) (rowGroup : GroupPath) (surface : SurfaceIndexedStringPatternCondition) :
    Except IndexedStringPatternElabError (CheckedIndexedStringPatternLeaf model) := do
  let selection ← (elaborateSemanticIndexSource model rowGroup surface.field).mapError .selection
  let declaration := selection.targetDeclaration
  let condition ← (elaborateStringPatternCondition compilePattern model declaration.groupPath
    { op := surface.op, field := { base := .relative 0, groups := [], field := declaration.name }, source := surface.source }).mapError .pattern
  if sameTarget : selection.targetDeclaration.id = condition.field.id then
    pure { selection, leaf := { compilePattern, condition }, sameTarget }
  else throw .incoherent

def CheckedIndexedStringPatternLeaf.bindingScope
    (source : CheckedIndexedStringPatternLeaf model) : List RepeatableLevel :=
  match source.selection.key with
  | .literal .. => []
  | .field declaration => declaration.repeatableScope

def CheckedIndexedStringPatternLeaf.evalObservation
    (source : CheckedIndexedStringPatternLeaf model) (observation : CellObservation) : Verdict :=
  source.leaf.condition.pattern.evalResolved source.leaf.condition.op observation.asStringComparisonOperand

end A12Kernel
