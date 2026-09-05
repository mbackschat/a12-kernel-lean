import A12Kernel.Elaboration.TemporalExtremumOperands
import A12Kernel.Semantics.DateAggregate

/-! # A12Kernel.Elaboration.TemporalExtremumStream — reading an admitted extremum's operands into the fold

[`Semantics/DateAggregate.lean`](../Semantics/DateAggregate.lean) has always folded an
already-classified temporal stream, and [`TemporalExtremumOperands.lean`](TemporalExtremumOperands.lean)
admits the operand lists the Kernel accepts. Nothing joined them: no code turned a model and a
document into the stream, so the extrema were admissible and unevaluable.

**The element type is the operands' own family, not one universal domain.** That was the open
representation question, and it is settled by measurement rather than chosen here: an extremum's
result is refused against a field of a different temporal family exactly as a plain field of its
own family would be, so a domain that erased the family would admit comparisons the Kernel refuses
([checkpoint](../../docs/SOURCES.md#src-extrema-operand-family-is-positional)). The fold was already
parametric in that type, so nothing about it changes; what this module supplies is the projection
into one family's domain.

**Scope: the complete-Date family, direct field operands, scalar reads.** The admitted component set
must be a whole calendar date, which is exactly the condition under which `FullDate` holds every
operand. A component-omitting list — `yyyy-MM`, or a yearless set completed by a Base Year — is
declined rather than folded, because its values are neither `FullDate` nor an instant and whether
the Kernel orders such operands by interval or by component tuple is an open runtime question
([SG6](../../docs/SEMANTICS-GAPS.md)). Star, group, and filtered operands are declined here too:
they resolve through the addressed context rather than a flat one, and admitting them by reading
only their declaring cell would silently fold one row where the Kernel folds all of them.
-/

namespace A12Kernel

/-- Why an admitted operand list cannot be read into the complete-Date fold.

    Every arm is this module's own boundary rather than a Kernel refusal, so none projects a
    diagnostic class: each names a shape the Kernel accepts and this slice does not yet evaluate. -/
inductive TemporalExtremumStreamError where
  /-- The agreed component set is not a whole calendar date, so `FullDate` cannot hold the operands. -/
  | notCompleteDate (components : TemporalComponents)
  /-- A star, group, or filtered operand, which needs the addressed context this slice does not take. -/
  | operandNeedsAddressing (path : List String)
  deriving Repr, DecidableEq

namespace TemporalExtremumStream

/-- The one declaration a direct operand reads, or the refusal its form earns here. -/
private def directDeclaration :
    ResolvedFieldEntityOperand model →
      Except TemporalExtremumStreamError FlatFieldDecl
  | .field declaration _ => pure declaration
  | .star source => throw (.operandNeedsAddressing source.declaration.path)
  | .starHaving source _ => throw (.operandNeedsAddressing source.declaration.path)
  | .group reference => throw (.operandNeedsAddressing reference.path)
  | .starredGroup source => throw (.operandNeedsAddressing source.group.path)
  | .starredGroupPresence source => throw (.operandNeedsAddressing source.groupPath)

/-- Read one admitted operand list into the complete-Date fold's own side.

    Operands stay in authored order, which the fold's own scan depends on for its left-biased tie
    and for reporting the first unavailable operand. Neither structural marker is set: a direct
    field list has no uninstantiated tail and no filter, and setting one would weaken every result's
    given-ness for no reason this slice can observe. -/
def readSide (admitted : CheckedTemporalExtremumOperands model)
    (context : FlatContext) (phase : Phase) :
    Except TemporalExtremumStreamError ResolvedDateAggregateSide := do
  if admitted.components ≠ TemporalComponents.fullDate then
    throw (.notCompleteDate admitted.components)
  else
    let declarations ←
      (admitted.shape.first :: admitted.shape.rest).mapM directDeclaration
    pure {
      operands := declarations.map fun declaration =>
        (context.observeAt phase declaration.id).asDateExtremumOperand
      hasUninstantiatedTail := false
      hasHaving := false }

/-- Evaluate one admitted complete-Date extremum against a flat context, as the shared classified
    comparison operand every Date consumer already takes. -/
def eval (admitted : CheckedTemporalExtremumOperands model)
    (op : TemporalExtremumOp) (context : FlatContext) (phase : Phase) :
    Except TemporalExtremumStreamError (SimpleComparisonOperand FullDate) := do
  pure (evalDateExtremumAggregate op (← readSide admitted context phase))

end TemporalExtremumStream

namespace TemporalExtremumStreamError

/-- No arm claims a Kernel class. Both name shapes the Kernel admits and this slice declines, which
    this vocabulary reports as absent coverage rather than as a refusal. -/
def diagnostic? : TemporalExtremumStreamError → Option KernelStaticDiagnostic
  | .notCompleteDate _ => none
  | .operandNeedsAddressing _ => none

end TemporalExtremumStreamError

end A12Kernel
