import A12Kernel.Elaboration.Flat.Types

/-! # Comparison entry before operand-family checks

These profiles retain only the resolved operation kind and the authored distinctions read by the
entry gate. A `kind` is the operation's result family, not the field's declared kind; numeric
`BaseYear` therefore has `.number` here. Callers retain the original expressions and pattern text.

Grouping must survive this projection: a grouped constant remains constant but a grouped clock loses
the bare-clock exception, and a grouped field is not a bare pattern operand. The
[comparison-entry checkpoint](../../docs/SOURCES.md#src-comparison-entry-gates) owns the observations.
The result identifies the next checker; it is not a Boolean claim that the entire comparison is legal.
-/

namespace A12Kernel

inductive ComparisonEntryOperand where
  | field (kind : SurfaceScalarKind)
  | expression (kind : SurfaceScalarKind)
  | literal (kind : SurfaceScalarKind)
  | clock (kind : TemporalKind)
  | grouped (operand : ComparisonEntryOperand)
  deriving Repr, DecidableEq

inductive ComparisonEntryFamily where
  | equality
  | ordering
  | tolerance
  | pattern
  deriving Repr, DecidableEq

/-- Ordinary comparisons still need their pair-specific kind/scale checks; patterns still need the
existing source admission. Only the tolerance entry is complete at this boundary. -/
inductive ComparisonEntryContinuation where
  | ordinary
  | patternSource
  | complete
  deriving Repr, DecidableEq

inductive ComparisonConstantForm where
  | variable
  | fixed
  | bareClock
  deriving Repr, DecidableEq

/-- Whether an ordering comparison can order a kind at all: Number and the temporal families, and
nothing else ([KF270](../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf270)). A CUSTOM declaration
carries the String kind here, and is not orderable either. The ordering entry gate asks it of both
operands, and the pair's diagnostic reuses it. -/
def SurfaceScalarKind.orderable : SurfaceScalarKind → Bool
  | .number | .temporal _ => true
  | .string | .enumeration | .boolean | .confirm | .dateRange => false

namespace ComparisonEntryOperand

def kind : ComparisonEntryOperand → SurfaceScalarKind
  | .field k | .expression k | .literal k => k
  | .clock k => .temporal k
  | .grouped operand => operand.kind

/-- Braces preserve constantness but remove the immediate clock spelling; the paired clock probes
at the owning checkpoint distinguish this from recursively recognizing `Today`/`Now`. -/
def constantForm : ComparisonEntryOperand → ComparisonConstantForm
  | .field _ | .expression _ => .variable
  | .literal _ => .fixed
  | .clock _ => .bareClock
  | .grouped operand =>
      match operand.constantForm with
      | .variable => .variable
      | .fixed | .bareClock => .fixed

def isSortable (operand : ComparisonEntryOperand) : Bool :=
  operand.kind.orderable

end ComparisonEntryOperand

/-- A constant pair needs exactly one bare clock and a temporal left result. Thus this entry
decision is directional even though many later comparison operators are symmetric. -/
def comparisonConstantPairAllowed (left right : ComparisonEntryOperand) : Bool :=
  match left.constantForm, right.constantForm with
  | .variable, _ | _, .variable => true
  | .fixed, .fixed | .bareClock, .bareClock => false
  | .fixed, .bareClock | .bareClock, .fixed =>
      match left.kind with
      | .temporal _ => true
      | _ => false

def checkComparisonEntry (family : ComparisonEntryFamily)
    (left right : ComparisonEntryOperand) :
    Except KernelStaticDiagnostic ComparisonEntryContinuation :=
  if !comparisonConstantPairAllowed left right then .error .invalidCompareToConst
  else match family with
    | .equality => .ok .ordinary
    | .ordering =>
        if left.isSortable && right.isSortable then .ok .ordinary
        else .error .invalidTypeForComparison
    | .tolerance =>
        if left.kind == .number && right.kind == .number then .ok .complete
        else .error .invalidTypeForToleranceOp
    | .pattern =>
        match left with
        | .field k =>
            if k != .string || right.kind != .string then .error .invalidTypeForPatternComparison
            else if right.constantForm == .variable then .error .missingConstantInPatternComparison
            else .ok .patternSource
        | .expression _ | .literal _ | .clock _ | .grouped _ =>
            .error .invalidParameterForPatternComparison

end A12Kernel
