import A12Kernel.Core
import A12Kernel.Elaboration.StaticDiagnostic

/-! # Temporal extractor entry after authored-literal recognition

Numeric component extractors and DateTime-to-Date/Time projections share literal recognition but have different literal admission. The caller retains its expression tree and supplies the recognized temporal kind only after the authored literal's lexical and calendar checks. This module neither parses text nor reuses stored-value decoding as an authored-literal recognizer.

A nonliteral source continues to its existing field, partial-precision, and format checks. A recognized DateTime literal completes this entry check only for the Date- or Time-valued projections; the numeric extractors refuse every direct literal regardless of its recognized kind.
-/

namespace A12Kernel

inductive TemporalExtractorFamily where
  | numeric
  | dateFromDateTime
  | timeFromDateTime
  deriving Repr, DecidableEq

/-- `none` records failed authored-temporal recognition, not an unavailable runtime value or an unsupported decoder. -/
inductive TemporalExtractorEntryOperand where
  | literal (recognizedKind : Option TemporalKind)
  | nonliteral
  deriving Repr, DecidableEq

inductive TemporalExtractorNextCheck where
  | complete
  | nonliteralSource
  deriving Repr, DecidableEq

def checkTemporalExtractorEntry (family : TemporalExtractorFamily)
    (operand : TemporalExtractorEntryOperand) :
    Except KernelStaticDiagnostic TemporalExtractorNextCheck :=
  match operand with
  | .nonliteral => .ok .nonliteralSource
  | .literal none => .error .invalidDateString
  | .literal (some kind) =>
      match family, kind with
      | .numeric, _ => .error .noConst
      | .dateFromDateTime, .dateTime | .timeFromDateTime, .dateTime => .ok .complete
      | _, _ => .error .wrongDateFormatForOp

end A12Kernel
