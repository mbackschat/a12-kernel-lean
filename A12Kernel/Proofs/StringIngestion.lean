import A12Kernel.Semantics.FlatValidation
import A12Kernel.Semantics.StringComputation

/-! # A12Kernel.Proofs.StringIngestion — one-pass evaluated String laws

This proof capsule covers the checked evaluation-cache boundary from `spec/02-logic-and-formal-errors.md` and its use by direct comparison, UTF-16 `Length`, and computation reads. It assumes an admitted parsed String; line-break permission, raw storage, enumeration ordering, and raw-type behavior remain separate obligations.
-/

namespace A12Kernel

/-- A leading CRLF pair is consumed in the current ingestion pass, independently of the remaining input. -/
theorem normalizeEvaluatedString_crlfPrefix (rest : List Char) :
    normalizeEvaluatedString (String.ofList ('\r' :: '\n' :: rest)) =
      String.ofList ('\n' :: normalizeCrlfCharacters rest) := by
  simp [normalizeEvaluatedString, normalizeCrlfCharacters]

/-- The ingestion transformation must run exactly once: a second pass can consume a pair exposed by the first pass. -/
theorem normalizeEvaluatedString_notIdempotent :
    normalizeEvaluatedString (normalizeEvaluatedString "\r\r\n") ≠
      normalizeEvaluatedString "\r\r\n" := by
  decide

/-- A successful nonempty String check caches exactly the one-pass evaluated text. -/
theorem formalCheckString_cachesNormalized (text : String)
    (nonempty : (normalizeEvaluatedString text).isEmpty = false) :
    formalCheck { kind := .string } (.parsed (.str text)) = {
      rawPresent := true
      parsed := some (.str (normalizeEvaluatedString text))
      findings := []
    } := by
  simp [formalCheck, nonempty]

/-- Both validation and computation phases read the same cached ingestion result; neither phase normalizes a second time. -/
theorem checkedString_phasesReadNormalized (text : String)
    (nonempty : (normalizeEvaluatedString text).isEmpty = false) (phase : Phase) :
    observeCell phase (formalCheck { kind := .string } (.parsed (.str text))) =
      .value (.str (normalizeEvaluatedString text)) := by
  rw [formalCheckString_cachesNormalized text nonempty]
  cases phase <;> rfl

/-- Direct String comparison receives the cached normalized text from the checked read for its resolved field. -/
theorem directStringOperand_readsNormalized (context : FlatContext)
    (field : FlatStringField) (text : String)
    (read : context.read field.id =
      formalCheck { kind := .string } (.parsed (.str text)))
    (nonempty : (normalizeEvaluatedString text).isEmpty = false) :
    context.resolveDirectStringComparisonOperand field =
      .value (normalizeEvaluatedString text) true := by
  simp [FlatContext.resolveDirectStringComparisonOperand,
    FlatContext.observeValidationAt, read, formalCheck, nonempty, observeCell]

/-- A checked String value-list operand consumes the same normalized cache as direct comparison, changing only the consumer-specific cell vocabulary. -/
theorem stringValueListCell_readsNormalized (context : FlatContext)
    (field : FlatStringField) (text : String)
    (read : context.read field.id =
      formalCheck { kind := .string } (.parsed (.str text)))
    (nonempty : (normalizeEvaluatedString text).isEmpty = false) :
    (FlatTextFieldOperand.string field).valueListCell context =
      .present (normalizeEvaluatedString text) := by
  rw [FlatTextFieldOperand.valueListCell, FlatTextFieldOperand.resolve,
    directStringOperand_readsNormalized context field text read nonempty]
  rfl

/-- A checked empty String remains an empty token-list cell rather than a present empty token. -/
theorem stringValueListCell_empty (context : FlatContext)
    (field : FlatStringField)
    (empty : context.observeValidationAt field.id = .empty) :
    (FlatTextFieldOperand.string field).valueListCell context = .empty := by
  simp [FlatTextFieldOperand.valueListCell, FlatTextFieldOperand.resolve,
    FlatContext.resolveDirectStringComparisonOperand, empty,
    SimpleComparisonOperand.asTokenValueListCell]

/-- String `Length` counts the cached normalized text supplied by the checked read for its resolved field. -/
theorem stringLengthOperand_readsNormalized (context : FlatContext)
    (field : FlatStringField) (text : String)
    (read : context.read field.id =
      formalCheck { kind := .string } (.parsed (.str text)))
    (nonempty : (normalizeEvaluatedString text).isEmpty = false) :
    context.resolveStringLengthOperand field =
      .value (utf16CodeUnitLength (normalizeEvaluatedString text)) .fixed := by
  simp [FlatContext.resolveStringLengthOperand,
    FlatContext.observeValidationAt, read, formalCheck, nonempty, observeCell]

/-- A computation field read receives the same cached normalized text from its resolved checked read without another transformation. -/
theorem stringComputationField_readsNormalized (context : StringComputationContext)
    (field : FieldId) (text : String)
    (read : context.read field =
      formalCheck { kind := .string } (.parsed (.str text)))
    (nonempty : (normalizeEvaluatedString text).isEmpty = false) :
    (StringExpr.field field).eval context =
      .ok (.text (normalizeEvaluatedString text)) := by
  simp [StringExpr.eval, StringComputationContext.readTerm, read,
    checkedString_phasesReadNormalized text nonempty .computation, nonempty] <;> rfl

end A12Kernel
