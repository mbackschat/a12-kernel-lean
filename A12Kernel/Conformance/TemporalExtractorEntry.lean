import A12Kernel.Elaboration.TemporalExtractorEntry

namespace A12Kernel.Conformance.TemporalExtractorEntry

private def view (family : TemporalExtractorFamily)
    (operand : TemporalExtractorEntryOperand) :
    Option String × Option TemporalExtractorNextCheck :=
  match checkTemporalExtractorEntry family operand with
  | .error diagnostic => (some diagnostic.kernelCode, none)
  | .ok next => (none, some next)

private def families : List TemporalExtractorFamily :=
  [.numeric, .dateFromDateTime, .timeFromDateTime]

example :
    families.map (fun family =>
      ([none, some .date, some .time, some .dateTime] : List (Option TemporalKind)).map
        (fun kind => view family (.literal kind))) = [
      [(some "MVK_INVALID_DATE_STRING", none), (some "MVK_NO_CONST", none),
        (some "MVK_NO_CONST", none), (some "MVK_NO_CONST", none)],
      [(some "MVK_INVALID_DATE_STRING", none), (some "MVK_WRONG_DATE_FORMAT_FOR_OP", none),
        (some "MVK_WRONG_DATE_FORMAT_FOR_OP", none), (none, some .complete)],
      [(some "MVK_INVALID_DATE_STRING", none), (some "MVK_WRONG_DATE_FORMAT_FOR_OP", none),
        (some "MVK_WRONG_DATE_FORMAT_FOR_OP", none), (none, some .complete)]] := by
  native_decide

example : families.map (view · .nonliteral) =
    List.replicate 3 (none, some .nonliteralSource) := by
  native_decide

example :
    view .numeric (.literal (some .date)) = (some "MVK_NO_CONST", none) ∧
      view .dateFromDateTime (.literal (some .dateTime)) = (none, some .complete) ∧
      view .numeric .nonliteral = (none, some .nonliteralSource) := by
  native_decide

end A12Kernel.Conformance.TemporalExtractorEntry
