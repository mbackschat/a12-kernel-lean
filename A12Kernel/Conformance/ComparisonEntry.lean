import A12Kernel.Elaboration.ComparisonEntry

/-! # Comparison-entry separators

The [retained matrix](../../docs/SOURCES.md#src-comparison-entry-gates) checks complete rules.
These cases stop at the entry boundary: `ordinary` and `pattern` require their existing next checker.
In particular the observed scale mismatch and malformed regex are not entry refusals.
-/

namespace A12Kernel.Conformance.ComparisonEntry

open A12Kernel

private def result (family : ComparisonEntryFamily) (left right : ComparisonEntryOperand) : String :=
  match checkComparisonEntry family left right with
  | .error d => d.kernelCode
  | .ok .ordinary => "ordinary"
  | .ok .patternSource => "pattern"
  | .ok .complete => "complete"

private def today : ComparisonEntryOperand := .clock .date
private def now : ComparisonEntryOperand := .clock .dateTime
private def day : ComparisonEntryOperand := .literal (.temporal .date)
private def number : ComparisonEntryOperand := .literal .number
private def text : ComparisonEntryOperand := .literal .string
private def field : ComparisonEntryOperand := .field .string

example :
    [result .equality today today, result .equality (.grouped today) today,
     result .equality today (.grouped today),
     result .equality (.grouped today) (.grouped today),
     result .equality (.grouped (.grouped today)) today,
     result .equality now now, result .equality now (.grouped now),
     result .equality (.grouped now) (.grouped now)] =
    ["MVK_INVALID_COMPARE_TO_CONST", "ordinary", "ordinary",
     "MVK_INVALID_COMPARE_TO_CONST", "ordinary", "MVK_INVALID_COMPARE_TO_CONST",
     "ordinary", "MVK_INVALID_COMPARE_TO_CONST"] := by native_decide

example :
    [result .equality today day, result .equality (.grouped today) day,
     result .equality day today, result .equality day (.grouped today),
     result .equality today (.grouped day),
     result .ordering today number, result .ordering number today,
     result .ordering (.grouped today) number,
     result .ordering today now, result .ordering today (.grouped now)] =
    ["ordinary", "MVK_INVALID_COMPARE_TO_CONST", "ordinary", "MVK_INVALID_COMPARE_TO_CONST",
     "ordinary", "ordinary", "MVK_INVALID_COMPARE_TO_CONST", "MVK_INVALID_COMPARE_TO_CONST",
     "MVK_INVALID_COMPARE_TO_CONST", "ordinary"] := by native_decide

example :
    [result .pattern text text, result .pattern (.grouped text) text,
     result .pattern (.grouped field) text, result .pattern (.expression .string) text,
     result .pattern (.expression .number) text, result .pattern (.grouped today) today,
     result .pattern (.field .number) field, result .pattern field number,
     result .pattern field field, result .pattern field text,
     result .pattern field (.grouped text)] =
    ["MVK_INVALID_COMPARE_TO_CONST", "MVK_INVALID_COMPARE_TO_CONST",
     "MVK_INVALID_PARAMETER_FOR_PATTERN_COMPARISON", "MVK_INVALID_PARAMETER_FOR_PATTERN_COMPARISON",
     "MVK_INVALID_PARAMETER_FOR_PATTERN_COMPARISON", "MVK_INVALID_PARAMETER_FOR_PATTERN_COMPARISON",
     "MVK_INVALID_TYPE_FOR_PATTERN_COMPARISON", "MVK_INVALID_TYPE_FOR_PATTERN_COMPARISON",
     "MVK_MISSING_CONST_IN_PATTERN_COMP", "pattern", "pattern"] := by native_decide

example :
    [result .tolerance number number, result .tolerance text text,
     result .tolerance field (.field .number), result .tolerance (.field .number) field,
     result .tolerance (.field .number) (.field .number),
     result .ordering field (.field .number), result .equality field (.field .number),
     result .equality (.field .number) (.field .number)] =
    ["MVK_INVALID_COMPARE_TO_CONST", "MVK_INVALID_COMPARE_TO_CONST",
     "MVK_INVALID_TYPE_FOR_TOLERANCE_OP", "MVK_INVALID_TYPE_FOR_TOLERANCE_OP",
     "complete", "MVK_INVALID_TYPE_FOR_COMPARISON", "ordinary", "ordinary"] := by native_decide

end A12Kernel.Conformance.ComparisonEntry
