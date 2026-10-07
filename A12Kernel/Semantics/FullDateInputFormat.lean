import A12Kernel.Semantics.TemporalTarget
import A12Kernel.Semantics.String

namespace A12Kernel

/-- Exact complete-Date formats admitted by the bounded stored-input classifier. This is wider than the
computed-target renderer by the measured compact spelling, so input certification cannot accidentally
widen target authoring. -/
inductive FullDateInputFormat where
  | dayMonthYearDots
  | yearMonthDayDashes
  | yearMonthDayConcatenated
  deriving Repr, DecidableEq

namespace FullDateInputFormat

/-- Admit the three complete-Date declaration spellings measured on stored input. -/
def ofSource? : String → Option FullDateInputFormat
  | "dd.MM.yyyy" => some .dayMonthYearDots
  | "yyyy-MM-dd" => some .yearMonthDayDashes
  | "yyyyMMdd" => some .yearMonthDayConcatenated
  | _ => none

/-- Embed the narrower computed-target format in the stored-input vocabulary. -/
def ofTarget : FullDateTargetFormat → FullDateInputFormat
  | .dayMonthYearDots => .dayMonthYearDots
  | .yearMonthDayDashes => .yearMonthDayDashes

end FullDateInputFormat

/-- Split one fixed-width ASCII date into its three declared components **without** judging them. The
widths and the separator are the whole gate here: a component of the wrong width, a non-ASCII-digit
body, or a wrong field count is rejected, while a zero component or an impossible calendar day still
passes. Partial precision needs exactly this step, because a zero is an omission marker there rather
than an unreal date, so the reality test cannot be folded into the split. -/
def FullDateInputFormat.parseComponents? (format : FullDateInputFormat)
    (text : String) : Option DateParts :=
  let component (width : Nat) (source : String) : Option Nat :=
    if source.length = width then parseAsciiNatural? source else none
  match format with
  | .dayMonthYearDots =>
      match text.splitOn "." with
      | [dayText, monthText, yearText] => do
          let day ← component 2 dayText
          let month ← component 2 monthText
          let year ← component 4 yearText
          pure { year, month, day }
      | _ => none
  | .yearMonthDayDashes =>
      match text.splitOn "-" with
      | [yearText, monthText, dayText] => do
          let year ← component 4 yearText
          let month ← component 2 monthText
          let day ← component 2 dayText
          pure { year, month, day }
      | _ => none
  | .yearMonthDayConcatenated =>
      if text.length = 8 then do
        let year ← component 4 (text.take 4).toString
        let month ← component 2 (text.drop 4 |>.take 2).toString
        let day ← component 2 (text.drop 6).toString
        pure { year, month, day }
      else none

/-- Parse a computed-target format through its corresponding stored-input spelling. -/
def FullDateTargetFormat.parseComponents? (format : FullDateTargetFormat)
    (text : String) : Option DateParts :=
  (FullDateInputFormat.ofTarget format).parseComponents? text

end A12Kernel
