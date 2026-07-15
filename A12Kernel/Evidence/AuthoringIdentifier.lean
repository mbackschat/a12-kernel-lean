/-! # A12Kernel.Evidence.AuthoringIdentifier — conservative authoring names

Evidence renderers that reconstruct pinned English authoring expressions share this one deliberately narrow identifier policy. It admits only unquoted ASCII identifiers outside the known English terminal vocabulary; full quoted-name escaping remains a separate future boundary.
-/

namespace A12Kernel.Evidence.AuthoringIdentifier

private def hasDuplicate [BEq α] : List α → Bool
  | [] => false
  | value :: rest => rest.contains value || hasDuplicate rest

private def asciiAlpha (character : Char) : Bool :=
  decide (character.toNat < 128) && character.isAlpha

private def asciiAlphanum (character : Char) : Bool :=
  decide (character.toNat < 128) && character.isAlphanum

/-- The ASCII-identifier terminals in the pinned English authoring vocabulary. The non-identifier terminal `@From` is rejected by shape before this lookup. -/
def reserved : List String :=
  ["Abs", "AbsValue", "AddDays", "AddHours", "AddMinutes", "AddMonths", "AddSeconds",
    "AddYears", "AllFieldsFilled", "AllGroupsFilled", "And", "and", "AND",
    "AtLeastOneDateRangeOverlaps", "AtLeastOneFieldFilled",
    "AtLeastOneFieldValueIncludedInValueList", "AtLeastOneGroupFilled", "BaseYear",
    "CurrentRepetition", "CustomCondition", "Date", "DateFromDateTime", "DateRange",
    "DateRangesOverlap", "DateTime", "DayFromDate", "DifferenceInDays", "DifferenceInHours",
    "DifferenceInMinutes", "DifferenceInMonths", "DifferenceInSeconds", "DifferenceInYears",
    "DiffersWithToleranceRange1", "DiffersWithToleranceRange2", "DiffersWithToleranceRange5",
    "DiffersWithToleranceRange10", "EndOfDateRange", "False", "FieldFilled",
    "FieldNotFilled", "FieldValueAsNumber", "FieldValueAsString",
    "FieldValueIncludedInValueList", "FieldValueNotIncludedInValueList",
    "FieldValuesNotUnique", "FieldsNotCollectivelyFilled", "FirstDay", "FirstFilledValue",
    "For", "GroupFilled", "GroupNotFilled", "GroupsNotCollectivelyFilled", "Having",
    "HoursFromTime", "In", "in", "IN", "Invalid", "LastDay", "Length", "Max", "MaxValue",
    "Min", "MinutesFromTime", "MinValue", "MonthFromDate", "MoreThanOneFieldFilled",
    "NoFieldFilled", "NoFieldValueIncludedInValueList", "NoGroupFilled",
    "NotAllFieldValuesIncludedInValueList", "NotAllFieldsFilled", "NotAllGroupsFilled",
    "NotExactlyOneFieldFilled", "Now", "NumberOfDifferentValues", "NumberOfFilledFields",
    "NumberOfFilledGroups", "NumberOfValueInFields", "Or", "or", "OR", "PatternMatched",
    "PatternViolated", "QuarterFromDate", "RangeAsNumber", "RangeAsString",
    "RepetitionNotUnique", "RoundAccounting", "RoundAccountingValue", "RoundDown",
    "RoundDownValue", "RoundUp", "RoundUpValue", "RuleGroup", "SecondsFromTime",
    "StartOfDateRange", "Sum", "SumOfProducts", "SuppressWarning", "Time",
    "TimeFromDateTime", "to", "To", "TO", "Today", "True", "Valid", "ValueAsDate",
    "ValueNotConsistent", "YearFromDate"]

/-- Whether a segment is safe for direct use by the deliberately unquoted evidence renderers. -/
def safe (identifier : String) : Bool :=
  match identifier.toList with
  | [] => false
  | first :: rest =>
      (asciiAlpha first || first == '_') &&
      rest.all (fun character => asciiAlphanum character || character == '_') &&
      !reserved.contains identifier

example : reserved.length = 111 := by native_decide
example : hasDuplicate reserved = false := by native_decide
example : safe "Date" = false := by native_decide
example : safe "Today" = false := by native_decide
example : safe "Length" = false := by native_decide
example : safe "Sum" = false := by native_decide
example : safe "Valid" = false := by native_decide
example : safe "and" = false := by native_decide
example : safe "AND" = false := by native_decide
example : safe "Shipment" = true := by native_decide
example : safe "Source] + True" = false := by native_decide

end A12Kernel.Evidence.AuthoringIdentifier
