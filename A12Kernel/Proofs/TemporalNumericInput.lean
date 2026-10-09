import A12Kernel.Semantics.TemporalNumericInput

namespace A12Kernel

theorem storedTemporalNumeric_empty (field : FlatTemporalField) (part : TemporalNumericPart)
    (format : Option FullDateTargetFormat) :
    CellObservation.empty.asStoredTemporalNumericOperand field part format = .value 0 .both := rfl

theorem storedTemporalNumeric_unknown (field : FlatTemporalField) (part : TemporalNumericPart)
    (format : Option FullDateTargetFormat) (cause : FormalCause) :
    (CellObservation.unknown cause).asStoredTemporalNumericOperand field part format = .unknown cause := rfl

theorem storedTemporalNumeric_poison (field : FlatTemporalField) (part : TemporalNumericPart)
    (format : Option FullDateTargetFormat) (cause : FormalCause) :
    (CellObservation.poison cause).asStoredTemporalNumericOperand field part format = .unknown cause := rfl

theorem storedTemporalNumeric_value (field : FlatTemporalField) (part : TemporalNumericPart)
    (format : Option FullDateTargetFormat) (payload : Value) (amount : Rat)
    (projected : part.projectStored? field format payload = some amount) :
    (CellObservation.value payload).asStoredTemporalNumericOperand field part format = .value amount .fixed := by
  simp [CellObservation.asStoredTemporalNumericOperand, projected]

theorem storedTemporalNumeric_partial_parse (field : FlatTemporalField) (part : DateNumericPart)
    (format : FullDateTargetFormat) (text : String) (parts : DateParts)
    (parsed : format.parseComponents? text = some parts) :
    (TemporalNumericPart.date part).projectStored? field (some format) (.partialDate text) = some (part.extract parts) := by
  simp [TemporalNumericPart.projectStored?, parsed]

theorem storedTemporalNumeric_partial_time_refused (field : FlatTemporalField) (part : TimeNumericPart)
    (format : Option FullDateTargetFormat) (text : String) :
    (TemporalNumericPart.time part).projectStored? field format (.partialDate text) = none := rfl

theorem storedTemporalNumeric_clock_year (field : FlatTemporalField) (time : TimeOfDay)
    (instant : Instant) (format : Option FullDateTargetFormat)
    (holds : field.holdsValue (.time instant time) = true) :
    (TemporalNumericPart.date .year).projectStored? field format (.temporal (.time instant time)) = some 1970 := by
  simp [TemporalNumericPart.projectStored?, holds, TemporalNumericPart.project?, DateNumericPart.projectTemporal?]

end A12Kernel
