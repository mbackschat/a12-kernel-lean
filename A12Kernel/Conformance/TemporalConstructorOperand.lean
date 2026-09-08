import A12Kernel.Elaboration.TemporalConstructorOperand

/-! # Locks on the temporal constructor's per-position operand gate

Every row below is a cell of the measured seven-operator by eight-position grid, dispatched in one
`dmtool batch` with an accepted control per constructor
([checkpoint](../../docs/SOURCES.md#src-temporal-constructor-operand-positions)).
-/

namespace A12Kernel.Conformance.TemporalConstructorOperand

open A12Kernel

/-- The grid the sweep measured: every extraction operator at every position of every constructor. -/
private def grid : List (TemporalConstructor × Nat × TemporalComponent) :=
  [TemporalConstructor.date, .time, .dateTime].flatMap fun constructor =>
    (List.range constructor.arity).flatMap fun position =>
      TemporalComponent.all.map fun operand => (constructor, position, operand)

private def refusalsAt (constructor : TemporalConstructor) (position : Nat) :
    List (Option ConstructorOperandRefusal) :=
  TemporalComponent.all.map (constructorOperandRefusal constructor position ·)

/- **Each component position admits exactly one operator, its own.** Across all six component
   positions the admitted set is a singleton, which is the property a per-position table has and a
   per-constructor allow-list does not. -/
example :
    ([TemporalConstructor.date, .time].flatMap fun constructor =>
      (List.range 3).map fun position =>
        (refusalsAt constructor position).count none) = [1, 1, 1, 1, 1, 1] := by
  native_decide

/- **The measured Date row, in full.** `DayFromDate` admitted at the day slot; the two sibling date
   components draw the wrong-position class; `QuarterFromDate` and all three time operators draw the
   not-allowed class. This single row carries the whole split. -/
example :
    refusalsAt .date 0 =
      [none, some .extractOpWrongPosition, some .extractOpWrongPosition,
       some .extractOpNotAllowed, some .extractOpNotAllowed, some .extractOpNotAllowed,
       some .extractOpNotAllowed] := by
  native_decide

/- The mirror row on `Time`, which is what makes the rule symmetric rather than a fact about dates:
   here the *time* siblings draw the wrong-position class and every date operator the not-allowed one. -/
example :
    refusalsAt .time 1 =
      [some .extractOpNotAllowed, some .extractOpNotAllowed, some .extractOpNotAllowed,
       some .extractOpNotAllowed, some .extractOpWrongPosition, none,
       some .extractOpWrongPosition] := by
  native_decide

/- **Which operator each position admits, in order, for both component constructors.** The middle
   position is a reversal's fixed point, so a row pinning it alone leaves the slot *order* unlocked;
   these are the measured admissions at every position and they fix the order outright. -/
example :
    (TemporalConstructor.date.componentSlots.map (·.extractor) =
        ["DayFromDate", "MonthFromDate", "YearFromDate"]) ∧
      (TemporalConstructor.time.componentSlots.map (·.extractor) =
        ["HoursFromTime", "MinutesFromTime", "SecondsFromTime"]) := by
  native_decide

/- **`QuarterFromDate` is admitted at no component position and never draws the wrong-position
   class**, although it shares the date family with the three components `Date` does admit. Without
   this row the family test alone would be indistinguishable from the measured rule. At `DateTime`'s
   value slots it draws that constructor's own class like every other operator, which is why the
   filter is over the component constructors rather than the whole grid. -/
example :
    (grid.filter fun (constructor, position, operand) =>
      constructor != .dateTime && operand == .quarter &&
        constructorOperandRefusal constructor position operand != some .extractOpNotAllowed) = [] := by
  native_decide

/- **`DateTime` reports the date-kind class in both slots**, including the time slot, where the family
   rule would have predicted a time class. Its slot table is empty because its positions take values
   rather than components. -/
example :
    refusalsAt .dateTime 0 = List.replicate 7 (some .invalidDateForOp) ∧
      refusalsAt .dateTime 1 = List.replicate 7 (some .invalidDateForOp) := by
  native_decide

/- The two component constructors never report the date-kind class, and `DateTime` reports nothing
   else — so the class partitions the constructors rather than the positions. -/
example :
    (grid.filter fun (constructor, position, operand) =>
      (constructorOperandRefusal constructor position operand == some .invalidDateForOp) !=
        (constructor == .dateTime)) = [] := by
  native_decide

/- Operand counts: `Time` admits any nonempty prefix and the other two admit only their full list.
   The `Date`-at-two row is the measured one; the rest is the slot table's own consequence. -/
example :
    (List.range 5).map (operandCountAdmitted .time ·) = [false, true, true, true, false] ∧
      (List.range 5).map (operandCountAdmitted .date ·) = [false, false, false, true, false] ∧
      (List.range 4).map (operandCountAdmitted .dateTime ·) = [false, false, true, false] := by
  native_decide

/- The extractor names and the three catalog keys, which a consumer must produce verbatim. The two
   keys differing only by word order are the pair this family is most likely to swap. -/
example :
    (TemporalComponent.all.map (·.extractor)).eraseDups.length = 7 ∧
      ConstructorOperandRefusal.extractOpWrongPosition.catalogKey =
        "MVK_INVALID_DATE_OR_TIME_EXTRACT_OP" ∧
      ConstructorOperandRefusal.extractOpNotAllowed.catalogKey =
        "MVK_DATE_OR_TIME_EXTRACT_OP_NOT_ALLOWED" := by
  native_decide

end A12Kernel.Conformance.TemporalConstructorOperand
