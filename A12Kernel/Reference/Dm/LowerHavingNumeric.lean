import A12Kernel.Reference.Dm.LowerCore
import A12Kernel.Elaboration.CorrelationSurface

namespace A12Kernel.Dm

def Path.havingField? (path : Path) : Option (HavingOrigin × SurfaceFieldPath) := do
  let field ← { path with correlated := false }.toFieldPath?
  pure (if path.correlated then .outer else .inner, field)


def lowerHavingEntitySource (arguments : List Argument) : Lowering SurfaceHavingEntitySource := do
  let operands ← arguments.mapM fun
    | .mk (.constant "RuleGroup") none none => pure (.group .inner (.ruleGroup false))
    | .mk (.entity { path, index := none, category }) none none => do
        if path.segments.any (·.star) then
          pure (.star (if path.correlated then .outer else .inner)
            { base := path.base, groups := path.starGroups }
            (category.map FieldEntityReadForm.projected |>.getD .stored))
        else
          let some (origin, field) := path.havingField? |
            refuse "Having" "field-list entity"
          pure (.entity { origin, field, form := category.map FieldEntityReadForm.projected |>.getD .stored })
    | _ => refuse "Having" "field-list operand"
  let first :: rest := operands | refuse "Having" "empty field list"
  pure { first, rest }


/-- Constructors and model-classified temporal selectors use the recursive Having route.
Established direct comparisons retain their admission and diagnostics (spec/04 and spec/05). -/
def Expr.havingTemporalConstructor (isTemporalSelection : List Argument → Bool := fun _ => false) : Expr → Bool
  | .braces source => source.havingTemporalConstructor isTemporalSelection
  | .call "StartOfDateRange" [.mk (.constant "BaseYear") none none] none none
  | .call "EndOfDateRange" [.mk (.constant "BaseYear") none none] none none => false
  | .call name arguments none none =>
      (["FirstFilledValue", "MinValue", "MaxValue", "Min", "Max"].contains name && isTemporalSelection arguments) ||
        ["AddDays", "AddMonths", "AddYears", "AddHours", "AddMinutes", "AddSeconds", "ValueAsDate", "Time", "Date", "DateTime", "DateFromDateTime", "TimeFromDateTime", "StartOfDateRange", "EndOfDateRange"].contains name
  | _ => false

def Path.havingGroup? (path : Path) : Option (HavingOrigin × SurfaceGroupReference) := do
  let group ← { path with correlated := false }.toGroupPath?
  pure (if path.correlated then .outer else .inner, .path group)

def lowerHavingNumericAtomWith (temporal : Expr → Lowering Temporal) : Expr → Lowering (SurfaceHavingNumericAtomOf Temporal)
  | .call "FirstFilledValue" arguments none none => .firstFilled <$> lowerHavingEntitySource arguments
  | .call "NumberOfFilledGroups" arguments none none => .groupCount <$> lowerHavingEntitySource arguments
  | .call "SumOfProducts" arguments none none => .product <$> lowerHavingEntitySource arguments
  | .call "NumberOfFilledFields" arguments none none =>
      (.collectionCount ∘ .filledFields) <$> lowerHavingEntitySource arguments
  | .call "NumberOfValueInFields" [.mk expected none none] (some listed) none => do
      let source ← lowerHavingEntitySource listed
      let count ← match expected with
        | .number text => do
            let some literal := decodeNumber? text | refuse "NumberOfValueInFields" "expected value"
            pure (.numberValue literal.value source)
        | .string value =>
            if isTemporalConstant value then refuse "NumberOfValueInFields" "temporal constant"
            else pure (.tokenValue value source)
        | .constant "True" => pure (.booleanValue true source)
        | .constant "False" => pure (.booleanValue false source)
        | _ => refuse "NumberOfValueInFields" "expected value"
      pure (.collectionCount count)
  | .call id arguments none none => do
      if let [.mk source none none] := arguments then
        let directRangeBound := match source with
          | .call name _ _ _ => name == "StartOfDateRange" || name == "EndOfDateRange"
          | _ => false
        if source.havingTemporalConstructor (fun _ => true) && !directRangeBound then
          if let some part := ((datePart? id).map TemporalNumericPart.date).orElse (fun _ => (timePart? id).map TemporalNumericPart.time) then
            return .temporalExpressionPart part (← temporal source)
      if let some op := aggregateOp? id then do
        pure (.aggregate op (← lowerHavingEntitySource arguments))
      else lowerNonAggregateHavingNumericAtom (.call id arguments none none)
  | other => lowerNonAggregateHavingNumericAtom other
where
  lowerNonAggregateHavingNumericAtom : Expr → Lowering (SurfaceHavingNumericAtomOf Temporal)
    | .call id [.mk left none none, .mk right none none] none none => do
        let field : Expr → Option SurfaceHavingTemporalRef
          | .entity { path, index := none, category := none } => do
              let (origin, field) ← path.havingField?
              pure { origin, field }
          | _ => none
        if (dateDifferenceOperandWith? field left).isNone || (dateDifferenceOperandWith? field right).isNone then
          let unit ← match id with
            | "DifferenceInDays" => pure TemporalOperationUnit.days
            | "DifferenceInMonths" => pure TemporalOperationUnit.months
            | "DifferenceInYears" => pure TemporalOperationUnit.years
            | "DifferenceInHours" => pure TemporalOperationUnit.hours
            | "DifferenceInMinutes" => pure TemporalOperationUnit.minutes
            | "DifferenceInSeconds" => pure TemporalOperationUnit.seconds
            | _ => refuse "Having" "difference unit"
          return .temporalDifference unit (← temporal left) (← temporal right)
        if id == "DifferenceInDays" || (calendarUnit? id).isSome then
          let some left := dateDifferenceOperandWith? field left | refuse "Having" "difference left"
          let some right := dateDifferenceOperandWith? field right | refuse "Having" "difference right"
          if id == "DifferenceInDays" then return .dayDifference left right
          let some unit := calendarUnit? id | refuse "Having" "difference unit"
          return .dateDifference unit left right
        let some left := dateDifferenceOperandWith? field left | refuse "Having" "difference left"
        let some right := dateDifferenceOperandWith? field right | refuse "Having" "difference right"
        let some unit := subdayUnit? id | refuse "Having" "difference unit"
        pure (.dateTimeDifference unit left right)
    | .constant "BaseYear" => pure .baseYear
    | .call id [.mk (.constant "BaseYear") none none] none none => do
        let some part := datePart? id | refuse "Having" "BaseYear component"
        pure (.baseYearDatePart .direct part)
    | .call id [.mk (.constant source) none none] none none => do
        let source ← match source with
          | "Today" => pure HavingClockSource.today
          | "Now" => pure HavingClockSource.now
          | _ => refuse "Having" "clock source"
        let some part := (datePart? id).map TemporalNumericPart.date |>.orElse
          (fun _ => (timePart? id).map TemporalNumericPart.time) | refuse "Having" "clock component"
        pure (.clockPart source part)
    | .call id [.mk (.call bound [.mk (.constant "BaseYear") none none] none none) none none] none none => do
        let some part := datePart? id | refuse "Having" "BaseYear component"
        let source ← match bound with
          | "StartOfDateRange" => pure (.range .start)
          | "EndOfDateRange" => pure (.range .finish)
          | _ => refuse "Having" "BaseYear endpoint"
        pure (.baseYearDatePart source part)
    | .call id [.mk (.call bound [.mk (.entity { path, index := none, category := none }) none none] none none) none none] none none => do
        let some part := datePart? id | refuse "Having" "DateRange component"
        let some (origin, field) := path.havingField? | refuse "Having" "DateRange field"
        let bound ← match bound with
          | "StartOfDateRange" => pure DateRangeBound.start
          | "EndOfDateRange" => pure DateRangeBound.finish
          | _ => refuse "Having" "DateRange endpoint"
        pure (.dateRangeBoundPart origin field bound part)
    | .call "FieldValueAsNumber" [.mk (.entity { path, index := none, category }) none none] none none => do
        let some (origin, field) := path.havingField? | refuse "Having" "conversion field"
        pure (.fieldValueAsNumber {
          origin, field, projectionRef := category.map EnumerationProjectionRef.category |>.getD .stored })
    | .call "Length" [.mk (.entity { path, index := none, category := none }) none none] none none =>
        match path.havingField? with
        | some (origin, field) => pure (.stringLength origin field)
        | none => refuse "Having" "Length field"
    | .value { path, index := none, category := none } =>
        match path.havingField? with
        | some (origin, field) => pure (.field { origin, field })
        | none => refuse "Having" "numeric field"
    | .call "CurrentRepetition" [.mk (.entity { path, index := none, category := none })
          none none] none none =>
        match path.havingGroup? with
        | some (origin, group) => pure (.repetition { origin, group })
        | none => refuse "Having" "CurrentRepetition"
    | .call "RangeAsNumber" [.mk (.entity { path, index := none, category := none }) none none,
          .mk (.number start) none none, .mk (.number finish) none none] none none => do
        let some (origin, field) := path.havingField? | refuse "Having" "range field"
        let some start := start.toNat? | refuse "Having" "range start"
        let some finish := finish.toNat? | refuse "Having" "range finish"
        pure (.stringRange origin field start finish)
    | .call id [.mk (.entity { path, index := none, category := none }) none none] none none => do
        let some (origin, field) := path.havingField? | refuse "Having" "temporal field"
        let some part := (datePart? id).map TemporalNumericPart.date |>.orElse
          (fun _ => (timePart? id).map TemporalNumericPart.time) | refuse "Having" "numeric source"
        pure (.temporalPart origin field part)
    | .call id [.mk source none none] none none => do
        let some part := (datePart? id).map TemporalNumericPart.date |>.orElse
          (fun _ => (timePart? id).map TemporalNumericPart.time) | refuse "Having" "numeric source"
        pure (.temporalExpressionPart part (← temporal source))
    | other => refuse "Having" other.construct

end A12Kernel.Dm
