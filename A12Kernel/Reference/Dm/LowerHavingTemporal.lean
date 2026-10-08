import A12Kernel.Reference.Dm.LowerHavingNumeric
import A12Kernel.Reference.Dm.LowerCore
import A12Kernel.Elaboration.CorrelationSurface

namespace A12Kernel.Dm

mutual
private partial def lowerHavingDateComponent : Expr → Lowering (SurfaceHavingDateComponent SurfaceHavingTemporalExpression)
  | .string text => pure (.constant text)
  | .entity { path, index := none, category := none, filter := none } => do
      let some (origin, field) := path.havingField? | refuse "Date" "component path"
      pure (.field { origin, field })
  | .call name [.mk operand none] none none => do
      let some part := datePart? name | refuse "Date" "component extractor"
      match operand with
      | .constant "BaseYear" => pure (.baseYearExtractor .direct part)
      | .constant "Today" => pure (.clockExtractor .today part)
      | .constant "Now" => pure (.clockExtractor .now part)
      | .call bound [.mk (.constant "BaseYear") none] none none =>
          match bound with
          | "StartOfDateRange" => pure (.baseYearExtractor (.range .start) part)
          | "EndOfDateRange" => pure (.baseYearExtractor (.range .finish) part)
          | _ => refuse "Date" "Base Year endpoint"
      | .entity { path, index := none, category := none, filter := none } => do
          let some (origin, field) := path.havingField? | refuse "Date" "extractor path"
          pure (.extractor part { origin, field })
      | source => .expression part <$> lowerHavingTemporalExpression true source
  | _ => refuse "Date" "direct component"

partial def lowerHavingDateComponents (arguments : List Argument) : Lowering SurfaceHavingDateComponents := do
  let components ← arguments.mapM fun
    | .mk expression none => lowerHavingDateComponent expression
    | _ => refuse "Date" "component modifier"
  match components with
  | [day, month] => pure { day, month, year := .baseYear }
  | [day, month, year] => pure { day, month, year := .complete year }
  | [day, month, century, shortYear] => pure { day, month, year := .centuryAndShortYear century shortYear }
  | _ => refuse "Date" "component arity"

private partial def lowerHavingTimeComponent : Expr → Lowering (SurfaceHavingTimeComponent SurfaceHavingTemporalExpression)
  | .string text => pure (.constant text)
  | .entity { path, index := none, category := none, filter := none } => do
      let some (origin, field) := path.havingField? | refuse "Time" "component path"
      pure (.field { origin, field })
  | .call name [.mk operand none] none none => do
      let some part := timePart? name | refuse "Time" "component extractor"
      match operand with
      | .constant "Now" => pure (.nowExtractor part)
      | .entity { path, index := none, category := none, filter := none } => do
          let some (origin, field) := path.havingField? | refuse "Time" "extractor path"
          pure (.extractor part { origin, field })
      | source => .expression part <$> lowerHavingTemporalExpression true source
  | _ => refuse "Time" "direct component"

private partial def lowerHavingTimeComponents (arguments : List Argument) : Lowering SurfaceHavingTimeComponents := do
  let components ← arguments.mapM fun
    | .mk expression none => lowerHavingTimeComponent expression
    | _ => refuse "Time" "component modifier"
  match components with
  | [] => pure .empty
  | [hour] => pure (.hour hour)
  | [hour, minute] => pure (.minute hour minute)
  | [hour, minute, second] => pure (.second hour minute second)
  | _ => refuse "Time" "component arity"

/-- Source slots use unbracketed entities and reject grouping, like ordinary temporal lowering
(spec/12 §3). Every field keeps its own captured/candidate origin. -/
partial def lowerHavingTemporalExpression (sourceSlot : Bool) : Expr → Lowering SurfaceHavingTemporalExpression
  | .call "ValueAsDate" [.mk (.entity { path, index := none, category := none, filter := none }) none, .mk (.constant endpoint) none] none none => do
      let some (origin, field) := path.havingField? | refuse "ValueAsDate" "partial Date entity"
      let endpoint ← match endpoint with
        | "FirstDay" => pure ValueAsDateEndpoint.firstDay
        | "LastDay" => pure ValueAsDateEndpoint.lastDay
        | _ => refuse "ValueAsDate" "endpoint"
      pure (.partialDate { origin, field } endpoint)
  | .entity { path, index := none, category := none, filter := none } => do
      if !sourceSlot then refuse "Having" "bare temporal value"
      let some (origin, field) := path.havingField? | refuse "Having" "temporal entity"
      pure (.field { origin, field })
  | .value { path, index := none, category := none, filter := none } => do
      if sourceSlot then refuse "Having" "bracketed temporal source"
      let some (origin, field) := path.havingField? | refuse "Having" "temporal value"
      pure (.field { origin, field })
  | .braces source => do
      if sourceSlot then refuse "Having" "grouped temporal source"
      .grouped <$> lowerHavingTemporalExpression false source
  | expression@(.call "Min" arguments none none) | expression@(.call "Max" arguments none none) => do
      if sourceSlot then refuse "Having" "extremum in temporal source slot"
      let lower : Argument → Lowering SurfaceHavingTemporalExpression
        | .mk operand none => lowerHavingTemporalExpression false operand
        | _ => refuse "Having" "temporal extremum modifier"
      let first :: rest ← arguments.mapM lower | refuse "Having" "empty temporal extremum"
      pure (.combine (if expression.construct == "Min" then .minimum else .maximum) first rest)
  | .call "FirstFilledValue" arguments none none => do
      if sourceSlot then refuse "Having" "selection in temporal source slot"
      .selection .firstFilled <$> lowerHavingEntitySource arguments
  | .call "MinValue" arguments none none => do
      if sourceSlot then refuse "Having" "extremum in temporal source slot"
      .selection (.extremum .minimum) <$> lowerHavingEntitySource arguments
  | .call "MaxValue" arguments none none => do
      if sourceSlot then refuse "Having" "extremum in temporal source slot"
      .selection (.extremum .maximum) <$> lowerHavingEntitySource arguments
  | .call "Time" arguments none none => .timeConstruction <$> lowerHavingTimeComponents arguments
  | .call "Date" arguments none none => .dateConstruction <$> lowerHavingDateComponents arguments
  | .call "DateTime" [.mk date none, .mk time none] none none => do
      pure (.dateTime (← lowerHavingTemporalExpression true date) (← lowerHavingTemporalExpression true time))
  | .call name [.mk source none, .mk amount none] none none => do
      let unit ← match name with
        | "AddDays" => pure TemporalOperationUnit.days
        | "AddMonths" => pure TemporalOperationUnit.months
        | "AddYears" => pure TemporalOperationUnit.years
        | "AddHours" => pure TemporalOperationUnit.hours
        | "AddMinutes" => pure TemporalOperationUnit.minutes
        | "AddSeconds" => pure TemporalOperationUnit.seconds
        | _ => refuse "Having" "temporal binary operator"
      pure (.shift unit (← lowerHavingTemporalExpression true source) (← lowerHavingTemporalAmount amount))
  | .call "DateFromDateTime" [.mk source none] none none =>
      .dateFromDateTime <$> lowerHavingTemporalExpression true source
  | .call "TimeFromDateTime" [.mk source none] none none =>
      .timeFromDateTime <$> lowerHavingTemporalExpression true source
  | .constant "Now" => pure .now
  | .constant "Today" => pure .today
  | .constant "BaseYear" => do
      if !sourceSlot then refuse "Having" "polymorphic BaseYear value"
      pure (.baseYearBound .start)
  | .call "StartOfDateRange" [.mk (.constant "BaseYear") none] none none => pure (.baseYearBound .start)
  | .call "EndOfDateRange" [.mk (.constant "BaseYear") none] none none => pure (.baseYearBound .finish)
  | .call name [.mk (.entity { path, index := none, category := none, filter := none }) none] none none => do
      let bound ← match name with
        | "StartOfDateRange" => pure DateRangeBound.start
        | "EndOfDateRange" => pure DateRangeBound.finish
        | _ => refuse "Having" "temporal operator"
      let some (origin, field) := path.havingField? | refuse "Having" "range endpoint entity"
      pure (.rangeBound { origin, field } bound)
  | .string text =>
      match dateTimeConstant? text, timeConstant? text, authoredDateLiteral? text with
      | some value, _, _ => pure (.dateTimeLiteral value)
      | _, some value, _ => pure (.timeLiteral value)
      | _, _, some value => pure (.dateLiteral value)
      | _, _, _ => refuse "Having" "temporal literal"
  | other => refuse "Having" other.construct

private partial def lowerHavingTemporalAmount (expression : Expr) : Lowering SurfaceHavingTemporalAmount :=
  let atom := lowerHavingNumericAtomWith (lowerHavingTemporalExpression true)
  lowerNumericExpr atom (fun source => do atom (.value (← numericFieldFormReference source))) expression

end

end A12Kernel.Dm
