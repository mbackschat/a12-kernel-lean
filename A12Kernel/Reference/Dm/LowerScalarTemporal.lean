import A12Kernel.Reference.Dm.LowerNumeric
import A12Kernel.Elaboration.TemporalNumericExpression

/-! # Scalar temporal source and numeric projection lowering -/

namespace A12Kernel.Dm

private def fieldOperand (model : FlatModel) (group : GroupPath) (construct : String) (expr : Expr) :
    Lowering FlatFieldDecl := do
  let some path := expr.fieldEntity? | refuse construct "operand"
  elaborated construct (model.resolveFieldDeclarationUnchecked group path)

private def temporalNumericPart? (name : String) : Option TemporalNumericPart :=
  match datePart? name with
  | some part => some (.date part)
  | none => match name with
      | "HoursFromTime" => some (.time .hour)
      | "MinutesFromTime" => some (.time .minute)
      | "SecondsFromTime" => some (.time .second)
      | _ => none

/-- Decode every direct component form the checked Date constructor already certifies. -/
private def lowerDateComponent (model : FlatModel) (rowGroup : GroupPath) :
    Expr → Lowering SurfaceConstructedDateSource
  | .string text => pure (.constant text)
  | .call name [.mk operand none none] none none => do
      let some part := datePart? name | refuse "Date" "component extractor"
      match operand with
      | .constant "BaseYear" => pure (.baseYearExtractor part)
      | .constant "Today" => pure (.todayExtractor part)
      | .constant "Now" => pure (.nowExtractor part)
      | .call bound [.mk (.constant "BaseYear") none none] none none =>
          match bound with
          | "StartOfDateRange" => pure (.baseYearRangeExtractor .start part)
          | "EndOfDateRange" => pure (.baseYearRangeExtractor .finish part)
          | _ => refuse "Date" "Base Year endpoint"
      | _ =>
          let some path := operand.fieldEntity? | refuse "Date" "extractor operand"
          let field ← elaborated "Date" (model.resolveFieldDeclarationUnchecked rowGroup path)
          pure (.extractor part field.id)
  | expression => do
      let some path := expression.fieldEntity? | refuse "Date" "component field"
      let field ← elaborated "Date" (model.resolveFieldDeclarationUnchecked rowGroup path)
      match field.policy.kind.surfaceKind with
      | .number => pure (.numberField field.id)
      | .string => pure (.stringField field.id)
      | .temporal _ => pure (.dateYearField field.id)
      | _ => refuse "Date" "component kind"

def lowerDateComponents (model : FlatModel) (rowGroup : GroupPath)
    (arguments : List Argument) : Lowering SurfaceConstructedDateComponents := do
  let some expressions := arguments.mapM (fun | .mk expression none none => some expression | _ => none) | refuse "Date" "component modifier"
  let component := lowerDateComponent model rowGroup
  match expressions with
  | [day, month] => pure { day := ← component day, month := ← component month, year := .baseYear }
  | [day, month, year] => pure {
      day := ← component day, month := ← component month, year := .complete (← component year) }
  | [day, month, century, shortYear] => pure {
      day := ← component day, month := ← component month
      year := .centuryAndShortYear (← component century) (← component shortYear) }
  | _ => refuse "Date" "component arity"

private inductive TemporalExpressionPosition where
  | value
  | source

/-- Field spelling depends on the grammar position (spec/12 §3): value expressions use
brackets, while temporal source slots take an entity. Keep that distinction until lowering. -/
private partial def lowerScalarTemporalExpressionAt (model : FlatModel) (rowGroup : GroupPath)
    (position : TemporalExpressionPosition) (expression : Expr) : Lowering SurfaceScalarTemporalExpression := do
  let lowerSourceSlot (source : Expr) : Lowering SurfaceScalarTemporalExpression :=
    lowerScalarTemporalExpressionAt model rowGroup .source source
  let lowerNumericAtom (expression : Expr) : Lowering (Sum SurfaceNumericAtom (TemporalNumericPart × SurfaceScalarTemporalExpression)) := do
    match expression with
    | .call name [.mk source none none] none none =>
        match temporalNumericPart? name with
        | some part => pure (.inr (part, ← lowerSourceSlot source))
        | none => .inl <$> lowerValidationNumericAtom expression
    | _ => .inl <$> lowerValidationNumericAtom expression
  let lowerTimeComponent : Argument → Lowering (Sum SurfaceTimeComponent (TimeNumericPart × SurfaceScalarTemporalExpression))
    | .mk (.string text) none none => pure (.inl (.constant text))
    | .mk (.call name [.mk source none none] none none) none none => do
        let some (.time part) := temporalNumericPart? name | refuse "Time" "component extractor"
        pure (.inr (part, ← lowerSourceSlot source))
    | .mk expression none none => do
        let declaration ← fieldOperand model rowGroup "Time" expression
        match declaration.policy.kind.surfaceKind with
        | .number => pure (.inl (.number declaration.id))
        | .string => pure (.inl (.string declaration.id))
        | _ => refuse "Time" "component kind"
    | _ => refuse "Time" "component"
  let lowerTimeComponents : List Argument → Lowering (TimeComponentPrefix (Sum SurfaceTimeComponent (TimeNumericPart × SurfaceScalarTemporalExpression)))
    | [] => pure .empty
    | [hour] => do pure (.hour (← lowerTimeComponent hour))
    | [hour, minute] => do pure (.minute (← lowerTimeComponent hour) (← lowerTimeComponent minute))
    | [hour, minute, second] => do
        pure (.second (← lowerTimeComponent hour) (← lowerTimeComponent minute) (← lowerTimeComponent second))
    | _ => refuse "Time" "arity"
  let lowerRangeSlot (bound : DateRangeBound) (source : Expr) : Lowering SurfaceScalarTemporalExpression := do
    match source with
    | .constant "BaseYear" =>
        pure (.baseYearBound (if bound == .start then .start else .finish))
    | _ =>
        let some path := source.fieldEntity? | refuse "TemporalExpression" "range entity"
        pure (.rangeBound path bound)
  match expression with
  | .braces source => (.group ·) <$> lowerScalarTemporalExpressionAt model rowGroup .value source
  | .value { path, index := none, category := none } =>
      match position, path.toFieldPath? with
      | .value, some field => pure (.field field)
      | .source, _ => refuse "TemporalExpression" "bracketed read in temporal source slot"
      | _, none => refuse "TemporalExpression" "field path"
  | .entity { path, index := none, category := none } =>
      match position, path.toFieldPath? with
      | .source, some field => pure (.field field)
      | .value, _ => refuse "TemporalExpression" "bare entity in temporal value expression"
      | _, none => refuse "TemporalExpression" "field path"
  | .call "DateTime" [.mk date none none, .mk time none none] none none =>
      pure (.dateTimeConstruction (← lowerSourceSlot date) (← lowerSourceSlot time))
  | .call "ValueAsDate" [.mk source none none, .mk (.constant endpoint) none none] none none => do
      let some path := source.fieldEntity? | refuse "ValueAsDate" "partial Date entity"
      let endpoint ← match endpoint with
        | "FirstDay" => pure ValueAsDateEndpoint.firstDay
        | "LastDay" => pure ValueAsDateEndpoint.lastDay
        | _ => refuse "ValueAsDate" "endpoint"
      pure (.valueAsDate path endpoint)
  | .call "Date" arguments none none =>
      (.dateConstruction ·) <$> lowerDateComponents model rowGroup arguments
  | .call "Time" arguments none none =>
      (.timeConstruction ·) <$> lowerTimeComponents arguments
  | .constant "Now" => pure .now
  | .constant "Today" => pure .today
  | .call "StartOfDateRange" [.mk source none none] none none => lowerRangeSlot .start source
  | .call "EndOfDateRange" [.mk source none none] none none => lowerRangeSlot .finish source
  | .call "DateFromDateTime" [.mk source none none] none none =>
      (.dateFromDateTime ·) <$> lowerSourceSlot source
  | .call "TimeFromDateTime" [.mk source none none] none none =>
      (.timeFromDateTime ·) <$> lowerSourceSlot source
  | .string text =>
      match dateTimeConstant? text, timeConstant? text, civilDateConstant? text with
      | some value, _, _ => pure (.dateTimeLiteral value)
      | _, some value, _ => pure (.timeLiteral value)
      | _, _, some value => match FullDate.ofCivil? value with
          | some value => pure (.dateLiteral value)
          | none => refuse "TemporalExpression" "literal calendar profile"
      | _, _, _ => refuse "TemporalExpression" "literal"
  | .call name [.mk source none none, .mk amount none none] none none => do
      match name with
      | "Min" | "Max" =>
          pure (.combine (if name == "Min" then .minimum else .maximum)
            (← lowerScalarTemporalExpressionAt model rowGroup .value source)
            (← lowerScalarTemporalExpressionAt model rowGroup .value amount))
      | "AddDays" | "AddMonths" | "AddYears" =>
          let unit := if name == "AddDays" then DateShiftUnit.days
            else if name == "AddMonths" then .months else .years
          pure (.calendarShift unit (← lowerSourceSlot source)
            (← lowerNumericExpr lowerNumericAtom (lowerNumericFieldAtom model rowGroup lowerNumericAtom) amount))
      | "AddHours" | "AddMinutes" | "AddSeconds" =>
          let unit := if name == "AddHours" then DateTimeSubdayUnit.hours
            else if name == "AddMinutes" then .minutes else .seconds
          pure (.subdayShift unit (← lowerSourceSlot source)
            (← lowerNumericExpr lowerNumericAtom (lowerNumericFieldAtom model rowGroup lowerNumericAtom) amount))
      | "MinValue" | "MaxValue" =>
          pure (.extremum (if name == "MinValue" then .minimum else .maximum)
            (← lowerEntitySource model rowGroup [.mk source none none, .mk amount none none]))
      | _ => refuse "TemporalExpression" name
  | .call name operands none none => do
      let operator ← match name with
        | "MinValue" => pure TemporalExtremumOp.minimum
        | "MaxValue" => pure TemporalExtremumOp.maximum
        | _ => refuse "TemporalExpression" name
      pure (.extremum operator (← lowerEntitySource model rowGroup operands))
  | expression => refuse "TemporalExpression" expression.construct

def lowerScalarTemporalExpression (model : FlatModel) (rowGroup : GroupPath)
    (expression : Expr) : Lowering SurfaceScalarTemporalExpression :=
  lowerScalarTemporalExpressionAt model rowGroup .value expression

/-- Reuse established numeric atoms first; recursive temporal operands retain the common source
syntax and enter the same checked projection on both numeric arms. -/
def lowerCompleteComputationNumericAtom (model : FlatModel) (rowGroup : GroupPath)
    (expression : Expr) : Lowering SurfaceNumericComputationAtom :=
  match lowerComputationNumericAtom model rowGroup expression with
  | .ok source => pure source
  | .error original => do
      let .call name [.mk source none none] none none := expression | throw original
      let some part := temporalNumericPart? name | throw original
      pure (.temporalPart (← lowerScalarTemporalExpressionAt model rowGroup .source source) part)

end A12Kernel.Dm
