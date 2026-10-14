import A12Kernel.Reference.Dm.LowerNumeric
import A12Kernel.Reference.Dm.LowerHavingNumeric
import A12Kernel.Elaboration.TemporalNumericExpression
import A12Kernel.Elaboration.NumericComputation.Core
import A12Kernel.Elaboration.DateRangePredicate

/-! # Scalar temporal source and numeric projection lowering -/

namespace A12Kernel.Dm

def lowerDateRangeEndpoint (model : FlatModel) (group : GroupPath)
    (expression : Expr) : Lowering SurfaceDateRangeEndpoint := do
  match expression with
  | .entity { path, index := some key, category := none, filter := none } =>
      pure (.indexed (← lowerIndexedSource model group path key))
  | _ =>
      let some path := expression.fieldEntity? | refuse "DateRange" "endpoint operand"
      pure (.field path)

private def rangeConstruction? : Expr → Option (Expr × Expr)
  | .braces source => rangeConstruction? source
  | .call "DateRange" [.mk start none, .mk finish none] none none => some (start, finish)
  | _ => none

/-- Preserve source-slot versus stored-value grammar and selected-key refusals before choosing a range comparison carrier. -/
def lowerDateRangeComparison? (model : FlatModel) (group : GroupPath)
    (operator : CompareOp) (left right : Expr) : Option (Lowering (EqualityOp × SurfaceDateRangeComparison)) := do
  let operator ← match operator with | .eq => some EqualityOp.equal | .ne => some .notEqual | _ => none
  let endpoint := lowerDateRangeEndpoint model group
  let source : Lowering SurfaceDateRangeComparison ← match rangeConstruction? left, rangeConstruction? right with
    | some (start, finish), some (otherStart, otherFinish) => some (do
        pure (.constructed (← endpoint start) (← endpoint finish) (← endpoint otherStart) (← endpoint otherFinish)))
    | some (start, finish), none => do
        let stored ← right.fieldValue?
        some (do pure (.mixed (← endpoint start) (← endpoint finish) stored .left))
    | none, some (start, finish) => do
        let stored ← left.fieldValue?
        some (do pure (.mixed (← endpoint start) (← endpoint finish) stored .right))
    | none, none => do
        let left ← left.fieldValue?
        let right ← right.fieldValue?
        let declaration ← (model.resolveFieldDeclarationUnchecked group left).toOption
        if declaration.policy.kind != .dateRange then none else some (pure (.stored left right))
  pure (do pure (operator, ← source))

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
  | .call name [.mk operand none] none none => do
      let some part := datePart? name | refuse "Date" "component extractor"
      match operand with
      | .constant "BaseYear" => pure (.baseYearExtractor part)
      | .constant "Today" => pure (.todayExtractor part)
      | .constant "Now" => pure (.nowExtractor part)
      | .call bound [.mk (.constant "BaseYear") none] none none =>
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

private def lowerDateComponentsWith (component : Expr → Lowering Source)
    (arguments : List Argument) : Lowering (SurfaceConstructedDateComponents Source) := do
  let some expressions := arguments.mapM (fun | .mk expression none => some expression | _ => none) | refuse "Date" "component modifier"
  match expressions with
  | [day, month] => pure { day := ← component day, month := ← component month, year := .baseYear }
  | [day, month, year] => pure {
      day := ← component day, month := ← component month, year := .complete (← component year) }
  | [day, month, century, shortYear] => pure {
      day := ← component day, month := ← component month
      year := .centuryAndShortYear (← component century) (← component shortYear) }
  | _ => refuse "Date" "component arity"


def lowerDateComponents (model : FlatModel) (rowGroup : GroupPath)
    (arguments : List Argument) : Lowering SurfaceConstructedDateComponents :=
  lowerDateComponentsWith (lowerDateComponent model rowGroup) arguments

private inductive TemporalExpressionPosition where
  | value
  | source

/-- An entity-list call whose operand carries a `Having`. The Having atom family cannot carry a
filter, so such an amount lowers to the ordinary filtered carriers instead. -/
private def filteredEntityCall? : Expr → Bool
  | .call _ arguments listed _ => (arguments ++ listed.getD []).any fun
      | .mk (.entity reference) _ => reference.filter.isSome
      | _ => false
  | _ => false

private def lowerFilteredShiftAmount (model : FlatModel) (rowGroup : GroupPath) (expression : Expr) :
    Lowering SurfaceFilteredShiftAmount := do
  match ← lowerComputationNumericAtom model rowGroup expression with
  | .numeric (.aggregate op source) => pure (.aggregate op source)
  | .firstFilled source => pure (.firstFilled source)
  | .valueCount expected source => pure (.valueCount expected source)
  | .tokenValueCount expected source => pure (.tokenValueCount expected source)
  | .tokenEntityValueCount expected source => pure (.tokenEntityValueCount expected source)
  | .booleanValueCount expected source => pure (.booleanValueCount expected source)
  | .filledFieldCount source => pure (.filledFieldCount source)
  | _ => refuse "TemporalExpression" "filtered shift amount"

/-- Field spelling depends on the grammar position (spec/12 §3): value expressions use
brackets, while temporal source slots take an entity. Keep that distinction until lowering. -/
private partial def lowerScalarTemporalExpressionAt (model : FlatModel) (rowGroup : GroupPath)
    (position : TemporalExpressionPosition) (expression : Expr) : Lowering SurfaceScalarTemporalExpression := do
  let lowerSourceSlot (source : Expr) : Lowering SurfaceScalarTemporalExpression :=
    lowerScalarTemporalExpressionAt model rowGroup .source source
  let lowerNumericAtom := lowerHavingNumericAtomWith lowerSourceSlot
  let lowerAmount : Expr → Lowering (AuthoredNumericExpr
      (Sum (SurfaceHavingNumericAtomOf SurfaceScalarTemporalExpression) SurfaceFilteredShiftAmount)) :=
    lowerNumericExpr
      (fun atom => if filteredEntityCall? atom then .inr <$> lowerFilteredShiftAmount model rowGroup atom
        else .inl <$> lowerNumericAtom atom)
      (fun atom => .inl <$> lowerNumericFieldAtom model rowGroup lowerNumericAtom atom)
  let lowerTimeComponent : Argument → Lowering (SurfaceScalarTimeComponent)
    | .mk (.string text) none => pure (.inl (.inl (.constant text)))
    | .mk (.call name [.mk source none] none none) none => do
        let some (.time part) := temporalNumericPart? name | refuse "Time" "component extractor"
        pure (.inr (part, ← lowerSourceSlot source))
    | .mk (.entity { path, index := some key, category := none, filter := none }) none => do
        pure (.inl (.inr (← lowerIndexedSource model rowGroup path key)))
    | .mk expression none => do
        let declaration ← fieldOperand model rowGroup "Time" expression
        match declaration.policy.kind.surfaceKind with
        | .number => pure (.inl (.inl (.number declaration.id)))
        | .string => pure (.inl (.inl (.string declaration.id)))
        | _ => refuse "Time" "component kind"
    | _ => refuse "Time" "component"
  let lowerTimeComponents : List Argument → Lowering (TimeComponentPrefix (SurfaceScalarTimeComponent))
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
    | .entity { path, index := some key, category := none, filter := none } =>
        pure (.indexedRangeBound (← lowerIndexedSource model rowGroup path key) bound)
    | _ =>
        let some path := source.fieldEntity? | refuse "TemporalExpression" "range entity"
        pure (.rangeBound path bound)
  match expression with
  | .braces source => (.group ·) <$> lowerScalarTemporalExpressionAt model rowGroup .value source
  | .value { path, index := some key, category := none, filter := none } =>
      match position with
      | .value => (.indexed ·) <$> lowerIndexedSource model rowGroup path key
      | .source => refuse "TemporalExpression" "bracketed read in temporal source slot"
  | .entity { path, index := some key, category := none, filter := none } =>
      match position with
      | .source => (.indexed ·) <$> lowerIndexedSource model rowGroup path key
      | .value => refuse "TemporalExpression" "bare entity in temporal value expression"
  | .value { path, index := none, category := none, filter := none } =>
      match position, path.toFieldPath? with
      | .value, some field => pure (.field field)
      | .source, _ => refuse "TemporalExpression" "bracketed read in temporal source slot"
      | _, none => refuse "TemporalExpression" "field path"
  | .entity { path, index := none, category := none, filter := none } =>
      match position, path.toFieldPath? with
      | .source, some field => pure (.field field)
      | .value, _ => refuse "TemporalExpression" "bare entity in temporal value expression"
      | _, none => refuse "TemporalExpression" "field path"
  | .call "DateTime" [.mk date none, .mk time none] none none =>
      pure (.dateTimeConstruction (← lowerSourceSlot date) (← lowerSourceSlot time))
  | .call "ValueAsDate" [.mk source none, .mk (.constant endpoint) none] none none => do
      let endpoint ← match endpoint with
        | "FirstDay" => pure ValueAsDateEndpoint.firstDay
        | "LastDay" => pure ValueAsDateEndpoint.lastDay
        | _ => refuse "ValueAsDate" "endpoint"
      match source with
      | .entity { path, index := some key, category := none, filter := none } =>
          pure (.indexedValueAsDate (← lowerIndexedSource model rowGroup path key) endpoint)
      | _ =>
          let some path := source.fieldEntity? | refuse "ValueAsDate" "partial Date entity"
          pure (.valueAsDate path endpoint)
  | .call "Date" arguments none none =>
      (.dateConstruction ·) <$> lowerDateComponentsWith (fun component => do
        match component with
        | .entity { path, index := some key, category := none, filter := none } =>
            pure (.inl (.inr (← lowerIndexedSource model rowGroup path key)))
        | _ =>
            match lowerDateComponent model rowGroup component with
            | .ok source => pure (.inl (.inl source))
            | .error _ =>
                let .call name [.mk source none] none none := component | refuse "Date" "component source"
                let some part := datePart? name | refuse "Date" "component extractor"
                pure (.inr (part, ← lowerSourceSlot source))) arguments
  | .call "Time" arguments none none =>
      (.timeConstruction ·) <$> lowerTimeComponents arguments
  | .constant "Now" => pure .now
  | .constant "Today" => pure .today
  | .constant "BaseYear" =>
      match position with
      | .source => pure (.baseYearBound .start)
      | .value => refuse "TemporalExpression" "polymorphic BaseYear value"
  | .call "StartOfDateRange" [.mk source none] none none => lowerRangeSlot .start source
  | .call "EndOfDateRange" [.mk source none] none none => lowerRangeSlot .finish source
  | .call "DateFromDateTime" [.mk source none] none none =>
      (.dateFromDateTime ·) <$> lowerSourceSlot source
  | .call "TimeFromDateTime" [.mk source none] none none =>
      (.timeFromDateTime ·) <$> lowerSourceSlot source
  | .string text =>
      match dateTimeConstant? text, timeConstant? text, authoredDateLiteral? text with
      | some value, _, _ => pure (.dateTimeLiteral value)
      | _, some value, _ => pure (.timeLiteral value)
      | _, _, some source => match (source.completedDate? model).bind FullDate.ofCivil? with
          | some value => pure (.dateLiteral value source.year.isSome)
          | none => refuse "TemporalExpression" "literal calendar profile"
      | _, _, _ => refuse "TemporalExpression" "literal"
  | .call "Min" operands none none | .call "Max" operands none none => do
      let name := expression.construct
      let first :: rest := operands | refuse name "empty operand list"
      let lowerOperand : Argument → Lowering SurfaceScalarTemporalExpression
        | .mk operand none => lowerScalarTemporalExpressionAt model rowGroup .value operand
        | _ => refuse name "operand modifier"
      pure (.combine (if name == "Min" then .minimum else .maximum)
        (← lowerOperand first) (← rest.mapM lowerOperand))
  | .call name [.mk source none, .mk amount none] none none => do
      match name with
      | "AddDays" | "AddMonths" | "AddYears" =>
          let unit := if name == "AddDays" then DateShiftUnit.days
            else if name == "AddMonths" then .months else .years
          pure (.calendarShift unit (← lowerSourceSlot source)
            (← lowerAmount amount))
      | "AddHours" | "AddMinutes" | "AddSeconds" =>
          let unit := if name == "AddHours" then DateTimeSubdayUnit.hours
            else if name == "AddMinutes" then .minutes else .seconds
          pure (.subdayShift unit (← lowerSourceSlot source)
            (← lowerAmount amount))
      | "MinValue" | "MaxValue" =>
          pure (.extremum (if name == "MinValue" then .minimum else .maximum)
            (← lowerEntitySource model rowGroup [.mk source none, .mk amount none]))
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

def lowerScalarDateComponents (model : FlatModel) (rowGroup : GroupPath)
    (arguments : List Argument) : Lowering (SurfaceConstructedDateComponents SurfaceScalarDateComponent) := do
  let .dateConstruction components ← lowerScalarTemporalExpression model rowGroup (.call "Date" arguments none none)
    | refuse "Date" "component source"
  pure components

/-- Reuse established numeric atoms first; recursive temporal operands retain the common source
syntax and enter the same checked projection on both numeric arms. -/
def lowerCompleteComputationNumericAtom (model : FlatModel) (rowGroup : GroupPath)
    (expression : Expr) (bindingGroup? : Option GroupPath := none) : Lowering SurfaceNumericComputationAtom := do
  let surface ← lower
  if let some bindingGroup := bindingGroup? then
    discard <| (model.numericComputationAtomType rowGroup bindingGroup surface).mapError fun error => {
      construct := "NumericOperand"
      detail := error.diagnostic?.map (·.kernelCode) |>.getD (oneLine ((repr error).pretty 100000)) }
  pure surface
where
  lower : Lowering SurfaceNumericComputationAtom :=
    match lowerComputationNumericAtom model rowGroup expression bindingGroup? with
    | .ok source => pure source
    | .error original => do
        match expression with
        | .call name [.mk source none] none none =>
            let some part := temporalNumericPart? name | throw original
            let source ← lowerScalarTemporalExpressionAt model rowGroup .source source
            if !source.admittedSourceSlot .ordinary then refuse "Syntax" SyntaxErrorClass.unexpectedToken.code
            pure (.temporalExpression (.projection part source))
        | .call name [.mk left none, .mk right none] none none =>
            let unit ← match name with
              | "DifferenceInDays" => pure TemporalOperationUnit.days
              | "DifferenceInMonths" => pure TemporalOperationUnit.months
              | "DifferenceInYears" => pure TemporalOperationUnit.years
              | "DifferenceInHours" => pure TemporalOperationUnit.hours
              | "DifferenceInMinutes" => pure TemporalOperationUnit.minutes
              | "DifferenceInSeconds" => pure TemporalOperationUnit.seconds
              | _ => throw original
            pure (.temporalExpression (.difference unit
              (← lowerScalarTemporalExpressionAt model rowGroup .source left)
              (← lowerScalarTemporalExpressionAt model rowGroup .source right)))
        | _ => throw original

end A12Kernel.Dm
