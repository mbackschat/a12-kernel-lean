import A12Kernel.Reference.Dm.LowerCore
import A12Kernel.Elaboration.CorrelationSurface

namespace A12Kernel.Dm

/-- A filter operand's path without its `$`, and the origin the `$` selects. -/
def Path.havingField? (path : Path) : Option (HavingOrigin × SurfaceFieldPath) := do
  let field ← { path with correlated := false }.toFieldPath?
  pure (if path.correlated then .outer else .inner, field)


/-- Only constructor-containing expressions select the recursive Having route; established direct
comparisons retain their existing admission and diagnostics (spec/04 and spec/05). -/
def Expr.havingTemporalConstructor : Expr → Bool
  | .braces source => source.havingTemporalConstructor
  | .call "StartOfDateRange" [.mk (.constant "BaseYear") none none] none none
  | .call "EndOfDateRange" [.mk (.constant "BaseYear") none none] none none => false
  | .call name _ _ _ => ["Date", "DateTime", "DateFromDateTime", "TimeFromDateTime", "StartOfDateRange", "EndOfDateRange"].contains name
  | _ => false

private def lowerHavingDateComponent : Expr → Lowering SurfaceHavingDateComponent
  | .string text => pure (.constant text)
  | .entity { path, index := none, category := none } => do
      let some (origin, field) := path.havingField? | refuse "Date" "component path"
      pure (.field { origin, field })
  | .call name [.mk operand none none] none none => do
      let some part := datePart? name | refuse "Date" "component extractor"
      match operand with
      | .constant "BaseYear" => pure (.baseYearExtractor .direct part)
      | .constant "Today" => pure (.clockExtractor .today part)
      | .constant "Now" => pure (.clockExtractor .now part)
      | .call bound [.mk (.constant "BaseYear") none none] none none =>
          match bound with
          | "StartOfDateRange" => pure (.baseYearExtractor (.range .start) part)
          | "EndOfDateRange" => pure (.baseYearExtractor (.range .finish) part)
          | _ => refuse "Date" "Base Year endpoint"
      | .entity { path, index := none, category := none } => do
          let some (origin, field) := path.havingField? | refuse "Date" "extractor path"
          pure (.extractor part { origin, field })
      | _ => refuse "Date" "direct extractor operand"
  | _ => refuse "Date" "direct component"

def lowerHavingDateComponents (arguments : List Argument) : Lowering SurfaceHavingDateComponents := do
  let components ← arguments.mapM fun
    | .mk expression none none => lowerHavingDateComponent expression
    | _ => refuse "Date" "component modifier"
  match components with
  | [day, month] => pure { day, month, year := .baseYear }
  | [day, month, year] => pure { day, month, year := .complete year }
  | [day, month, century, shortYear] => pure { day, month, year := .centuryAndShortYear century shortYear }
  | _ => refuse "Date" "component arity"

/-- Source slots use unbracketed entities and reject grouping, like ordinary temporal lowering
(spec/12 §3). Every field keeps its own captured/candidate origin. -/
def lowerHavingTemporalExpression (sourceSlot : Bool) : Expr → Lowering SurfaceHavingTemporalExpression
  | .entity { path, index := none, category := none } => do
      if !sourceSlot then refuse "Having" "bare temporal value"
      let some (origin, field) := path.havingField? | refuse "Having" "temporal entity"
      pure (.field { origin, field })
  | .value { path, index := none, category := none } => do
      if sourceSlot then refuse "Having" "bracketed temporal source"
      let some (origin, field) := path.havingField? | refuse "Having" "temporal value"
      pure (.field { origin, field })
  | .braces source => do
      if sourceSlot then refuse "Having" "grouped temporal source"
      .grouped <$> lowerHavingTemporalExpression false source
  | .call "Date" arguments none none => .dateConstruction <$> lowerHavingDateComponents arguments
  | .call "DateTime" [.mk date none none, .mk time none none] none none => do
      pure (.dateTime (← lowerHavingTemporalExpression true date) (← lowerHavingTemporalExpression true time))
  | .call "DateFromDateTime" [.mk source none none] none none =>
      .dateFromDateTime <$> lowerHavingTemporalExpression true source
  | .call "TimeFromDateTime" [.mk source none none] none none =>
      .timeFromDateTime <$> lowerHavingTemporalExpression true source
  | .constant "Now" => pure .now
  | .constant "Today" => pure .today
  | .call "StartOfDateRange" [.mk (.constant "BaseYear") none none] none none => pure (.baseYearBound .start)
  | .call "EndOfDateRange" [.mk (.constant "BaseYear") none none] none none => pure (.baseYearBound .finish)
  | .call name [.mk (.entity { path, index := none, category := none }) none none] none none => do
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

end A12Kernel.Dm
