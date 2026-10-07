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
  | .call name _ _ _ => ["DateTime", "DateFromDateTime", "TimeFromDateTime", "StartOfDateRange", "EndOfDateRange"].contains name
  | _ => false

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
