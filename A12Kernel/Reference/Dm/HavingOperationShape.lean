import A12Kernel.Reference.Dm.HavingListAdmission
import A12Kernel.Reference.Dm.HavingScalarAdmission
import A12Kernel.Reference.Dm.HavingConstructorAdmission

namespace A12Kernel.Dm
open HavingListAdmission

mutual
private partial def rawScalarAtomAvailable : Expr → Bool
  | .entity _ | .value _ | .string _ => true
  | .constant name => ["True", "False", "Today", "Now", "BaseYear"].contains name
  | .call "NumberOfValueInFields" [.mk expected none] (some arguments) none =>
      (match expected with | .number _ | .string _ | .constant _ => true | _ => false) &&
      arguments.all (fun | .mk (.entity _) none | .mk (.constant "RuleGroup") none => true | _ => false)
  | source@(.call id arguments none none) =>
      if id == "CurrentRepetition" then arguments.length == 1 && arguments.all (fun
        | .mk (.entity _) none | .mk (.constant "RuleGroup") none => true | _ => false)
      else if id == "DateRange" then arguments.length == 2 && arguments.all (fun
        | .mk (.entity _) none | .mk (.constant "RuleGroup") none => true | _ => false)
      else if let some (.difference _) := rawTemporalArithmetic? id then
        match arguments with
        | [.mk left none, .mk right none] =>
            rawTemporalSourceAvailable true left && rawTemporalSourceAvailable true right
        | _ => false
      -- A standalone `ValueAsDate` completes its partial date, so its own gates run on the raw route
      -- (KF599's `ValueAsDate($Items/Count, FirstDay)` rows).
      else (rawScalarOperator? id).isSome || (rawListOperator? id).isSome || rawTemporalSourceAvailable true source
  | _ => false

/-- Route by syntax only: a precision refusal must not suppress the raw path before its
operand read (CheckRundenOpImpl; CheckRundenOperOpImpl). -/
partial def rawScalarTreeAvailable : Expr → Bool
  | .number _ => true
  | .braces body => rawScalarTreeAvailable body
  | .arith _ left right => rawScalarTreeAvailable left && rawScalarTreeAvailable right
  | expression@(.call name arguments none none) =>
      if ["Abs", "Min", "Max"].contains name || isNumericFieldForm name || (roundingMode? name).isSome then
        arguments.all (fun | .mk source none => rawScalarTreeAvailable source | _ => false)
      else rawScalarAtomAvailable expression
  | expression => rawScalarAtomAvailable expression

private partial def rawTemporalSourceAvailable (allowCompletion : Bool) : Expr → Bool
  | .entity _ | .string _ => true
  | .constant name => ["Today", "Now", "BaseYear", "RuleGroup"].contains name
  | .call name arguments none none =>
      if let some constructor := rawTemporalConstructor? name then
        match constructor, arguments with
        | .dateTime, [.mk date none, .mk time none] =>
            rawTemporalSourceAvailable true date && rawTemporalSourceAvailable false time
        | .dateTime, _ => false
        | _, _ => arguments.all (fun | .mk component none => rawConstructorComponentAvailable component | _ => false)
      else match arguments with
        | [.mk source none] =>
            if isRawRangeBound name then (match source with | .entity _ | .constant "BaseYear" | .constant "RuleGroup" => true | _ => false)
            else (rawTemporalExtractor? name).isSome && rawTemporalSourceAvailable false source
        | [.mk source none, .mk amount none] =>
            if name == "ValueAsDate" then allowCompletion && (match source with | .entity _ | .constant "RuleGroup" => true | _ => false)
            else match rawTemporalArithmetic? name with
              | some (.shift _) => rawTemporalSourceAvailable true source && rawScalarTreeAvailable amount
              | _ => false
        | _ => false
  | _ => false

private partial def rawConstructorComponentAvailable : Expr → Bool
  | .entity _ | .string _ | .constant "RuleGroup" => true
  | .call name [.mk source none] none none =>
      (rawTemporalExtractor? name).isSome && rawTemporalSourceAvailable false source
  | _ => false
end

end A12Kernel.Dm
