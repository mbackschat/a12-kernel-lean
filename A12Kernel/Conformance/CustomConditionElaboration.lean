import A12Kernel.Elaboration.CustomCondition

/-! # Checked `CustomCondition` name locks

These cases retain the exact `nameOhnePunkt` character classes and the quote-versus-reserved-token distinction while leaving the locale-specific terminal inventory with the caller.
-/

namespace A12Kernel.Conformance.CustomConditionElaboration

open A12Kernel

private def isReserved (name : String) : Bool :=
  name == "Today" || name == "RuleGroup"

private def checkedIdentity (spelling : CustomConditionNameSpelling) :
    Option (String × Bool) :=
  (checkCustomConditionName isReserved spelling).map fun checked =>
    (checked.value, checked.wasQuoted)

example :
    checkedIdentity (.unquoted "NotReverse") = some ("NotReverse", false) ∧
      checkedIdentity (.unquoted "1Special") = some ("1Special", false) ∧
      checkedIdentity (.unquoted "123") = some ("123", false) ∧
      checkedIdentity (.unquoted "_Special") = some ("_Special", false) ∧
      checkedIdentity (.unquoted ":Special") = some (":Special", false) ∧
      checkedIdentity (.unquoted "ÄÜÖäüöß") = some ("ÄÜÖäüöß", false) ∧
      checkedIdentity (.quoted "Today") = some ("Today", true) ∧
      checkedIdentity (.quoted "RuleGroup") = some ("RuleGroup", true) ∧
      checkedIdentity (.quoted "_Special2") = some ("_Special2", true) ∧
      checkedIdentity (.quoted ":Special") = some (":Special", true) ∧
      checkedIdentity (.quoted "ÄSpecial") = some ("ÄSpecial", true) := by
  native_decide

example :
    checkedIdentity (.unquoted "") = none ∧
      checkedIdentity (.quoted "") = none ∧
      checkedIdentity (.unquoted "Today") = none ∧
      checkedIdentity (.unquoted "RuleGroup") = none ∧
      checkedIdentity (.quoted "1Special") = none ∧
      checkedIdentity (.unquoted "Special-Case") = none ∧
      checkedIdentity (.unquoted "Special.Case") = none ∧
      checkedIdentity (.unquoted "Special/Case") = none ∧
      checkedIdentity (.unquoted "Special Case") = none ∧
      checkedIdentity (.quoted "Special-Case") = none ∧
      checkedIdentity (.unquoted "é") = none := by
  native_decide

end A12Kernel.Conformance.CustomConditionElaboration
