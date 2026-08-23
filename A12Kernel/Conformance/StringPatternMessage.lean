import A12Kernel.Elaboration.StringPatternMessage

/-! # en_US String-pattern producer conformance locks

The two admitted tokens against stylized and actual names, its rejected empty parameter, and the
delimiter gate it shares with the rule producer. -/

namespace A12Kernel.Conformance.StringPatternMessage

open A12Kernel

private def stringPatternInputs : StringPatternMessageInputs where
  fieldName := "Code"
  fieldValue := "$field$"

private def stringPatternRender? (template : String) : Option ResolvedMessageText := do
  let checked ←
    (elaborateEnUsStringPatternMessageTemplate template).toOption
  pure (checked.renderError stringPatternInputs).text

private def stringPatternTemplateError? (template : String) :
    Option ValidationMessageTemplateError :=
  match elaborateEnUsStringPatternMessageTemplate template with
  | .ok _ => none
  | .error error => some error

example :
    stringPatternRender? "$field$" =
        some { text := "Code" } ∧
      stringPatternRender? "Value [$field.value$]" =
        some { text := "Value [$field$]" } := by
  native_decide

example :
    stringPatternTemplateError? "$Field$" =
        some (.invalidParameter "Field") ∧
      stringPatternTemplateError? "$Code$" =
        some (.invalidParameter "Code") ∧
      stringPatternTemplateError? "Cost $$ $field$" =
        some (.invalidParameter "") ∧
      stringPatternTemplateError? "$field" =
        some .oddDollarCount := by
  native_decide

end A12Kernel.Conformance.StringPatternMessage
