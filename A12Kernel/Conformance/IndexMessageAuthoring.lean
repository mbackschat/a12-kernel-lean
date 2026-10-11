import A12Kernel.Elaboration.MessageParameterSyntax

namespace A12Kernel.Conformance.IndexMessageAuthoring

private def keywords : MessageParameterKeywords := {
  reserved := ["For", "RuleGroup", "BaseYear"]
  exempt := []
  exemptNonFinal := ["value", "Wert"]
  ruleGroup := "RuleGroup"
  rootGroup := "RootGroup"
  retired := []
  offset := []
  forTerminal := "For" }

private def terminals : MessageNameTerminals := {
  baseYear := "BaseYear", valueSuffix := "value"
  formLine := "Vordruckzeile", formName := "Vordruckname" }

private def decoded (source : String) : DecodedMessageName :=
  decodeMessageName keywords terminals (ParameterToken.ofParameter keywords source)

-- The entitySpec argument and paired parentheses belong to the parameter grammar (spec/11).
example : ["index().value", "index(Key.value", "index)Key(.value"].all
    (fun source => (decoded source).form.isNone) = true := by
  native_decide

example :
    let key := MessageEntitySpec.path {
      base := .relative 0, groups := [], field := { text := "Key" } }
    (decoded "index(Key).value").form = some (.indexField key .value) ∧
    (decoded "index(Key)->Label").form = some (.indexField key (.category "Label")) ∧
    (decoded "index(Key)").form = some (.indexField key .none) ∧
    (decodeMessageName keywords { terminals with valueSuffix := "Wert" }
      (ParameterToken.ofParameter keywords "index(Key).Wert")).form =
      some (.indexField key .value) ∧
    (decodeMessageName keywords { terminals with valueSuffix := "Wert" }
      (ParameterToken.ofParameter keywords "index(Key).value")).form.isNone = true := by
  native_decide

end A12Kernel.Conformance.IndexMessageAuthoring
